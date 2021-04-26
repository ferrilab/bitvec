# `bitvec` Memory Model

`bitvec` addresses individual bits, while computer hardware addresses register
elements. As a result, `bitvec` has a more complex memory model than the Rust
language does. The library implementation strives to satisfy users’
expectations, the Rust language’s rules, and performance in the produced
artifact to the best solution for all parties, with as few compromises as
possible. Unfortunately, this has the side effect of increasing the complexity
of the codebase, both for maintainers and for readers.

This document explains the abstract concepts of the `bitvec` memory model and
the means by which it is encoded in the Rust language without running afoul of
Rust or LLVM rules that threaten undefined behavior.

The `bitvec` memory model is typed entirely within the `store` module’s
`BitStore` trait definition and implementations. It utilizes the `access`
module’s `BitAccess` trait to mediate memory access events through types that
are known to be correct in the Rust and LLVM models, so that at any point in
program execution, memory access will be consistent and sound.

In addition, the `domain` module’s types provide views which manipulate the
`store` model to maximize performance. This document will discuss primarily
`store`, and use `domain` only to provide examples of how `store` is used in
practice to accomplish the library’s implementation.

## Aliasing

To Rust and LLVM, “aliasing” occurs whenever there are two paths to a memory
region, and at least one of them has write privileges. In Rust, this is
represented by the `&mut` reference exclusion rule: it is always, always,
**always** Undefined Behavior in the *Rust* memory model to have two
*references* which can reach a memory element if at least one of them is marked
`&mut`.

LLVM, which was created for, is written in, and culturally shaped by C++, takes
a similar view with its `noalias` annotation, but struggles to enforce it as
thoroughly as Rust does.

`bitvec` takes a similar view of the abstract meaning of the `&mut` reference
type, but where the Rust memory model focuses on whole units `T`, and has no
concept of subdivision from `T` into the bits that compose it, `bitvec` views
each individual bit as a standalone, independent, atom of memory. It excludes
the creation of two `&mut BitSlice` reference handles that are capable of
viewing the same *bit*, but will happily produce two `&mut BitSlice` handles
which are mutually-exclusive in bits, but reference the same register location
in memory.

Here we come to the first problem with the conflicting memory models: `bitvec`
cannot ever create an `&mut T` through which it may write to memory, because it
has no way of ensuring that no other `&T` or `&mut T` reference exists which is
capable of viewing the memory region into which it writes.

### Rust Shared Mutation

The problem isn’t just that the Rust standard library doesn’t offer any
non-`unsafe` APIs to produce such references. The problem is that this is about
the most illegal thing you can do in the eyes of the Rust compiler, and if it
ever detects this transgression, it has full liberty to either reject, or worse,
accept *and miscompile*, your program.

In Gankra’s [immortal words] on the topic of attempting to sneak past the
compiler’s commandments,

> - Transmuting an `&` to `&mut` is *always* UB
> - No you can’t do it
> - No you’re not special

The solution is simple: Rust exposes a type, [`UnsafeCell`], which is the
axiomatic type for mutation through shared views. In the Rust memory model, any
reference to a region of memory marked with `UnsafeCell` is permitted to write
to it, and if any other references can view that region, then it is up to them
to ensure consistent behavior.

This is, of course, not *quite* true in LLVM’s memory model, but we are not
there yet.

Since an `&mut BitSlice<_, T>` handle cannot produce an `&mut T` reference to
perform writes to memory, it must instead either use a `*mut T` bare pointer,
which has absolutely no checks or optimizations whatsoëver, or use an
`&UnsafeCell<T>` shared reference, which has all the usual guarantees present on
all[^1] reference types.

All `UnsafeCell` does is instruct the Rust compiler to politely look the other
way about your program’s memory accesses. It is somewhat like the C keyword
`volatile`, in that the compiler no longer believes that reads are stateless, or
freely reörderable, but entirely unlike that keyword in that the compiler
doesn’t have any obligation to *keep* your reads from or writes to such regions.

Rust provides an additional type called [`Cell`]. This is a wrapper over
`UnsafeCell`[^2] that defines a more useful API, including the only safe and
guaranteed way to write into memory through a shared reference: [`Cell::set`].

And *voilà*: `&mut BitSlice<_, T>` simply constructs `&Cell<T>` when writing,
the Rust compiler does not see a violation of the `&mut` exclusion principle,
and we are done.

### LLVM Shared Mutation

No we’re not. If it was that easy, there wouldn’t be a trait system or this
document dedicated specifically to dealing with this problem.

`Cell` is not thread-safe, because `Cell` does not modify the instructions used
to access memory. It produces ordinary load and store instructions, carefree and
ignorant of the bane of everyone who wants consistency and the delight of
everyone who wants performance: concurrency.

Just as it is undefined behavior in Rust to manifest two `&mut` references that
can view the same location, it is equally undefined behavior in LLVM to manifest
two pointers into memory that ever, at all, no matter **what**, perform any
memory access to the same location, at the same time, on multiple processors.

As with above:

> - Unsynchronized writes are *always* UB.
> - No you can’t do it.
> - No you’re not special.

LLVM has an even more insidious punishment for this transgression that Rust does
not directly express: unsynchronized reads from a data race produce [`poison`].
Poison is a nifty concept, because it’s not illegal to obtain one. When LLVM
gives you a `poison`, your program continues undergoing compilation as if
nothing had happened. You can pass it around. You can write to it, and if you
destroy it before reading, you’re fine.

As soon as you attempt to read the bit-wise value of `poison`, your program is
undefined[^3].

So if `bitvec` wants to be threadsafe, which it does, and it wants to insist on
its ability to safely alias the same memory location from multiple handles,
which is non-negotiable, there’s only one avenue left to take.

### Atomic Powered Microscopes

Rust doesn’t actually model atomics. It doesn’t have to do so: no harm can ever
come from multiple handles reading out of the same immutable location, harm can
only occur when writes are observable, and writes are not observable due to the
`&mut` exclusion rule. Well, except for `UnsafeCell`, so everything that has an
`UnsafeCell` in it gets marked as `!Send`, `&` references can’t cross threads,
and the whole problem is avoided.

This is, of course, not good enough. Concurrent, mutable, access to a location
is an important property in a computer. LLVM provides atomic types, which Rust
transparently exports as wrappers over `UnsafeCell` that have their `Sync`
implementation restored. Handles to a region marked as atomic will use some form
of hardware-provided exclusion in order to preserve the
one-writer-XOR-any-readers system behavior, and all is well.

Hardware-level exclusion has the unfortunate penalty of being, to put it
lightly, “slow”. So while it’s the safest choice to be correct, and was in fact
the default universal choice for all memory access in `bitvec` for some time,
its costs[^4] called for a more prudent behavior.

It’s time for a new trick, something that the Rust compiler does at the region
level, and that `bitvec` now does at the element level:

## Run Time Alias Analysis

`BitSlice` handles can only be constructed from ordinary Rust references to
memory, which Rust guarantees start out unaliased. The potential for aliasing
only occurs when a `&mut BitSlice` is split into multiple subslices using any
of the functions that eventually call `.split_at_unchecked_mut`. Since that is
the root function that introduces alias conditions, it returns subslices whose
memory type parameters are tainted with the `::Alias` marker. It has the
following type signature:

```rust
impl<O, T> BitSlice<O, T>
where O: BitOrder, T: BitStore {
  pub fn split_at_unchecked_mut(&mut self, at: usize) -> (
    &mut BitSlice<O, T::Alias>,
    &mut BitSlice<O, T::Alias>,
  );
}
```

The `BitStore` trait defines an `::Alias` associated type, which ensures that
all memory accesses through it have appropriate aliasing guards. For builds
which do not use the `atomic` feature (or where the target does not have an
atomic variant of the integer), this is `Cell`, and its protections are the loss
of thread-safety. For builds that do permit atomics, the marker enforces that
all reads and writes use atomic instructions.

The `::Alias` marker is applied, at compile time, by operations that split
`&mut BitSlice` references into multiple coëxisting subslices. This is a good
first step to reducing unnecessary synchrony, but not good enough. Consider the
following:

```rust
use bitvec::prelude::*;

let mut data = [0u8; 2];
let bits = data.view_bits_mut::<Local>();
let (one, two) = data.split_at_mut(8);
```

It so happens that this is equivalent to splitting `data` first, then viewing
each subslice as bits, but this transformation can only be done if the partition
point is known at compile-time to fall on an element boundary. There is no need
for the subslices `one` and `two` to use alias-safe operations, as accesses to
memory through them do not conflict with each other.

### Bit Slice Domains

The in-memory domain of any bit slice can be generalized to one of two formats:
either the slice touches zero element edges, or it touches at least one edge
element. Consider three bytes of memory (any element will do, but the extra
width on this page is unnecessary), with some bitslice regions drawn within
them:

```text
|00000000│11111111│22222222|
|76543210│76543210│76543210│
├────────┼────────┼────────┤
│        │        │        │ 1
│        ╞════╡   │        │ 2
│        │ ╞════╡ │        │ 3
│        │   ╞════╡        │ 4
│    ╞═══╪════╡   │        │ 5
│    ╞═══╪════════╡        │ 6
│        ╞════════╪═══╡    │ 7
│    ╞═══╪════════╪═══╡    │ 8
╞════════╪════════╪════════╡ 9
```

There are nine example slices here, but they can be reduced into six specific
categories, and two general ones:

1. empty: row 1
1. minor (interior of an element, no edge indices): row 3
1. partially-spanning head, fully-spanning body: rows 3 and 6
1. partially-spanning tail, fully-spanning body: rows 2 and 7
1. major (partial head, partial tail, full body): rows 5 and 8
1. spanning: row 9

The minor slice (row 3) is irreducible; the rest can all be divided into three
subcomponents:

- zero or one partially-occupied head element, where the slice touches the last
  index in it but not the first
- zero or more fully-occupied middle elements, where the slice touches all
  indices in each
- zero or one partially-occupied tail element, where the slice touches the first
  index in it but not the last

We can break each row down into these components:

|Row|Head|Body|Tail|
|:-:|:--:|:--:|:--:|
| 1 |None|   0|None|
| 2 |None|   0|Some|
| 4 |Some|   0|None|
| 5 |Some|   0|Some|
| 6 |Some|   1|None|
| 7 |None|   1|Some|
| 8 |Some|   1|Some|
| 9 |None|   3|None|

We can observe that where a slice fully-spans some elements, those elements
cannot be mutated by any other reference. In the `&BitSlice` case, all `&mut`s
are forbidden by the compiler’s ordinary rules; in the `&mut BitSlice` case,
`bitvec`’s obedience to those same rules forbids any other handle from observing
the bits covered by the `&mut BitSlice`. As such, it is statically impossible
for any alias to exist to the described memory in row 9, or for any alias to
observe element `1` of rows 6 through 8.

`bitvec` happily permits element-aliasing `&mut BitSlice` references to observe
the partially-filled elements in the outer columns, and middle column of rows 2
through 5, so writes to them must remain synchronized through either
single-threaded `Cell` or concurrency-safe atomics. These domain components can
be calculated from the three components of a slice pointer: the base address,
the starting bit index, and the bit count.

This is expressed in the `domain` module’s four enums.

### `BitDomain` and `BitDomainMut`

These enums split any `BitSlice` region into its subcomponents, immutably or
mutably, respectively. They have the definition

```rust
pub enum BitDomain /* Mut */ <'a, O, T>
where
  O: BitOrder,
  T: BitStore
{
  Enclave { body: &'a /* mut */ BitSlice<O, T> },
  Region {
    head: &'a /* mut */ BitSlice<O, T>,
    body: &'a /* mut */ BitSlice<O, T::Mem>,
    tail: &'a /* mut */ BitSlice<O, T>,
  },
}
```

and, rather than granting direct memory access, merely remove any aliasing
markers from as much memory as possible. The subslices that partially fill their
base element do not need to add an additional aliasing marker, as the marker is
only required when writes to the element may collide. If the slice is immutable,
aliasing never occurs, so synchrony is never required. If the slice is mutable,
then the only way to get a partial edge slice is to either forget about some
bits from the main slice, which is *not* an alias event, or to split the slice,
which *is*, and splitting already marks the alias.

### `Domain` and `DomainMut`

The bit domains are still bit slices, and do not offer a way to access the
backing memory. For operations where raw memory access is required, these enums
produce the same domain definitions, but typed for the bare elements rather than
their bits.

They have the definition

```rust
pub enum Domain /* Mut */ <'a, T>
where T: BitStore {
  Enclave {
    head: BitIdx<T::Mem>,
    elem: &'a T /* ::Access */,
    tail: BitEnd<T::Mem>,
  },
  Region {
    head: Option<(BitIdx<T::Mem>, &'a T /* ::Access */)>,
    body: &'a /* mut */ [T::Mem],
    tail: Option<(&'a T /* ::Access */, BitIdx<T::Mem>)>,
  },
}
```

As with the bit domains, these domains will inherit any aliasing markers from
their source bitslice. The `::Alias` associated type enables the mutable domain
to produce references that allow mutation without adding an unnecessary
aliasing marker. Rust strongly forbids the production of `&mut` references to
aliased memory elements, which is why the only `&mut` reference in these views
is to memory that is fully known to be unaliased.

> This deäliasing behavior is why `BitSlice`s are impossible to construct over
> memory that permits external aliases outside of `bitvec`’s control.

The `DomainMut` structure will produce bare [atomic] or [`Cell`] types in the
alias condition. This is necessary in order to avoid production of `&mut`
references which alias (as this is undefined in the Rust abstract machine,
regardless of behavior), and safe because any other references to the same
location will be similarly aliased and capable of handling external mutation.

## LLVM Suboptimizations

LLVM considers a “racing read”, that is, any read from memory that could occur
contemporaneously with an atomic write, to be undefined behavior. This is a
reasonable view to take, but a pessimistic one. `bitvec` has information that
cannot be expressed to LLVM about which **bits** of an element it will observe
or modify, and `bitvec` is capable of guaranteeing that two distinct access
points will not be able to interfere with each other electrically. LLVM does not
know this, so it considers any write to memory to touch *all* bits of the
touched element, and any read from memory to view *all* bits of the fetched
element.

`bitvec` exclusively[^5] writes to contended memory with the Rust functions
[`AtomicT::fetch_and`] and [`AtomicT::fetch_or`], which are mapped to the LLVM
instructions [`__atomic_fetch_and_N`][llvm_atomic] and
[`__atomic_fetch_or_N`][llvm_atomic]. It uses bitmasks that *`bitvec`* can
[guarantee][bv_ord] are non-intersecting, but this proof cannot be extended to
even the Rust compiler, let alone LLVM. These bitmasks are applied to register
values before using either of the `fetch_op` instructions, and after any reads
that use [`AtomicT::load`]/[`__atomic_load_N`][llvm_atomic].

If the `bitvec` mask proofs were extendible to LLVM, and LLVM were to expand its
tracking of which bits of a memory address became `poison`ed by a memory write,
and which bits of a fetched memory value became un-`poison`ed by a masking
operation, then the compiler would be more able to observe that `bitvec` memory
accesses do not *observably* interfere with each other. This observation would
then define the behavior in the compiler’s memory model of racing writes/reads,
and permit an increased (possibly even complete) removal of synchrony guards.

> I am not aware of any processor hardware which fails to guarantee that all
> bits of memory are fully defined at the clock edges of all instructions that
> use the location. To the full extent my knowledge, all memory banks in all
> relevant processors have a stable bit-value at the start of a tick, when
> reads occur, and at the end of a tick, when writes commit. At no point does
> changing the value of one bit of a memory component affect the electrical
> value of other bits in the component.
>
> This is not necessarily true of other storage devices, such as SSDs, but
> `bitvec` can only be used to access storage cells mapped in the RAM address
> space, which tend to all have this stability property.

## Summary

The formal definition of the `bitvec` memory model extends the Rust
mutable-exclusion rules by refining memory regions to have bit-precision instead
of element-precision. The Rust compiler is only weakly capable of tracking the
region status of individual bits, and only in compiler-internal structures. LLVM
has a more robust arbitrary-bit-tracking capability, but similarly limits its
interface to external code.

Barring any errors in the `bitvec` implementation, the `bitvec` memory model is
fully sound in its behavior with regard to single-observer race freedom.
Synchronization is only added in order to correctly interface with `rustc` and
LLVM without causing either of them to introduce undefined behavior due to a
lack of information.

At time of writing, `bitvec` is experimenting with an API for a shared reference
of `&BitSlice<_, T::Alias>` to issue an appropriately synchronized mutation.
This is a soundness hole in the type system, as a sibling `T::Mem` view to
memory affected by the mutation is freely permitted to exist. This API will not
be published as part of the crate until the library is enabled to prevent the
simultaneous production of `::Mem` and `::Alias` aliasing references.

## Footnotes

[^1]: all references to `T` where `T` is either `!Sized`, or
      `mem::size_of::<T>()` is non-zero, that is. A fun quirk of Rust’s
      first-class concept of zero-width types is that the only illegal value for
      a `&Zst` reference is null. Since there is nothing to load or store
      through a `&Zst` reference, the compiler doesn’t *care* what the reference
      value is, as it will never be used to perform memory access.

[^2]: literally: <https://doc.rust-lang.org/1.43.0/src/core/cell.rs.html#232-235>

[^3]: This is not *absolutely* true. Like we saw with `UnsafeCell`, the only
      immutable rule of compiler developers is that whenever they make an
      immutable rule, they also provide a way to sidestep it. If you [`freeze`]
      a `poison`, you are now free to read its value and act on it. LLVM just
      doesn’t make any guarantees about what you’ll see.

[^4]: I’d feel a great deal more comfortable if I had firm knowledge of what
      those costs actually **were**. An atomic write always issues a `lock`
      instruction modifier on x86, and I have heard vastly different things
      about what that actually *means*, from “it’s free if no other cache holds
      that address” up to “it poisons the whole cacheline”, and have not had
      much luck producing a benchmark that firmly demonstrates that unneeded
      atomic access is a strict performance cost.

[^5]: In multi-threaded environments. Disabling atomics also disables `bitvec`’s
      support for multi-threaded, so the penalty for aliasing is reduced to an
      inability to remove redundant reads.

[bv_ord]: https://github.com/myrrlyn/bitvec/blob/HEAD/src/order.rs
[immortal words]: https://doc.rust-lang.org/stable/nomicon/transmutes.html
[llvm_atomic]: https://releases.llvm.org/10.0.0/docs/Atomics.html#libcalls-atomic
[`AtomicT::fetch_and`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicUsize.html#method.fetch_and
[`AtomicT::fetch_or`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicUsize.html#method.fetch_or
[`AtomicT::load`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicUsize.html#method.load
[`Cell`]: https://doc.rust-lang.org/stable/core/cell/struct.Cell.html
[`Cell::set`]: https://doc.rust-lang.org/stable/core/cell/struct.Cell.html#method.set
[`UnsafeCell`]: https://doc.rust-lang.org/stable/core/cell/struct.UnsafeCell.html
[`freeze`]: https://llvm.org/docs/LangRef.html#i-freeze
[`poison`]: https://llvm.org/docs/LangRef.html#poison-values
