<div class="title-block" style="text-align: center;" align="center">

# `bitvec` <!-- omit in toc -->

## Managing Memory Bit by Bit <!-- omit in toc -->

[![Crate][crate_img]][crate]
[![Documentation][docs_img]][docs]
[![License][license_img]][license_file]

[![Continuous Integration][travis_img]][travis]
[![Code Coverage][codecov_img]][codecov]
[![Crate Downloads][downloads_img]][crate]
[![Crate Size][loc_img]][loc]

</div>

`bitvec` permits a program to view memory as bit-addressed, rather than
byte-addressed. It is a foundation library for `bool`ean collections and
precise, user-controlled, in-memory layout of data fields and I/O protocol
buffers.

# Table of Contents <!-- omit in toc -->

1. [Introduction](#introduction)
   1. [Capabilities](#capabilities)
   1. [Limitations](#limitations)
1. [Usage](#usage)
   1. [User Stories](#user-stories)
      1. [Collections of Bits](#collections-of-bits)
      1. [Bitfield Memory Access](#bitfield-memory-access)
   1. [Please Just Show Me Some Code](#please-just-show-me-some-code)
1. [Feature Flags](#feature-flags)
   1. [`alloc` Feature](#alloc-feature)
   1. [`atomic` Feature](#atomic-feature)
   1. [`serde` Feature](#serde-feature)
   1. [`std` Feature](#std-feature)
1. [API Reference](#api-reference)
   1. [Implementation Details](#implementation-details)
1. [Alias Conditions](#alias-conditions)

# Introduction

Computers operate on bytes. Memory is addressed in byte intervals, and processor
registers are powers of bytes in size. Data that does not evenly fill a byte, or
a power of a byte, creates inconveniences for the machine and for the
programmer.

`bitvec` removes the human-facing inconveniences by modelling memory as if it
were addressed as individual bits, and registers as if they supported any width.

If you need to work with data that does not evenly fill one of the fundamental
register types, or if you need precise control of your in-memory representation
of a buffer, or if you are merely operating on large collections of `bool`, then
this library is the best tool available for your use.

## Capabilities

`bitvec` is the only crate in the Rust ecosystem that fits directly into the
Rust language memory model and APIs. Its most important feature is the
[`&/mut BitSlice`] reference type, which is a slice of bits without any
restriction on where in memory it begins or ends. Because it is a reference, it
can be used in traits whose signatures demand an explicit *reference* type, not
merely some borrowing handle.

In addition, `bitvec` implements the register behavior seen in C and Ada
[bitfield]s by permitting many [`&/mut BitSlice`] regions to be used as if they
were memory locations into and out of which programmers can move integers.

Furthermore, `bitvec` implements the entire standard-library sequence API, to
the point that you can begin using the crate by running a `sed` script and have
almost no errors. Where `bitvec` is unable to implement an exact port, it
provides a replacement API with equivalent behavior.

Lastly, unlike *any* other bit-sequence library the author has encountered,
`bitvec` is generic over not only the register type used as the underlying
memory storage (in C bitfields, this is the integer type of the `struct` member),
but is also generic over the ordering of bit indices within a register. Users
can select the ordering and register combination that best matches their needs,
and gain source code that is easily legible, as well as a compiled artifact that
**just works**, and takes advantage of aggressive compile-time computation and
codegen optimizations.

## Limitations

The [`&/mut BitSlice`] reference type is implemented with a pointer encoding
that packs the starting-bit index into the length portion of an ordinary slice
reference. This costs three bits of the length counter, and requires more
computation to operate on the pointer than an ordinary slice pointer would
incur. [`BitSlice`] regions are thus limited to one-eighth the range of a
`usize` length index.

While the Rust source code of the library is unable to write the pointer
encoding as `const fn` (so far), the author has observed that the compiler’s
existing capabilities for `const`-value propagation eliminate a great deal of
the pointer encoding’s cost by performing partial or complete work at compile
time, and create precomputed instruction arguments rather than runtime function
calls.

Because the [`&/mut BitSlice`] *reference* uses a unique encoding, the
`BitSlice` *region* type cannot be used as an argument to any other pointer
type. You **must** use the container types provided by `bitvec`. If `bitvec`
does not have a port of the container you want (for example, [`Rc`] and
[`Arc`]), you must file an issue for future work.

`bitvec` cannot fully mirror the C++ [`std::bitset<N>`] type until type-level
integers are more fully stabilized in the Rust compiler. The [`BitArray`] type
provides the best analogue that Rust can offer.

# Usage

**Minimum Supported Rust Version:** `1.47.0`

`bitvec` does not have a firm MSRV policy. The MSRV is advanced as needed to
simplify the library’s ongoing development. `bitvec` tracks the evolution of the
standard library on a best-effort basis. As new behaviors are stabilized on the
core types it mirrors, `bitvec` will update to match them according to user
demand or authorial free time.

To use `bitvec`, depend on it in your Cargo manifest:

```toml
# Cargo.toml

[dependencies]
bitvec = "0.20"
```

and import its prelude into any module that needs it:

```rust
// src/lib.rs

use bitvec::prelude::*;
```

The prelude imports all the symbols that the library needs to operate. Almost
all names begin with `Bit`, which should significantly lower the chances of a
symbol collision. If you encounter a name collision, or wish greater precision
over which symbols are imported, consider importing the prelude module itself
under an alias:

```rust
// src/lib.rs

use bitvec::prelude as bv;
```

You can read the [prelude reëxports][prelude] to learn what symbols you need,
and import them directly rather than using a glob import.

## User Stories

`bitvec` improves upon the Unix tenet of “do[ïng] one thing well” by doing *two*
things well. By describing memory as a contiguous sequence of individual bits,
it is able to mirror the standard-library types `[bool]`, `[bool; N]`,
`Box<[bool]>`, and `Vec<bool>` with types that offer the same API and
functionality, while storing each bit of the collection in exactly one bit of
memory, rather than eight. In addition, its implementation of a complete memory
model allows it to implement the basis of bitfield-style memory access for
integers, rather than only bits.

### Collections of Bits

> I do not care about what “memory” looks like; I just have some very large
> collections of `bool`s and I want to use less resident memory!
>
> —you, probably

The fastest way to start using `bitvec` to drive your `bool`ean collections is
to perform textual find/replace operations:

- `[bool]` → `BitSlice`
- `[bool; LEN]` →
  `BitArray<Lsb0, [usize; bitvec::mem::elts::<usize>(LEN)]>` (you probably want
  to compute the new `LEN` yourself)
- `Box<[bool]>` → `BitBox`
- `Vec<bool>` → `BitVec`

If you have errors about missing type parameters, use `<_, _>` or
`<Lsb0, usize>` as needed until the compiler relents. These are the default type
arguments and will be the best suited for your target’s performance.

Almost everything else in your project should continue working. The primary
exception is that `collection[place] = value;` is not expressible in `bitvec`,
so any such assignments will need to be changed to
`collection.set(place, value);`

> There is an RFC that, if implemented, would make index-access syntax use this
> method signature! This would allow `[]=`-style assignment, bringing `bitvec`
> fully in line with the standard-library APIs.

Any remaining errors should be straightforward to resolve. If they are not,
please file an issue.

Once your project compiles again, you will now have smaller heap allocations,
and possibly faster set analyses. You will also gain set arithmetic and query
behaviors that the standard library does not have on its `bool`ean collections.

### Bitfield Memory Access

> I am *very* concerned with the precise electrical construction of my memory,
> and frankly, I’m tired of translating data-sheet cell numbers into shift and
> mask operations. I don’t want to set one bit at a time, either. I want to be
> able to write an integer into any section of bits, regardless of what my bus
> controller thinks is possible.
>
> —the crate author, a day before beginning this project

or

> i was able to just type bit indices from the datasheet into the rust and it
> just, works. … itanium is based on 41-bit instruction words and i can just, not
> care. this is wonderful
>
> —a satisfied user

This project was written specifically to handle the de/construction of I/O
buffers that are not expressible in ordinary Rust. If you need logic more
complex than a `#[repr(C)]` attribute on your type definitions and a
pointer-cast to `*const u8`, then this is the project for you.

`bitvec` provides two bit-ordering behaviors out of the box:

- `Lsb0` moves across a register starting at the least significant bit and ending
  at the most significant bit.
- `Msb0` moves across a register starting at the most significant bit and ending
  at the least significant bit.
- `LocalBits` is an alias to whichever of those GCC would pick in `struct`
  bitfields.

Additionally, it allows you to use any of the register types available on your
target as the memory unit: `u8`, `u16`, `u32`, `u64` (if present), and `usize`.
While `usize` is the default, you *almost certainly* want to use `u8` for this
scenario. Almost all protocols are byte-oriented.

You can read a more thorough explanation, and see tables, of the
ordering/register combinations in the [Bit Ordering] document.

## Please Just Show Me Some Code

Okay! This snippet provides a whirlwind tour of the library. You can see more
[examples] in the repository, which showcase more specific goals.

```rust
use bitvec::prelude::*;

use std::iter::repeat;

fn main() {
  // You can build a static array,
  let arr = bitarr![Lsb0, u32; 0; 64];
  // a hidden static slice,
  let slice = bits![mut LocalBits, u16; 0; 10];
  // or a boxed slice,
  let boxed = bitbox![0; 20];
  // or a vector, using macros that extend the `vec!` syntax
  let mut bv = bitvec![Msb0, u8; 0, 1, 0, 1];

  // You can also explicitly borrow existing scalars,
  let data = 0u32;
  let bits = BitSlice::<Lsb0, _>::from_element(&data);
  // or arrays,
  let mut data = [0u8; 3];
  let bits = BitSlice::<Msb0, _>::from_slice_mut(&mut data[..]);
  // and these are available as shortcut methods:
  let bits = 0u32.view_bits::<Lsb0>();
  let bits = [0u8; 3].view_bits_mut::<Msb0>();

  // `BitVec` implements the entire `Vec` API
  bv.reserve(8);

  // Like `Vec<bool>`, it can be extended by any iterator of `bool` or `&bool`
  bv.extend([false; 4].iter());
  bv.extend([true; 4].iter().copied());

  // `BitSlice`-owning buffers can be viewed as their raw memory
  assert_eq!(
    bv.as_slice(),
    &[0b0101_0000, 0b1111_0000],
    //  ^ index 0       ^ index 11
  );
  assert_eq!(bv.len(), 12);
  assert!(bv.capacity() >= 16);

  bv.push(true);
  bv.push(false);
  bv.push(true);

  // `BitSlice` implements indexing
  assert!(bv[12]);
  assert!(!bv[13]);
  assert!(bv[14]);
  assert!(bv.get(15).is_none());

  // but not in place position
  // bv[12] = false;
  // because it cannot produce `&mut bool`.
  // instead, use `.get_mut()`:
  *bv.get_mut(12).unwrap() = false;
  // or `.set()`:
  bv.set(12, false);

  // range indexing produces subslices
  let last = &bv[12 ..];
  assert_eq!(last.len(), 3);
  assert!(last.any());

  for _ in 0 .. 3 {
    assert!(bv.pop().is_some());
  }

  //  `BitSlice` implements set arithmetic against any `bool` iterator
  bv &= repeat(true);
  bv |= repeat(false);
  bv ^= repeat(true);
  bv = !bv;
  // the crate no longer implements integer arithmetic, but `BitSlice`
  // can be used to represent varints in a downstream library.

  // `BitSlice`s are iterators:
  assert_eq!(
    bv.iter().filter(|b| *b).count(),
    6,
  );

  // including mutable iteration, though this requires explicit binding:
  for (idx, mut bit) in bv.iter_mut().enumerate() {
    //      ^^^ not optional
    *bit ^= idx % 2 == 0;
  }

  // `BitSlice` can also implement bitfield memory behavior:
  bv[1 .. 7].store(0x2Eu8);
  assert_eq!(bv[1 .. 7].load::<u8>(), 0x2E);
}
```

As a general rule, you should be able to migrate old code to use the library by
performing textual replacement of old types with their `bitvec` equivalents,
such as with `s/Vec<bool>/BitVec/g`, and have the rest of your code using the
modified values just work. There will be some errors, such as the absence of
`IndexMut<usize>`, but the crate is built to be as close to drop-in as can
possibly be expressed.

The [examples] directory shows how the crate can be used in a variety of
applications; if it does not contain one relevant to you, please file an issue
with what you are trying to accomplish (or if you accomplished it already, a
snippet!) to grow the collection.

# Feature Flags

`bitvec` has a few Cargo features that it uses to control its shape. By default,
its manifest looks like this:

```toml
# Your Cargo.toml

[dependencies.bitvec]
version = "0.20"
features = [
  "alloc",
  "atomic",
  # "serde",
  "std",
]
```

You can disable the three uncommented features by using the rule
`default-features = false`, and then reënable the ones you need specifically.

## `alloc` Feature

This feature links `bitvec` against the distribution-provided [`alloc`] crate,
if your target has one, and enables the [`BitBox`] and [`BitVec`] types. This
feature is a dependency of the `std` feature, and will always be present when
building for targets that have [`std`]. If you are building for a `#![no_std]`
target, you will need to disable the `std` default feature, and may choose to
reënable the `alloc` feature if your target has an `alloc` library and your
project specifies an allocator.

## `atomic` Feature

This feature configures whether `bitvec` will attempt to use atomic instructions
when accessing aliased memory addresses. For a given integer type `T`, if
`bitvec` is able to use atomic instructions to access it, then
[`&/mut BitSlice<O, T>`] references are safe to move across thread boundaries.
If `bitvec` cannot use atomic instructions, either because this feature is
disabled or because this feature is enabled but the target processor does not
provide the necessary instructions, then `&/mut BitSlice<O, T>` references lose
their ability to cross threads.

`bitvec` uses the [`radium`] project to determine whether atomic instructions
are available for a given integer type `T` on a target processor. The `"atomic"`
feature does not **guarantee** atomicity; it can only **attempt** atomicity. If
`radium` reports that a given integer cannot be accessed atomically on a target,
then `bitvec` will fall back to non-atomic, non-threadsafe, behavior for that
integer.

You may disable this feature to unconditionally use [`Cell`]-based memory access
to aliased locations, thereby disabling multithreading support in
[`&/mut BitSlice`] and ensuring that memory access always uses ordinary
load/store instructions.

Currently, the targets for which `bitvec` is tested have either no atomic
instructions at all, or have atomic instructions available for all integer types
that can be used as the `T` in a [`BitSlice<O, T>`]. `bitvec`’s encoding
restrictions forbid the use of `u64` on targets with 32-bit processor words, so
the 32-bit processors that have `AtomicU32` but not `AtomicU64` do not display
aliasing behavior that varies by integer width.

## `serde` Feature

This feature enables a [`serde::Serialize`] implementation for [`BitSlice`], and
a full `serde::Serialize`/[`serde::Deserialize`] implementation on [`BitArray`],
[`BitBox`], and [`BitVec`]. This feature allows you to transport bit collections
through I/O protocols.

Note that this behavior is **very** different from using `bitvec` to manage a
buffer whose *contents* are an I/O protocol message! You may choose to implement
a `serde::Serializer`/`serde::Deserializer` protocol using `bitvec` to control
layout of your packets, but the `De`/`Serialize` implementations provided do not
do this work. They only write a collection into an already-existing transport
protocol, and are not required to maintain layout representation guarantees.

In particular, at this time `bitvec` does not transport the bit-ordering or
memory-element type parameters, so there is no means of ensuring that the
deserializer is using the same parameter set as the serializer and is thus
capable of receiving the transported data.

## `std` Feature

This feature links `bitvec` against the distribution-provided [`std`] crate, if
your target has one. The only additional features it provides that are not
present in [`alloc`] are implementations of [`io::Read`] and [`io::Write`] on
data structures that match `Read` and `Write` types in `std`, for bit orderings
that have [`BitField`] trait implementations.

# API Reference

The complete API reference can be found on [docs.rs], and will not be duplicated
here. As a summary:

The [`BitSlice`] type describes a region of memory viewed in bit-addressed
precision. It is parameterized by two types, a [`BitOrder`] translation of
indices to positions within a register type, and a [`BitStore`] register type.
It is a region type, and cannot be held as an immediate. It must be held by
reference, `&BitSlice<O, T>` or `&mut BitSlice<O, T>`, or through one of the
container types provided by `bitvec`. It cannot, ever, be used as a type
parameter in containers not provided by this crate.

The [`BitArray`] type describes a block of contiguous memory, which can be
backed by a scalar or an array of scalars, as a `BitSlice` region. The Rust
type-level-integer language implementation is not yet sufficient to correctly
port the C++ `std::bitset<N>` type, so this type is instead parameterized over
the backing memory type, rather than a number of bits. Hopefully, this will
change in the future to permit `<Order, Store, const Bits>` instead.

The [`BitBox`] and [`BitVec`] types are heap-allocated owning buffers,
corresponding to `Box<[bool]>` and `Vec<bool>`, respectively. They defer to
`BitSlice` for data manipulation, and their only inherent behavior is
manipulation of the allocated block.

Each data type has a constructor macro: [`bits!`] for `BitSlice`, [`bitarr!]`
for `BitArray`, [`bitbox!`] for `BitBox`, and [`bitvec!`] for `BitVec`. These
macros implement a superset of the `vec!` macro’s argument grammar, and enable
the compile-time construction of `BitSlice` buffers. `bitbox!` and `bitvec!`
copy their precomputed buffers into heap allocations at runtime.

The [`BitField`] trait describes how a `BitSlice` region can be used for value
storage. It is implemented for `BitSlice<Lsb0, _>` and `BitSlice<Msb0, _>`,
enabling those slices to act as memory stores for any unsigned integral value.

The [`BitOrder`] trait provides translations from semantic indices that appear
in user code to the actual shift-and-mask instructions used to operate on
memory. As this trait has very strict requirements for implementations that
cannot (yet) be made into compiler errors, it is marked `unsafe`.
Implementations other than the provided [`Lsb0`] and [`Msb0`] are permitted, but
will have niche applicability and, likely, reduced performance.

The [`BitStore`] trait describes memory elements, and their behavior in CPU
registers and during load/store instructions. It is implemented on the unsigned
integers not wider than a processor word, their `Cell<>` wrappers, and their
`Atomic` variants. It cannot be implemented outside `bitvec`.

The [`BitView`], [`AsBits<T>`], and [`AsBitsMut<T>`] traits allow a type to
define how it can be viewed as a [`BitSlice`]. Default implementations are
provided for integers and integer arrays, and can be added for user types.

The `domain` module implements the crate’s internal memory model, and performs
the work of managing alias detection and selecting the appropriate un/aliased
memory behaviors. The enums in it are part of the primary API, and can be
constructed from [`BitSlice`]s in order to enable precise memory accesses.

## Implementation Details

In addition to the API surface for general use, `bitvec` exposes some APIs that
are useful for developing the crate itself, or extensions to it.

The `devel` module contains snippets of type manipulation or value checking used
in the crate internals. These functions are not part of the public API, but are
pieces of logic that often occur enough in crate internals to be worth naming,
and are likely to be useful in extension code as well.

The `index` module contains typed indices into register elements. Implementors
of the `BitOrder` trait operate on the types here in order to plug into the rest
of the crate system. This module also contains register types needed to interact
with the `access` module, if you want to use the memory interface system
separately from the crate’s data structures.

The `mem` module contains logic for operating on integers in memory. It is an
implementation detail of the memory modeling system.

The `pointer` module implements the pointer encoding used to drive the
`&BitSlice` reference type. It is explicitly **not** exposed outside the crate,
and is not planned to be stabilized as an external interface. If you have a use
case for it, please file an issue.

# Alias Conditions

`bitvec` operates on the principle that each bit is an individually-addressed
element of memory. This is, of course, untrue in hardware, and so `bitvec` must
be aware of the underlying memory region and how the bus drives `bitvec`’s
operation.

`bitvec` structures may only be constructed over raw integers. Once constructed,
a `&mut BitSlice` can be split into multiple subslices that do not overlap in
bits, but do overlap in memory elements on the bus. In order to remain correct
in the Rust memory model and in the generated instructions, these split slices
are marked as aliased, and switch over to using coördinated types capable of
handling multiple handles with write capability to the same element. By default,
these types are atomic, however, as discussed above, they can fall back to
`Cell`s instead.

`bitvec` is capable of performing pointer analysis to determine which elements
in a slice region are known to be aliased and which are not. This analysis
depends on the rule that `&`/`&mut` exclusion *and modification* rules apply to
the entire `BitSlice` region, but the [`UnsafeCell`] type sidesteps this: shared
references are still capable of modifying the memory regions that may be viewed
by shared references that do *not* expect volatility.

Instead, `bitvec` uses wrapper types over atoms and cells that disallow mutation
of the underlying memory except through `&mut` exclusive references. These
wrapper types retain the volatility properties of their wrapped types, and so,
for instance, the wrapped atomic will still perform an atomic load from memory
on each access. The only restriction needed is that these types cannot be used
to write into memory that has any possibility of being viewed without a
synchronization control.

`bitvec` has no plans to support shared-mutable `BitSlice` regions.

<!-- Badges -->
[codecov]: https://codecov.io/gh/myrrlyn/bitvec "Code Coverage"
[codecov_img]: https://img.shields.io/codecov/c/github/myrrlyn/bitvec.svg?logo=codecov "Code Coverage Display"
[crate]: https://crates.io/crates/bitvec "Crate Link"
[crate_img]: https://img.shields.io/crates/v/bitvec.svg?logo=rust "Crate Page"
[docs]: https://docs.rs/bitvec "Documentation"
[docs_img]: https://docs.rs/bitvec/badge.svg "Documentation Display"
[downloads_img]: https://img.shields.io/crates/dv/bitvec.svg?logo=rust "Crate Downloads"
[license_file]: https://github.com/myrrlyn/bitvec/blob/master/LICENSE.txt "License File"
[license_img]: https://img.shields.io/crates/l/bitvec.svg "License Display"
[loc]: https://github.com/myrrlyn/bitvec "Repository"
[loc_img]: https://tokei.rs/b1/github/myrrlyn/bitvec?category=code "Repository Size"
[travis]: https://travis-ci.org/myrrlyn/bitvec "Travis CI"
[travis_img]: https://img.shields.io/travis/myrrlyn/bitvec.svg?logo=travis "Travis CI Display"

<!-- Documentation -->
[`Arc`]: https://doc.rust-lang.org/stable/alloc/sync/struct.Arc.html "Arc API reference"
[`AsBits<T>`]: https://docs.rs/bitvec/latest/bitvec/view/trait.AsBits.html "AsBits API reference"
[`AsBitsMut<T>`]: https://docs.rs/bitvec/latest/bitvec/view/trait.AsBitsMut.html "AsBitsMut API reference"
[`AtomicU8`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicU8.html "AtomicU8 API reference"
[`AtomicU64`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicU64.html "AtomicU64 API reference"
[`AtomicUsize`]: https://doc.rust-lang.org/stable/core/sync/atomic/struct.AtomicUsize.html "AtomicUsize API reference"
[`BitArray`]: https://docs.rs/bitvec/latest/bitvec/array/struct.BitArray.html "BitArray API reference"
[`BitBox`]: https://docs.rs/bitvec/latest/bitvec/boxed/struct.BitBox.html "BitBox API reference"
[`BitField`]: https://docs.rs/bitvec/latest/bitvec/fields/trait.BitField.html "BitField API reference"
[`BitOrder`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html "BitOrder API reference"
[`BitSlice`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html "BitSlice API reference"
[`BitSlice<O, T>`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html "BitSlice API reference"
[`BitSlice::split_at_mut`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html#method.split_at_mut "BitSlice::split_at_mut API reference"
[`BitStore`]: https://docs.rs/bitvec/latest/bitvec/store/trait.BitStore.html "BitStore API reference"
[`BitVec`]: https://docs.rs/bitvec/latest/bitvec/vec/struct.BitVec.html "BitVec API reference"
[`BitView`]: https://docs.rs/bitvec/latest/bitvec/view/trait.BitView.html "BitView API reference"
[`Cell`]: https://doc.rust-lang.org/stable/core/cell/struct.Cell.html "Cell API reference"
[`Lsb0`]: https://docs.rs/bitvec/latest/bitvec/order/struct.Lsb0.html "Lsb0 API reference"
[`Msb0`]: https://docs.rs/bitvec/latest/bitvec/order/struct.Msb0.html "Msb0 API reference"
[`Rc`]: https://doc.rust-lang.org/stable/alloc/rc/struct.Rc.html "Rc API reference"
[`UnsafeCell`]: https://doc.rust-lang.org/stable/core/cell/struct.UnsafeCell.html "UnsafeCell API reference"

[`alloc`]: https://doc.rust-lang.org/stable/alloc "alloc API reference"
[`bitarr!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitarr.html "bitarr! API reference"
[`bitbox!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitbox.html "bitbox! API reference"
[`bits!`]: https://docs.rs/bitvec/latest/bitvec/macro.bits.html "bits! API reference"
[`bitvec!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitvec.html "bitvec! API reference"
[`domain`]: https://docs.rs/bitvec/latest/bitvec/domain "Domain module API reference"
[`io::Read`]: https://doc.rust-lang.org/stable/std/io/trait.Read.html "Read API reference"
[`io::Write`]: https://doc.rust-lang.org/stable/std/io/trait.Write.html "Write API reference"
[`serde::Deserialize`]: https://docs.rs/serde/latest/serde/de/trait.Deserialize.html "Deserialize API reference"
[`serde::Serialize`]: https://docs.rs/serde/latest/serde/ser/trait.Serialize.html "Serialize API reference"
[`std`]: https://doc.rust-lang.org/stable/std "std API reference"

[`&/mut BitSlice`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html "BitSlice API reference"

[Bit Ordering]: https://github.com/bitvecto-rs/bitvec/blob/HEAD/book/bit-ordering.md
[docs.rs]: https://docs.rs/bitvec/latest/bitvec "crate API reference"
[examples]: https://github.com/myrrlyn/bitvec/blob/HEAD/examples
[macro]: https://docs.rs/bitvec/latest/bitvec/#macros
[prelude]: https://docs.rs/bitvec/latest/bitvec/prelude

<!-- External References -->
[`radium`]: https://crates.io/crates/radium
[`std::bitset<N>`]: https://en.cppreference.com/w/cpp/utility/bitset
[bitfield]: https://en.cppreference.com/w/cpp/language/bit_field "C++ bitfields"
