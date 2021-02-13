# Changelog <!-- omit in toc -->

All notable changes will be documented in this file.

This document is written according to the [Keep a Changelog][kac] style.

1. [0.21](#021)
   1. [Added](#added)
   1. [Changed](#changed)
1. [0.20.0](#0200)
   1. [Added](#added-1)
      1. [Pointer Overhaul](#pointer-overhaul)
   1. [Changed](#changed-1)
      1. [Aliasing Typesystem](#aliasing-typesystem)
      1. [`&bool` to `BitRef`](#bool-to-bitref)
   1. [Removed](#removed)
1. [0.19.4](#0194)
   1. [Changed](#changed-2)
1. [0.19.3](#0193)
   1. [Added](#added-2)
1. [0.19.2](#0192)
1. [0.19.1](#0191)
1. [0.19.0](#0190)
   1. [Macro Constructor Implementation](#macro-constructor-implementation)
   1. [`BitRegister` Internal Trait](#bitregister-internal-trait)
1. [0.18.3](#0183)
1. [0.18.2](#0182)
1. [0.18.1](#0181)
1. [0.18.0](#0180)
      1. [Bit Arrays in Value Position](#bit-arrays-in-value-position)
      1. [Type-Level Alias Detection](#type-level-alias-detection)
1. [0.17.4](#0174)
1. [0.17.3](#0173)
1. [0.17.2](#0172)
1. [0.17.1](#0171)
1. [0.17.0](#0170)
1. [0.16.2](#0162)
1. [0.16.1](#0161)
1. [0.16.0](#0160)
1. [0.15.2](#0152)
1. [0.15.1](#0151)
1. [0.15.0](#0150)
1. [0.14.0](#0140)
1. [0.13.0](#0130)
1. [0.12.0](#0120)
1. [0.11.3](#0113)
1. [0.11.2](#0112)
1. [0.11.1](#0111)
1. [0.11.0](#0110)
1. [0.10.2](#0102)
1. [0.10.1](#0101)
1. [0.10.0](#0100)
1. [0.9.0](#090)
1. [0.8.0](#080)
1. [0.7.0](#070)
1. [0.6.0](#060)
1. [0.5.0](#050)
1. [0.4.0](#040)
1. [0.3.0](#030)
1. [0.2.0](#020)
1. [0.1.0](#010)

## 0.21

### Added

- The `BitArr!` macro constructs `BitArray` type names.
- `BitVec::from_element` and `BitVec::from_slice` constructors. Thanks to
  GitHub user [@HamishWMC] for reöpening [Issue #6]
- `BitSlice::{first,last}_{one,zero}` finds the index of the first or last bit
  in the bit-slice set to one or zero, respectively. Thanks to GitHub user
  [@seanyoung] for the feature request in [Issue #103].
- `BitSlice::{leading,trailing}_{ones,zeros}` count the length of the *run* of
  the requested bit at the requested edge of the bit-slice. Thanks to GitHub
  user @seanyoung for the feature request in Issue #103.

### Changed

- The `bitarr!` macro no longer constructs `BitArray` type names. In addition,
  it can take a `const` first argument to produce code that is usable in `const`
  contexts, such as producing a `const` or `static` binding. These invocations
  are limited to only using the blessed `Lsb0`, `Msb0`, and `LocalBits` ordering
  tokens, and may not use any other type names for orderings.

- The `bits!` macro now accepts `static` and `static mut` first arguments. These
  direct the macro to produce a hidden `static` item containing a buffer
  produced by `bitarr!(const)`. Borrowing a `BitArray` as a `BitSlice` requires
  code that cannot run in `const` contexts, so this macro may still only be used
  in local expressions, and not in `static` bindings. This behavior is useful
  for ensuring that the macro produces a permanent buffer rather than a
  temporary stack item.

- The `IterOnes` and `IterZeros` bit-finding iterators have some acceleration
  by specialization. The provided orderings will now use the
  `{leading,trailing}_{ones,zeros}` methods in the standard library rather than
  implementing a search directly.

## 0.20.0

This is a major expansion of the crate’s foundation, and has a great deal of
user-visible changes. There are breaking changes to type signatures, but in
practice most of them should be managed through type inference or deprecation
notices.

### Added

- GitHub user [@arucil] requested in [Issue #83] that additional APIs be added
  to match some of those found in the [`bit-set`] crate.

  The methods `.iter_ones()` and `.iter_zeros()` now yield each index where the
  stored bit is set to `1` or `0`, respectively.

- `BitArray` implements `IntoIterator`, matching the standard library’s
  still-unstable implementation and, more importantly, allowing `BitArray` to be
  used as the right-hand-side argument to the crate’s binary operator
  implementations.

- Additionally, `BitVec` can be constructed from iterators of unsigned integers.
  The implementation collects these integers into an ordinary `Vec`tor, then
  converts it in-place into a `BitVec`.

- Mutable iterators over `BitSlice` now have a method, `.remove_alias()`, which
  removes the aliasing marker they use to access memory. This method may only be
  used in loops that do not collect multiple yielded references to the slice
  into the same scope.

  This adapter permits loops that satisfy this condition to remove the
  performance cost of alias-safed memory accesses where the user has ensured
  that no alias conditions will exist.

  As an example, the following loop may safely use `.remove_alias()`:

  ```rust
  use bitvec::prelude::*;

  let bits = bits![mut 0; 10];
  for chunk in unsafe { bits.chunks_exact_mut(3).remove_alias() } {
    chunk.set_all(true);
  }
  ```

  because the loop body creates and destroys exactly one subslice per iteration,
  while this code cannot:

  ```rust
  use bitvec::prelude::*;

  let bits = bits![mut 0; 10];
  let mut iter = bits.chunks_exact_mut(3);
  let a = iter.next().unwrap();
  let b = iter.next().unwrap();
  let c = iter.next().unwrap();
  ```

  because the three subslices `a`, `b`, and `c` cannot have their aliasing
  markers removed, as they are permitted to perform racing accesses to the same
  memory location.

- The expanded pointer system allows the `core::ptr` module to be more fully
  ported as `bitvec::ptr`.

#### Pointer Overhaul

The pointer infrastructure in the crate has been entirely rewritten. This does
not affect the encoding structure used in `*BitSlice` pointers; it is primarily
a typesystem arrangement.

The previous `BitPtr` type has bene renamed to `BitSpan`. `BitSpan` retains all
responsibility for managing the encoding of `*BitSlice` pointers, and is
strictly crate-internal. The `BitPtr` name now refers to a structure that points
to a single bit in a memory location. `BitPtr` is now public API, and is used in
APIs that would return `*bool` in the standard library.

The `BitPtrRange` type implements `Range<*bool>` behavior, as `Range` itself
still uses driver traits that are unstable outside the standard library.

The `BitMut` proxy type is renamed to `BitRef`, and is implemented as a `BitPtr`
with an internal cache.

All pointer types express mutability permissions through the trait system,
rather than using duplicated types as in the language core. The `Mutability`
marker trait is implemented by two types, `Const` and `Mut`, which the pointer
types use to manage

### Changed

Changes to existing behavior in this release were primarily limited to two
components: the exact types used when marking bit-slices as aliased, and the
removal of `&bool` references in favor of the same proxy type that had been
standing in for `&mut bool`.

#### Aliasing Typesystem

The types used when a `&mut BitSlice` aliases its underlying memory are now
specialized wrappers rather than bare `Atomic` or `Cell<>` types. These new
wrappers forbid mutation through shared references, but retain the synchronized
load and store behavior of their wrapped types when accessed. This seals the
last (known) memory unsoundness hole in the crate, and ensures that the
following scenario can no longer cause undefined behavior:

```rust
use bitvec::prelude::*;

let mut data = [0u8; 2]
let bits = data.view_bits_mut::<Msb0>();
let (_, rest) = data.split_at_mut(4);

let sharemut_slice = rest.as_slice();
let (_, immut_slice, _) = rest.domain().region().unwrap();
```

In this example, `sharemut_slice` is a `&[u8::Alias]` slice and `immut_slice` is
a `&[u8]`. Prior to `0.20`, `u8::Alias` was an `AtomicU8` or a `Cell<u8>`,
either of which permit modification through `&` shared references. Doing so
while a `&[u8]` reference views the referent memory is undefined behavior.

Now, `u8::Alias` is `BitSafeU8`, which can be found in the `access` module. This
type family retains the load/store behavior of their eponymous types, but
forbids modifying the referent memory through an `&` shared reference.

In addition, the restriction of `bitvec` types to be only constructed from
ordinary integers is lifted. The construction macros are rewritten to support
these types.

#### `&bool` to `BitRef`

Because the `slice::Iter` iterator now produces `BitRef<Const>` instead of
`&bool`, and `BitRef` is not `Copy`, it no longer has access to the
`Iterator::copied` method. To prevent name resolution errors, it defines an
inherent method `.copied()` that produces an iterator of `bool` and raises a
deprecation notice. It also defines adapter methods, `.by_ref()` and
`.by_val()`, which adapt it to produce references to, or values of, `bool`.

Additionally, most APIs that took or produced `*T` to refer to a region’s base
address now take or produce a `BitPtr` instead.

### Removed

The deprecated methods on `BitView`, which were marked as such in `0.18` and
remained present for two minor versions, have been fully removed.

## 0.19.4

### Changed

The implementation of `BitSlice::copy_from_bitslice` now attempts to accelerate
its behavior from individual-bit where possible.

Where `self` and `src` have identical memory layouts (same starting point as
well as length), it will use `memcpy` to move whole elements as batches.

Additionally, `Lsb0`- and `Msb0`- ordered `BitSlice`s use a specialization hack
to copy by use of their `BitField` batch-movement implementations. This hack is
only usable for `BitField` implementations known to `bitvec` itself.

## 0.19.3

This release has no API changes, and is being issued as a patch rather than a
minor for convenience.

### Added

`BitPtr::ptr_diff` and `BitSlice::offset_from` enable computing the distances
between the heads of two bit-region pointers. This is *only* a defined
computation when both pointers are derived from the same allocation block. These
methods enable `nom` to use `BitSlice` as a sequence provider, but have little
other practical use.

## 0.19.2

Update to `radium 0.5`, which is an internal-only API change. This is not
observable to users of `bitvec`.

## 0.19.1

This updates the `radium` dependency to `0.4`, and uses its fallback types to
provide graceful degradation when a target CPU does not support atomic behavior
for a requested type. The `"atomic"` feature now controls whether the crate will
*attempt* atomic access in alias conditions, not *guarantee* it. This means that
`BitSlice<_, u64>` on a target with only 32-bit atomics will use `Cell`
aliasing, while `BitSlice<_, u32>` on that same target will still be able to use
atomic aliasing.

As there is no observable API change (targets attempting to declare atomic
aliasing on processors that did not support them were already a compiler error),
this is not a significant version increase.

## 0.19.0

This is a small patch release, but must be upgraded to a minor release because
of a name change in public API and implementation change that should not, but
*may*, affect public API.

### Macro Constructor Implementation

The macros used to construct `bitvec` literals have had their implementation
changed. The introduction of the `BitArray` type simplifies the construction of
buffers from token sequences, so `bits!` now produces a `BitArray` on the stack
rather than a hidden `static`.

Specifically, `bits!` changes its expansion from

```rust
{
  static BUFFER: &'static [T; N] = […];
  &BitSlice::<O, T>::from_slice(&BUFFER)[.. LEN]
}
```

to

```rust
(&BitArray::<O, [T; N]>::new([…])[.. LEN])
```

The test suite demonstrates that the compiler is able to correctly extend the
lifetime of the `BitArray` temporary to match the lifetime of the produced
reference. However, if you run into *any* issue where `bits!` calls that
previously worked now fail due to an insufficiently-scoped temporary, please
file an issue.

### `BitRegister` Internal Trait

As `BitMemory` is now able to describe any integer element in memory, but
`BitOrder` is still able to only operate on processor registers, a new trait
`BitRegister` serves to distinguish memory-bus integers from register-integers.
This trait provides no information other than its presence or absence.

`BitOrder` trait functions are modified to require it as the bound on their type
parameters, rather than `BitMemory`. This name change is visible to users, and
thus the reason for the minor release. `BitRegister` is conditionally
implemented according to the supported registers on the target processor.

## 0.18.3

Per [Issue #75], the `BitMemory` trait has been loosened to exclusively describe
integer types, and not be constrained to only the integers that can be used in
processor registers.

This permits the `BitField` functions to transfer integers of any width,
regardless of the processor word size.

## 0.18.2

Commit 6002818 changed the default ordering type-parameter to `Lsb0` instead of
`LocalBits`, but did not update macro constructors to use `Lsb0` when called
without an ordering argument. This caused type errors when using macros and
type declarations in the same slot, such as

```rust
let bits: &'static BitSlice = bits![0];
```

The binding was typed as `&'static BitSlice<Lsb0, usize>`, but the macro as
`&'static BitSlice<LocalBits, usize>`. This is only a problem on big-endian
targets, where `LocalBits` does not alias to `Lsb0`, but even though there are
no known users on big-endian targets, this incorrectness warrants a patch.

## 0.18.1

This fixes [Issue #69] and adds [Pull Request #68].

## 0.18.0

This release was implemented as a total discard and rewrite of the crate. The
rewrite is *largely* a copy of what was discarded, but the crate has been
rebuilt from nothing in order to provide more confidence that all parts of it
were reached. As such, this release has a *lot* of changes.

This release raises the MSRV to `1.44.0`, as [Rust PR #69373] stabilizes the
integer constructors `from_{b,l,n}e_bytes` and removes the need to reïmplement
them internally.

### Added <!-- omit in toc -->

- The CI test harness now covers targets beyond `x86_64-unknown-linux-gnu`,
  thanks to GitHub user [@Alexhuszagh]. `bitvec` guarantees support for all
  targets listed in the CI matrix through at least the next major release. If
  your target is not in this list, please file an issue for inclusion.

- `BitStore` is implemented on the `AtomicUN` corresponding to each `uN` that
  implements `BitStore`, as well as on `Cell<uN>`.

#### Bit Arrays in Value Position

The `BitArray<O, V>` type begins support for emulating the C++ `std::bitset<N>`
type, parameterized over the length in bits. This has been requested in the
past, such as in GitHub [issue #32], and is still (as of writing) not able to be
*correctly* implemented. Instead, `BitArray` is parameterized by a scalar or
array type that is large enough to hold the number of bits that the user wants.

The `bitarr!` macro constructs either values of `BitArray<O, V>` with the same
syntax as the other three macros, or constructs `BitArary<O, V>` typenames
suitable for a number of bits in a given order/store array. Invoked as
`bitarr!(for BITS, in ORDER, STORE)`, it produces a typename that can be used to
correctly type locations that cannot use inference from a value assigned  into
them, such as `struct` fields, `static` bindings, and `const` values.

Until type-level integers stabilize, this is the closest solution to the
`std::bitset<N>` behavior that `bitvec` can provide.

### Changed <!-- omit in toc -->

- The implementation of the `BitStore` trait is refactored to fully separate the
  concepts of memory storage and access. This is not a breaking change to the
  user API, as `BitStore` is an opaque trait that can only be used in marker
  position.

- The concrete effect of the `BitStore` internal refactor is that the default
  case of memory access is no longer atomic. Slices that have not called
  `.split_at_mut` are now guaranteed to elide bus locks to memory when they
  write.

- The `AsBits` trait has been relocated to the `view` module, and split into two
  trait families. The `BitView` trait has methods `.view_bits<O>` and
  `.view_bits_mut<O>`; the `AsBits<T>` and `AsBitsMut<T>` traits have
  `.as_bits<O>` and `.as_bits_mut<O>`, and are intended to correspond to the
  `AsRef<T>` and `AsMut<T>` traits in the standard library.

- The C-compatible ordering alias `Local` is renamed to `LocalBits`, in order to
  deconflict it with the innumerable other uses of the word.

- The default ordering parameter is `Lsb0`, rather than the `LocalBits` type
  alias. `Lsb0` offers consistently better codegen, even on big-endian targets.

#### Type-Level Alias Detection

There is a user-facing breaking change as a result of this work: all methods
which transitively call `.split_at_mut` or `.split_at_mut_unchecked` are now
marked as being of the type `&mut BitSlice<O, T> -> &mut BitSlice<O, T::Alias>`.
This distinction reënables synchronized access to memory. Slices marked with an
aliasing storage parameter are subject to atomic locks or `Cell` thread-unsafety
until the alias mark is removed.

Storage-generic code will need to deal with the `::Alias` markers.
Concretely-typed code will likely not be affected, unless bindings are
explicitly typed.

Any `BitSlice` can be broken into a memory domain description that minimizes the
aliased condition and maximizes the memory that it may access unaliased. The
four methods `.{bit_,}domain{,_mut}()` produce memory descriptors
`{Bit,}Domain{,Mut}`, which subslice the memory region into aliased and
unaliased components.

### Removed <!-- omit in toc -->

- The numeric arithmetic behavior has been fully removed, as per [Issue #17] and
  [Issue #50], filed by GitHub user [@luojia65]. The reason for this removal is
  that `BitSlice` implements lexicographic ordering, which differs from the
  numeric ordering expected by interpreting a `BitSlice` as a variable-length
  2’s-complement un/signed integer.

  Issue #17 requests that the varint behavior be moved to its own crate. No such
  crate currently exists, nor do I *immediately* plan to maintain one. If you
  rely on `bitvec` for a varint implementation, please contact me, and I will
  work with you to rebuild the removed behavior in an external crate, on
  wrapping types that erase the purely lexicographic behavior of `BitSlice`.

- `AsRef<[T]>` and `AsMut<[T]>` are removed. Use the domain methods or
  `.as_slice()`/`.as_mut_slice()` if you require direct access to backing
  storage.

## 0.17.4

### Fixed <!-- omit in toc -->

GitHub user [@kulp] noted in [Issue #55] that an allocator error occurred when
attempting to free a large `BitBox` on macOS. The underlying cause was found to
be an improper assembly of a `BitBox` after modifying the underlying allocation.
Specifically, `BitBox` relied on an incorrect assumption that
`Vec::into_boxed_slice` never moved the base address during resizing.

### Yanked Versions <!-- omit in toc -->

**This is a severe memory error!** As such, *all* prior versions of `bitvec`
have been yanked from [crates.io][crate]. Cargo will fetch yanked crates that
are listed in `Cargo.lock`, but will not use them for resolution of the
`Cargo.toml` manifest.

If you feel strongly that you cannot upgrade from a prior minor version, please
file an issue and I will backport this fix and publish a patch on your minor
series. I will also work with you on an upgrade path.

I have made the decision to yank prior versions as this is now the second memory
management error in the `0.17` series, and is demonstrated to exist back to
`0.11`. Versions older than `0.11` are not supported.

## 0.17.3

### Fixed <!-- omit in toc -->

GitHub users [@Alexhuszagh] and [@obeah] noted in [Issue #43] that the sequence
storage constructors used by the `bits!` macro yielded incorrect behavior. The
error was a copy-paste error in the production of byte reördering functions used
by the macro.

## 0.17.2

### Fixed <!-- omit in toc -->

GitHub user [@ImmemorConsultrixContrarie] reported [Issue #40], and provided
[Pull Request #41]. The defect report was a `STATUS_ILLEGAL_INSTRUCTION` event
that occurred only under `x86_64-pc-windows-gnu` (running the test under `-msvc`
failed to reproduce) when using `BitSlice::get_mut` to produce a `BitMut`
structure.

While PR #41 did not directly resolve the problem, during review, Immemor
suggested a rewrite of the `BitMut` structure to shrink it from three words to
two. This rewrite changed the computation of the memory address to modify in a
manner that resolved the illegal-instruction failure.

This crash is considered a severe bug, as it indicates memory unsafety. Users
are strongly encouraged to update to `0.17.2` immediately.

Thanks again to [@ImmemorConsultrixContrarie] for the report and solution!

## 0.17.1

### Added <!-- omit in toc -->

This patch restores the `cursor` module and its types, as aliases to the `order`
module and their equivalents, with a deprecation warning. Removing these names
entirely, without a deprecation redirect, is technically permissible but morally
in error.

### Changed <!-- omit in toc -->

In addition, the `Bits` trait has been renamed to `AsBits`, to better reflect
its behavior and reduce the chances of name collision, as it is a prelude
export.

### Removed <!-- omit in toc -->

The `AsBits::as_{mut_,}bitslice` deprecation aliases have been removed.

## 0.17.0

### Added <!-- omit in toc -->

- `BitField` trait now has `{load,store}_{le,be}` methods for explicitly
  choosing *element* order when performing storage. The `load`/`store` methods
  default to the target’s byte endiannes as a convenience. These may be
  deprecated in the future, if the explicit choice is strongly preferred.

  See the module and trait documentation for more detail.

- GitHub user [@mystor] provided a `bits!` macro in [Pull Request #34] which
  enables compile-time construction of `&'static BitSlice<O, T>` regions. This
  macro is currently limited to working with the literal `BitOrder`
  implementator names `Local`, `Lsb0`, and `Msb0`. This is a restriction in the
  Rust language (identifiers are not yet associated with types during macro
  expansion), and `bitvec` does not promise to expand support to other names or
  types in the future.

- `usize` implements `BitStore`, and is now the default type argument.

### Changed <!-- omit in toc -->

- Rename the `cursor` module to `order`, the `Cursor` trait to `BitOrder`, and
  the `BigEndian` and `LittleEndian` types to `Msb0` and `Lsb0`, respectively
- Fold `BitsMut` into `Bits`

### Removed <!-- omit in toc -->

- The Rust types `T`, `[T; 0 <= N <= 32]`, and `[T]` for `T: BitStore` no longer
implement `AsRef<BitSlice<_, T>>` or `AsMut<BitSlice<_, T>>`. This decision was
made due to consideration of [Issue #35], by GitHub user [@Fotosmile].

- The `store::Word` type alias is removed, as it was a patch for `usize`’s
  absence as a `BitStore` type. All uses of the `Word` alias can be replaced
  with `usize` without issue.

## 0.16.2

### Fixed <!-- omit in toc -->

Updated `radium` dependency to `0.3`, which enables it to compile on the
`thumbv7m-none-eabi` target. This addresses [Issue #36], which noted that
`bitvec` failed to compile for that target due to reduced support for atomic
types in `core`. Thanks to GitHub user [@lynaghk] for the report.

## 0.16.1

This is a hotfix for [Issue #33], filed by GitHub user [@jonas-schievink].
`BitVec::reserve` computed an incorrect element count to pass to `Vec::reserve`,
causing `BitVec::resize` to panic when its `BitVec::reserve` call failed to
sufficiently allocate memory before `BitVec::set_len` expanded into the memory
it expected to be present.

## 0.16.0

### Added <!-- omit in toc -->

- `Cursor` now provides a `mask` function, which produces a one-hot mask usable
  for direct memory access. Implementors of `Cursor` may use the default, or
  provide their own.
- `Bits` and `BitsMut` renamed their methods to `bits` and `bits_mut`,
  respectively; `as_bitslice` and `as_mut_bitslice` are marked deprecated and
  will be removed in `0.17`.
- The `BitField` trait allows `BitSlice<BigEndian, _>` and
  `BitSlice<LittleEndian, _>` to provide behavior analagous to bitfields in C
  and C++ `struct` definitions. This trait provides `load` and `store` methods
  on `BitSlice`s with those two `Cursor`s which allow for parallel access to the
  underlying memory. This trait is currently not able to be implemented by
  downstream crates; this restriction may ease in the future.

  The `load` and `store` methods are generic over `BitStore` value types,
  allowing users to load and store values of any of the four fundamental widths
  out of and into a `BitSlice` of any storage type. Users are able to, for
  example, use this trait to load and store `u32` values into `BitSlice<_, u8>`
  byte sequences.

  The behavior implemented in this crate follows local memory conventions as
  best it can. When storing a value into memory, the least significant part of
  the value will be in the least significant storage element of the slice, and
  the bits in each storage element’s region for value storage will be in
  standard memory order. This behavior *should* provide maximum compatibility
  for interoperability with the bitfield implementations in C and C++, and the
  bitstring implementation in Erlang.
- The `cursor::Local` type alias is a default bit ordering. Big-endian targets
  set it to `cursor::BigEndian`; all other targets set it to
  `cursor::LittleEndian`.
- The `store::Word` type alias is a default unit size. Targets with 32-bit CPU
  words set it to `u32`; 64-bit CPU word targets set it to `u64`; all other
  targets set it to `u8`.
- `BitSlice` is able to provide mutable borrowing access through iteration and
  inherent methods by using the `BitGuard` custom referential type. This type is
  not able to be used as an `&mut bool`, so the API is still not an exact mirror
  of the standard library.

### Changed <!-- omit in toc -->

- The default order and storage type parameters for all type constructors in the
  library have been changed. This means that `BitSlice`, `BitBox`, `BitVec`, and
  the `bitbox!` and `bitvec!` macros, are all changing the produced type if you
  have not specified their ordering and storage. The new default storage type is
  the target CPU word (`u32` on 32-bit systems, `u64` on 64-bit, `u8` on other)
  and the new default order type is the target byte ordering (`BigEndian` on
  big-endian, `LittleEndian` on little-endian and unknown).

  This change is expected to break dependent crates. The fix is straightforward:
  specify the types produced by this crate’s constructors, or adapt the types
  that receive them.

  This change was made in order to provide performance advantages by using the
  native CPU word size, and to ease choice of a bit ordering in usages that do
  not particularly care about the underlying memory’s appearance.
- The `BitSlice` inherent and trait API is updated to more closely track the
  standard library’s API as of `1.36.0`. The major change to existing code is
  that the `Iterator` implementations are now of `&bool`, not `bool`.
- The internal process that translates `BitSlice` operations into access
  operations on underlying memory has been rewritten. Production of contended
  references to bare fundamentals is now forbidden, and all access is mediated
  through either atomic (default) or `Cell` types.
- Bit indexing is more firmly encoded in the type system, which reduces the load
  of runtime assertions.
- `BitSlice::as_slice` excludes partial edge elements. `BitBox` and `BitVec` do
  not.

### Removed <!-- omit in toc -->

- `BitSlice::change_cursor` and `change_cursor_mut` allow incorrectly aliasing
  memory with different slice handles, because there is no way for them to
  compute the electrical positions they govern and then construct new indices in
  the target `Cursor` that match those positions.

  Example:

  ```rust
  use bitvec::prelude::*;
  let mut elt = 0u8;
  let bits = elt.bits_mut::<BigEndian>();
  let (head, tail) = bits.split_at_mut(4);
  let tail = tail.change_cursor_mut::<LittleEndian>();
  ```

  `head` now points at the first four bits in big-endian order, and tail at the
  last four bits in little-endian order, and these indices all map to the high
  nibble of `elt`. `head` and `tail` mutably alias.

  These functions are retained in `BitBox` and `BitVec`, as those types do not
  allow memory contention.

## 0.15.2

### Changed <!-- omit in toc -->

The `bitvec![bit; rep]` construction macro has its implementation rewritten to
be much faster. This fault was reported by GitHub user [@caelunshun] in
[Issue #28].

## 0.15.1

### Removed <!-- omit in toc -->

The `Send` implementation on `BitSlice` is removed when the `atomic` feature is
disabled.

While the `x86` architecture provides hardware guarantees that a
read/modify/write instruction sequence will update all other views of the
referent data, this is a property of the specific underlying machine and *not*
a property of the Rust abstract machine as interpreted by the compiler and LLVM.
As such, while `&mut BitSlice` references that alias the same underlying memory
element will not collide with each other in practice, they still must use atomic
operations in order to satisfy the Rust abstract machine.

The atomic feature is provided by default, and users must explicitly disable it
in order to disable atomic instruction access and thus remove the `Send` impl
allowing `&mut BitSlice` to cross threads.

Because this change does not affect the default interface exported by the crate,
I have decided to make this a patch release rather than bump the minor version.

## 0.15.0

### Changed <!-- omit in toc -->

The minimum compiler version was increased to `1.36.0`, which stabilized the
`alloc` crate. As such, the `#![feature(alloc)]` flag has been removed from the
library, and usage as `--no-default-features --features alloc` may safely use
allocation on the stable compiler series.

As `alloc` is available on a stable compiler, the `alloc` *crate feature* has
been made a strict dependency of the `std` crate feature.

Use of `--no-default-features` continues to set the crate in `#![no_std]` mode,
with no allocation support. `--no-default-features --features alloc` adds a
dependency on `alloc`, and the allocating types. The `std` feature alone now
*only* adds operating-system interfaces, such as `io::Write`.

`std` depends on `alloc`, so using the `std` feature will pull in allocation.

## 0.14.0

### Added <!-- omit in toc -->

- `add_assign_reverse` on `BitSlice` and `BitVec`, and `add_reverse` on
  `BitBox` and `BitVec`.

  These methods perform left-to-right addition, propagating the carry from the
  0th bit in the sequence to the nth. On `BitSlice`, `add_assign_reverse`
  returns the carry-out bit. On `BitVec`, `add_assign_reverse` and `add_reverse`
  push the carry-out to the right end of the vector.

  This feature was requested in [Issue #16], by GitHub user [@GeorgeGkas].

## 0.13.0

### Changed <!-- omit in toc -->

- The `BitPtr<T>` internal representation replaced the elements/tail tuple with
  a bit-length counter. Most of the changes as a result of this were purely
  internal, but as it affected the `Serde` representation, this was moved to a
  new version.

## 0.12.0

### Added <!-- omit in toc -->

- `BitSlice::at` simulates a write reference to a single bit. It creates an
  instance of `slice::BitGuard`, which holds a mutable reference to the
  requested bit and a `bool` slot. `BitGuard` implements `Deref` and `DerefMut`
  to its local `bool`, and writes its local `bool` value to the specified bit in
  `Drop`.

  This allows writing the following:

  ```rust
  *slice.at(index) = some_bit();
  ```

  as equivalent to

  ```rust
  slice.set(index, some_bit());
  ```

  Note that binding the value produced by `BitSlice::at` will cause the write to
  occur when that binding *goes out of scope*, not in the assigning statement.

  ```rust
  let slot = slice.at(index);
  *index = some_bit();
  //  write has not yet occurred in `slot`
  //  ... more work
  //  <- write occurs HERE
  ```

  In practice, this should not be an issue, since the rules for mutable borrows
  mean that the original slice is not observable until the slot value produced
  by `.at()` goes out of scope.

- **SEE THE RENAME BELOW.** The `Bits` and `BitsMut` traits provide reference
  conversion from many Rust fundamental types to `BitSlice` regions. `Bits` is
  analagous to `AsRef`, and `BitsMut` to `AsMut`. These traits are implemented
  on the `BitStore` fundamentals, slices of them, and arrays up to 32.

- `BitSlice::get_unchecked` and `BitSlice::set_unchecked` perform read and write
  actions without any bounds checking to ensure the index is within the slice
  bounds. This allows faster work in tight loops where the index is already
  checked against the slice length. These methods are, of course, incredibly
  unsafe, as they are raw memory access with no safeguards to ensure the read or
  write is within bounds.

### Changed <!-- omit in toc -->

- `BitVec::retain` changed its function argument from `(bool) -> bool` to
  `(usize, bool) -> bool`, and passes the index as well as the value.
- `Display` implementations of the `BitIdx` and `BitPos` types now just defer to
  the interior number, and do not write their own type.
- `BitSlice::as_ptr` and `::as_mut_ptr` now return the null pointer if they are
  the empty slice, rather than a dangling pointer.
- The trait formerly known as `Bits` in all previous versions is now `BitStore`,
  and the module `bits` is renamed to `store`. Only the `Bits` → `BitStore`
  rename affects public API.
- Rewrote the README to better describe all the recent work.
- The documentation examples use the new `as_bitslice` methods instead of the
  much less pleasant `Into` conversions to create `BitSlice` handles. This also
  serves to demonstrate the new favored method to access regions as bit slices.

## 0.11.3

[Issue #15]: Incorrect validity check in `BitIdx::span`; excluded tail indices
which were used in `BitVec::push`, inducing false `panic!` events. Thanks to
GitHub user [@schomatis] for the report.

## 0.11.2

### Added <!-- omit in toc -->

- `BitBox` and `BitVec` implement [`Sync`], as discussion with [@ratorx] and
  more careful reading of the documentation for `Sync` has persuaded me that
  this is sound.

## 0.11.1

[Issue #12]: I left in an `eprintln!` statement from debugging
`BitSlice::set_all`. Thanks to GitHub user [@koushiro] for the report.

## 0.11.0

~~This contains the last (planned) compiler version upgrade, to `1.34.0`, and~~
~~the last major feature add before `1.0`: Serde-powered de/serialization.~~

Deserialization is not possible without access to an allocator, so it is behind
a feature gate, `serde`, which depends on the `alloc` feature.

`BitSlice`, `BitBox`, and `BitVec` all support serialization, and `BitBox` and
`BitVec` support deserialization

### Added <!-- omit in toc -->

- `serde` feature to serialize `BitSlice`, `BitBox`, and `BitVec`, and
  deserialize `BitBox` and `BitVec`.
- `change_cursor<D>` method on `BitSlice`, `BitBox`, and `BitVec`, which enable
  changing the element traversal order on a data set without modifying that
  data. This is useful for working with slices that have their cursor type
  erased, such as crossing serialization or foreign-language boundaries.
- The internal `atomic` module and `Atomic` trait permit atomic access to
  elements for the `Bits` trait to use when performing bit set operations. This
  is not exposed to the public API.
- Internal domain models for the memory regions governed by `BitPtr`. These
  models provide improved logical support for manipulating bit sequences with as
  little inefficiency as possible.
- `BitPtr::bare_parts` and `BitPtr::region_data` internal APIs for accessing
  components of the pointer structure.
- Clippy is now part of the development routine.
- `bitbox!` macro wraps `bitvec!` to freeze the produced vector.

### Changed <!-- omit in toc -->

- The internal `Bits` trait uses a `const fn` stabilized in `1.33.0` in order to
  compute type information, rather than requiring explicit statements in the
  implementations. It now uses synchronized access to elements for write
  operations, to prevent race conditions between adjacent bit slices that
  overlap in an element.
- The internal `BitPtr` representation had its bit pattern rules modified. There
  is now only one empty-slice region representation, and the pointer is able to
  index one more element than it previously could. In addition, `BitPtr::tail()`
  produces `0` when empty, rather than `T::BITS`, allowing for more correct
  values in `serde` de/serialization.

### Removed <!-- omit in toc -->

- `BitPtr::set_head` and `BitPtr::set_tail`: in practice, `::new` and
  `::new_unchecked` were used at all potential use sites for these functions, as
  they are more powerful and better validated.
- `BitPtr::head_elt`, `BitPtr::body_elts`, and `BitPtr::tail_elt` were
  superseded by the `domain` module. Their public use is better served by
  the `AsRef` trait.
- `BitPtr::is_full`: removed for being never used in the library, and not an
  interesting query.

### Fixed <!-- omit in toc -->

- [Issue #9] revealed a severe logic error in the construction of bit masks in
  `Bits::set_at`. Thanks to GitHub user [@torce] for the bug report!
- [Issue #10] revealed a logic error in the construction of bit vectors from bit
  slices which did not begin at the front of an element.

  `BitVec::from_bitslice` cloned the entire underlying `&[T]` of the source
  `BitSlice`, which is incorrect, as `BitVec` currently cannot support offset
  head cursors. The correct behavior is to use `<BitVec as FromIterator<bool>>`
  to collect the source slice into a fresh `BitVec`.

  It may be possible in the future to permit offset head cursors in `BitBox` and
  `BitVec`.

  Thanks to GitHub user [@overminder] for the bug report!
- `BitSlice::set_all` had a bug where fully spanned elements were zeroed, rather
  than filled with the requested bit. This was only detected when the
  subtraction example in the `README` code sample broke. Resolution: add a
  function to the `Bits` trait which fills an element with a bit, producing all
  zero or all one.

## 0.10.2

Bugfix for [Issue #8]. This provides explicit implementations of the threading
traits `Send` and `Sync`. These traits were formerly automatically implemented;
the implementation change in `0.10.0` appears to have removed the automatic
impls.

`BitSlice` is both `Send` and `Sync`, as it is unowned memory. `BitBox` and
`BitVec` are `Send` but not `Sync`, as they are owned memory.

Thanks to GitHub user [@ratorx] for the report!

## 0.10.1

Bugfix for [Issue #7]. `BitSlice::count_ones` and `BitSlice::count_zeros`
counted the total number of bits present in a slice, not the number of bits set
or unset, when operating inside a single element.

The small case used `.map().count()`, but the large case correctly used
`.map().filter().count()`. The missing `.filter()` call, to remove unset or set
bits from the counting, was the cause of the bug.

Thanks to GitHub user [@geq1t] for the report!

## 0.10.0

This version was a complete rewrite of the entire crate. The minimum compiler
version has been upgraded to `1.31.0`. The crate is written against the Rust
2018 edition of the language. ~~It will be a `1.0` release after polishing.~~

### Added <!-- omit in toc -->

- `BitPtr` custom pointer representation. This is the most important component
  of the rewrite, and what enabled the expanded feature set and API surface.
  This structure allows `BitSlice` and `BitVec` to have head cursors at any bit,
  not just at the front edge of an element. This allows the crate to support
  arbitrary range slicing and slice splitting, and in turn greatly expand the
  usability of the slice and vector types.

  The `BitPtr` type is wholly crate-internal, and renders the `&BitSlice` and
  `BitVec` handle types ***wholly incompatible*** with standard Rust slice and
  vector handles. With great power comes great responsibility to never, ever,
  interchange these types through any means except the provided translation API.

- Range indexing and more powerful iteration. Bit-precision addressing allows
  arbitrary subslices and enables more of the slice API from `core`.

### Changed <!-- omit in toc -->

- Almost everything has been rewritten. The git diff for this version is
  horrifying.

- Formatting traits better leverage the builtin printing structures available
  from `core::fmt`, and are made available on `no_std`.

### Removed <!-- omit in toc -->

- `u64` is only usable as the storage type on 64-bit systems; it has 32-bit
  alignment on 32-bit systems and as such is unusable there.

## 0.9.0

### Changed <!-- omit in toc -->

- The trait `Endian` has been renamed to `Cursor`, and all type variables
  `E: Endian` have been renamed to `C: Cursor`.

- The `Bits` trait is no longer bound by `Default`.

## 0.8.0

### Added <!-- omit in toc -->

- `std` and `alloc` features, which can be disabled for use in `#![no_std]`
  libraries. This was implemented by Robert Habermeier, `rphmeier@gmail.com`.

  Note that the `BitSlice` tests and all the examples are disabled when the
  `alloc` feature is not present. They will function normally when `alloc` is
  present but `std` is not.

### Changed <!-- omit in toc -->

- Compute `Bits::WIDTH` as `size_of::<Self>() * 8` instead of `1 << Bits::INDX`.

## 0.7.0

### Added <!-- omit in toc -->

- `examples/readme.rs` tracks the contents of the example code in `README.md`.
  It will continue to do so until the `external_doc` feature stabilizes so that
  the contents of the README can be included in the module documentation of
  `src/lib.rs`.

- Officially use the Rust community code of conduct.

- README sections describe why a user might want this library, and what makes it
  different than `bit-vec`.

### Changed <!-- omit in toc -->

- Update minimum Rust version to `1.30.0`.

  Internally, this permits use of `std` rather than `::std`. This compiler
  edition does not change *intra-crate* macro usage. Clients at `1.30.0` and
  above no longer need `#[macro_use]` above `extern crate bitvec;`, and are able
  to import the `bitvec!` macro directly with `use bitvec::bitvec;` or
  `use bitvec::prelude::*`.

  Implementation note: References to literals stabilized at *some* point between
  `1.20.0` and `1.30.0`, so the static bool items used for indexing are no
  longer needed.

- Include numeric arithmetic as well as set arithmetic in the README.

## 0.6.0

### Changed <!-- omit in toc -->

- Update minimum Rust version to `1.25.0` in order to use nested imports.
- Fix logic in `Endian::prev`, and re-enabled edge tests.
- Pluralize `BitSlice::count_one()` and `BitSlice::count_zero()` function names.
- Fix documentation and comments.
- Consolidate implementation of `bitvec!` to not use any other macros.

## 0.5.0

### Added <!-- omit in toc -->

- `BitVec` and `BitSlice` implement `Hash`.

- `BitVec` fully implements addition, negation, and subtraction.

- `BitSlice` implements in-place addition and negation.
  - `impl AddAssign for BitSlice`
  - `impl Neg for &mut BitSlice`

  This distinction is required in order to match the expectations of the
  arithmetic traits and the realities of immovable `BitSlice`.

- `BitSlice` offers `.all()`, `.any()`, `.not_all()`, `.not_any()`, and
  `.some()` methods to perform n-ary Boolean logic.
  - `.all()` tests if all bits are set high
  - `.any()` tests if any bits are set high (includes `.all()`)
  - `.not_all()` tests if any bits are set low (includes `.not_all()`)
  - `.not_any()` tests if all bits are set low
  - `.some()` tests if any bits are high and any are low (excludes `.all()` and
    `.not_all()`)

- `BitSlice` can count how many bits are set high or low with `.count_one()` and
  `.count_zero()`.

## 0.4.0

### Added <!-- omit in toc -->

`BitSlice::for_each` provides mutable iteration over a slice. It yields each
successive `(index: usize, bit: bool)` pair to a closure, and stores the return
value of that closure at the yielded index.

`BitVec` now implements `Eq` and `Ord` against other `BitVec`s. It is impossible
at this time to make `BitVec` generic over anything that is `Borrow<BitSlice>`,
which would allow comparisons over different ownership types. The declaration

```rust
impl<A, B, C, D, E> PartialEq<C> for BitVec<A, B>
where A: Endian,
    B: Bits,
    C: Borrow<BitSlice<D, E>>,
    D: Endian,
    E: Bits,
{
    fn eq(&self, rhs: C) { … }
}
```

is impossible to write, so `BitVec == BitSlice` will be rejected.

As with many other traits on `BitVec`, the implementations are just a thin
wrapper over the corresponding `BitSlice` implementations.

### Changed <!-- omit in toc -->

Refine the API documentation. Rust guidelines recommend imperative rather than
descriptive summaries for function documentation, which largely meant stripping
the trailing -s from the first verb in each function document.

I also moved the example code from the trait-level documentation to the
function-level documentation, so that it would show up an `type::func` in the
`rustdoc` output rather than just `type`. This makes it much clearer what is
being tested.

### Removed <!-- omit in toc -->

`BitVec` methods `iter` and `raw_len` moved to `BitSlice` in `0.3.0` but were
not removed in that release.

The remaining debugging `eprintln!` calls have been stripped.

## 0.3.0

Split `BitVec` off into `BitSlice` wherever possible.

### Added <!-- omit in toc -->

- The `BitSlice` type is the `[T]` to `BitVec`'s `Vec<T>`. `BitVec` now `Deref`s
  to it, and has offloaded all the work that does not require managing allocated
  memory.
- Almost all of the public API on both types has documentation and example code.

### Changed <!-- omit in toc -->

- The implementations of left- ard right- shift are now faster.
- `BitVec` can `Borrow` and `Deref` down to `BitSlice`, and offloads as much
  work as possible to it.
- `Clone` is more intelligent.

## 0.2.0

Improved the `bitvec!` macro.

### Changed <!-- omit in toc -->

- `bitvec!` takes more syntaxes to better match `vec!`, and has better
  runtime performance. The increased static memory used by `bitvec!` should be
  more than counterbalanced by the vastly better generated code.

## 0.1.0

Initial implementation and release.

### Added <!-- omit in toc -->

- `Endian` and `Bits` traits
- `BitVec` type with basic `Vec` idioms and parallel trait implementations
- `bitvec!` generator macro

[@Alexhuszagh]: https://github.com/Alexhuszagh
[@Fotosmile]: https://github.com/Fotosmile
[@GeorgeGkas]: https://github.com/GeorgeGkas
[@HamishWMC]: https://github.com/HamishWMC
[@ImmemorConsultrixContrarie]: https://github.com/ImmemorConsultrixContrarie
[@arucil]: https://github.com/arucil
[@caelunshun]: https://github.com/caelunshun
[@geq1t]: https://github.com/geq1t
[@jonas-schievink]: https://github.com/jonas-schievink
[@koushiro]: https://github.com/koushiro
[@kulp]: https://github.com/kulp
[@luojia65]: https://github.com/luojia65
[@lynaghk]: https://github.com/lynaghk
[@mystor]: https://github.com/mystor
[@obeah]: https://github.com/obeah
[@overminder]: https://github.com/overminder
[@ratorx]: https://github.com/ratorx
[@schomatis]: https://github.com/schomatis
[@seanyoung]: https://github.com/seanyoung
[@torce]: https://github.com/torce
[Issue #6]: https://github.com/bitvecto-rs/bitvec/issues/6
[Issue #7]: https://github.com/bitvecto-rs/bitvec/issues/7
[Issue #8]: https://github.com/bitvecto-rs/bitvec/issues/8
[Issue #9]: https://github.com/bitvecto-rs/bitvec/issues/9
[Issue #10]: https://github.com/bitvecto-rs/bitvec/issues/10
[Issue #12]: https://github.com/bitvecto-rs/bitvec/issues/12
[Issue #15]: https://github.com/bitvecto-rs/bitvec/issues/15
[Issue #16]: https://github.com/bitvecto-rs/bitvec/issues/16
[Issue #17]: https://github.com/bitvecto-rs/bitvec/issues/17
[Issue #28]: https://github.com/bitvecto-rs/bitvec/issues/28
[Issue #32]: https://github.com/bitvecto-rs/bitvec/issues/32
[Issue #33]: https://github.com/bitvecto-rs/bitvec/issues/33
[Issue #35]: https://github.com/bitvecto-rs/bitvec/issues/35
[Issue #36]: https://github.com/bitvecto-rs/bitvec/issues/36
[Issue #40]: https://github.com/bitvecto-rs/bitvec/issues/40
[Issue #43]: https://github.com/bitvecto-rs/bitvec/issues/43
[Issue #50]: https://github.com/bitvecto-rs/bitvec/issues/50
[Issue #55]: https://github.com/bitvecto-rs/bitvec/issues/55
[Issue #69]: https://github.com/bitvecto-rs/bitvec/issues/69
[Issue #75]: https://github.com/bitvecto-rs/bitvec/issues/75
[Issue #83]: https://github.com/bitvecto-rs/bitvec/issues/83
[Issue #103]: https://github.com/bitvecto-rs/bitvec/issues/103
[Pull Request #34]: https://github.com/bitvecto-rs/bitvec/pull/34
[Pull Request #41]: https://github.com/bitvecto-rs/bitvec/pull/41
[Pull Request #68]: https://github.com/bitvecto-rs/bitvec/pull/68
[Rust PR #69373]: https://github.com/rust-lang/rust/pull/69373/
[`Sync`]: https://doc.rust-lang.org/stable/core/marker/trait.Sync.html
[`bit-set`]: https://crates.io/crates/bit-set
[crate]: https://crates.io/crates/bitvec
[kac]: https://keepachangelog.com/en/1.0.0/
