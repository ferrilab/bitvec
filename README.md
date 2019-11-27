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

# Table of Contents <!-- omit in toc -->

1. [Introduction](#introduction)
   1. [Unique Capabilities](#unique-capabilities)
   1. [Competitors](#competitors)
1. [Usage](#usage)
   1. [Code Sample](#code-sample)
1. [API](#api)
   1. [Data Structures](#data-structures)
      1. [`BitSlice`](#bitslice)
      1. [`BitVec`](#bitvec)
      1. [`BitBox`](#bitbox)
   1. [Traits](#traits)
      1. [`BitOrder`](#bitorder)
      1. [`BitStore`](#bitstore)
      1. [`BitField`](#bitfield)
      1. [`Bits`](#bits)
   1. [Bit Orderings](#bit-orderings)
   1. [Macros](#macros)
1. [Feature Flags](#feature-flags)
   1. [`alloc`](#alloc)
   1. [`atomic`](#atomic)
   1. [`serde`](#serde)
   1. [`std`](#std)
1. [Warnings](#warnings)
1. [Planned Features](#planned-features)

# Introduction

`bitvec` enables Rust projects to have complete, bit-level, control of memory,
with types that fit in with existing Rust idioms and patterns. The bit-precision
pointers in this crate allow creation of more powerful bit-masks, set
arithmetic, compact data storage, and I/O packet processing.

The core export of this crate is the type `BitSlice`. This type describes a
region of memory with individually-addressable bits. It is accessed by standard
Rust references: `&BitSlice<_, _>` and `&mut BitSlice<_, _>`. These references
are able to describe and operate on regions that start and end on any arbitrary
bit address, without requiring alignment to a memory element boundary.

Additionally, this crate exports a `BitVec` resizable type for dynamic
construction of `BitSlice` buffers.

## Unique Capabilities

`bitvec` has three features which distinguish it from the plethora of other bit
vector and bitstream I/O crates available: the `&BitSlice` reference handle,
proxy reference types which allow mutable references to individual bits, and
user-provided bit ordering.

1. A specialized pointer type enables `bitvec` to describe any region of memory
   with bit-level precision using only two machine words of space. This
   compacted pointer type is not found in any other bit-vector library, and
   enables the construction of `&BitSlice<O, T>` and `&mut BitSlice<O, T>`
   reference types. These types can then be used in trait APIs that expect
   references, and can be correctly traced by the borrow checker for aliasing
   and lifetime rules.

   The region handles `&/mut BitSlice`, `BitBox`, and `BitVec` are all the same
   size as their standard library counterparts `&/mut [bool]`, `Box<[bool]>`,
   and `Vec<bool>`.

1. Additionally, `BitSlice` has a child type, `BitMut`. Restrictions in the Rust
   language do not allow this to be used as a referent type (there is no
   `&mut Bit`). However, this is a subtype of `&mut BitSlice` which implements
   `Deref` and `DerefMut` to a local `bool`, and uses `Drop` to write its bool
   into a parent `BitSlice`. This allows for inelegant, but working, mutable
   borrowing of single bits.

1. Other bit-vector crates allow users to specify the type of memory element
   (one of the unsigned integer fundamental types) used by a bit region, but
   only `bitvec` also allows users to specify the ordering of bits within those
   elements. This parametricity enables `bitvec` to provide the fastest behavior
   as the default condition, while also allowing users to choose the ordering
   that matches their specific requirements.

   Least-significant-bit-first ordering is typically faster than
   most-significant-bit-first, as it is a single instruction `1 << idx` to
   produce a mask. However, many I/O protocols require
   most-significant-bit-first ordering. `bitvec` serves both use cases with
   ease, whereas other crates are specialized to one scenario and penalized in
   others.

## Competitors

There are many published Rust crates in this area of work. Most of them focus on
one particular use case for bitstreams, and cannot be extended to others. Of the
crates that provide a bit-level view of memory, `bitvec` is the most general,
most capable, and provides the highest degree of fidelity to the standard
library.

`bitvec` does *not* provide a small-vector optimization, memory compression, or
discontiguous memory structures. There are crates that provide these, or you can
build these from `bitvec` structures, but they are currently outside the scope
of the `bitvec` project.

# Usage

**Minimum Supported Rust Version:** `1.36.0`

The `1.36` release stablized the `alloc` crate, allowing the allocation types
(`BitVec`, `BitBox`) to be used in `#![no_std]` environments with the stable
compiler series.

Disabling the default features and *not* enabling `features = ["alloc"]` lowers
the minimum stable Rust version to `1.34.0`, which stabilized the atomic types
used internally. Disabling `features = ["atomic"]` does not lower the minimum
Rust version further, as the `radium` dependency is unconditionally floored at
1.34.

To use `bitvec`, depend on it in your Cargo manifest:

```toml
# Cargo.toml

[dependencies]
bitvec = "0.17"
```

and import its prelude anywhere you need to use its types:

```rust
//  src/lib.rs

use bitvec::prelude::*;
```

The prelude imports the data types, traits, macros, and type aliases needed to
make the crate usable in dependent code.

You can also bring the prelude module into scope without importing its symbols
directly, to avoid contaminating the local scope:

```rust
//  src/lib.rs

use bitvec::prelude as bv;
```

which will require a `bv::` prefix to use any of the prelude symbols.

The symbols imported by the prelude are:

- [`BitField`]: provides an analogue of C++ bitfields
- [`BitOrder`]: translates semantic indices to bit positions within memory
- [`BitSlice`]: specialization of `[bool]`
- [`BitStore`]: describes the unsigned integer types used to store bits
- [`Bits`]: conversion traits from Rust types to `&/mut BitSlice`
- [`Lsb0`]: a bit ordering, from least significant up to most significant
- [`Local`]: the local C bit ordering
- [`Msb0`]: a bit ordering, from most significant down to least significant
- [`Word`]: the local CPU word size

Additionally, when targeting a system where `alloc` is present, the prelude adds
the following:

- [`BitBox`]: specialization of `Box<[bool]>`
- [`BitVec`]: specialization of `Vec<bool>`
- [`bitbox!`]: a `vec!`-like macro which constructs `BitBox`es
- [`bitvec!`]: a `vec!`-like macro which constructs `BitVec`s

## Code Sample

This snippet highlights a selection of library functionality. It is deliberately
not representative of likely usage.

```rust
use bitvec::prelude::*;

use std::iter::repeat;

fn main() {
  //  macro constructor
  let mut bv = bitvec![Msb0, u8; 0, 1, 0, 1];

  //  `BitVec` has the `Vec` inherent API
  bv.reserve(8);

  //  and can be filled from any source of `bool`
  bv.extend(repeat(false).take(4));
  bv.extend(repeat(true).take(4));

  //  `BitSlice` can yield its raw memory
  assert_eq!(
    bv.as_slice(),
    &[0b0101_0000, 0b1111_0000],
    //  ^ index 0       ^ index 11
  );
  assert_eq!(bv.len(), 12);
  assert!(bv.capacity() >= 16);

  //  `BitVec`, like `Vec`, is a LIFO stack
  bv.push(true);
  bv.push(false);
  bv.push(true);

  //  `BitSlice` has indexing
  assert!(bv[12]);
  assert!(!bv[13]);
  assert!(bv[14]);
  assert!(bv.get(15).is_none());

  //  … and range indexing
  let last = &bv[12 ..];
  assert_eq!(last.len(), 3);
  assert!(last.any());

  (0 .. 3).for_each(|_| {
    bv.pop();
  });

  //  `BitSlice` provides set arithmetic against any `bool` source
  bv &= repeat(true);
  bv |= repeat(false);
  //  Invert all live bits
  bv ^= repeat(true);
  //  And again
  bv = !bv;

  //  `BitVec` also has rudimentary `BigInt` capability
  let one = bitvec![Msb0, u8; 1];
  bv += one.clone();
  assert_eq!(
    bv.as_slice(),
    &[0b0101_0001, 0b0000_0000],
  );
  bv -= one;
  assert_eq!(
    bv.as_slice(),
    &[0b0101_0000, 0b1111_0000],
  );

  //  It can iterate
  let mut count = 0;
  for bit in bv.iter() {
    if *bit {
      count += 1;
    }
  }
  assert_eq!(count, 6);

  //  … mutably
  for (idx, mut bit) in bv.iter_mut().enumerate() {
    *bit ^= idx % 2 == 0;
  }

  //  `BitSlice` can store variables
  bv[1 .. 7].store(0x3Fu8);
  //  and fetch them
  assert_eq!(bv[1 .. 7].load::<u8>(), Some(0x3F));
}
```

All `bitvec` types are designed to be removable wrappers over raw memory
elements. `BitSlice<O, T>` can unwrap into a slice `[T]`, `BitVec<O, T>` into a
vector `Vec<T>`, and `BitBox<O, T>` into a boxed slice `Box<[T]>`. They also
offer zero-copy methods which convert from their standard library counterpart
into themselves. This allows users to prepare memory however they wish, wrap it
in bit-resolution views, and then unwrap it when they are finished.

# API

The crate has a large API surface, as it provides a specialization of `core`’s
slice fundamental and `alloc`’s boxed slice and vector types. These three types
implement the entirety (as far as is possible) of the standard library’s API
surface for these types. In addition, `bitvec` exposes many of the support types
required to make it work.

The prelude contains all the types needed to use the crate. In addition, all
exported types are available through their module path for direct import.

## Data Structures

`bitvec` provides three data structures: `BitSlice`, `BitVec`, and `BitBox`.
These structures all require two type parameters: a memory type used as the
backing storage (`BitStore`), and an ordering of bits within that memory
(`BitOrder`).

### `BitSlice`

The `BitSlice` type is a specialization of the standard library’s `[]` slice
fundamental. Like `[bool]`, `BitSlice<O, T>` is a dynamically-sized type that
describes any region of contiguous memory. As a `!Sized` type, it can never be
used directly, but only held by reference: `&BitSlice<O, T>` and
`&mut BitSlice<O, T>`.

> Note that, unlike the standard library’s `[T]` type, `BitSlice<O, T>` can
> **not** be placed in any pointer types. `Box`, `Rc`, and `Arc` are all
> **incapable** of holding a `BitSlice<O, T>` region!

`BitSlice<O, T>` presents an API that behaves exactly like `[bool]`, with the
specialization that the contained data is tightly packed in memory. The only
major missing component that `[bool]` can do that `BitSlice<O, T>` cannot is
provide mutable indexing: `IndexMut` is required to produce and `&mut bool`, and
`BitSlice` is incapable of manifesting this type.

As with standard-library slices, `BitSlice<O, T>` has no restrictions on where
in memory it can begin and end. It correctly manages any sequence of contiguous
bits, starting and ending at any bit in memory.

Its maximum length is `usize::max_value() / 8`, due to implementation
constraints. This is 64 MiB on a 32-bit platform, and 256 PiB on a 64-bit
platform.

In addition to mirroring the standard library slice APIs, `BitSlice<O, T>` also
provides APIs specific to its role as a compact sequence of bits. It provides
query methods for set properties (`all`, `any`) as well as set-arithmetic
operations in the bitwise operators `&`, `|`, `^`, and `!`.

```rust
let mut raw = [0u8; 16];
let bits: BitSlice<Lsb0, u8> = BitSlice::from_slice(&raw[..]);
```

### `BitVec`

The `BitVec` type specializes the standard library’s `Vec` dynamic array. Like
`Vec<bool>`, `BitVec<O, T>` is a dynamically-resizable type that owns a buffer
of heap memory.

`BitVec<O, T>` reproduces the `Vec<bool>` API, with the same specialization
property and `IndexMut` restriction as `BitSlice<O, T>`. It has the same
relationship to `BitSlice<O, T>` as `Vec<bool>` does to `[bool]`.

```rust
let mut bv: BitVec<Local, Word> = BitVec::with_capacity(64);
```

### `BitBox`

The `BitBox` type specializes `Box<[bool]>`. It is a frozen `BitVec<O, T>`, and
has all the same relationships with `BitSlice<O, T>` that `Box<[bool]>` does
with `[bool]`.

```rust
let mut boxed: BitBox<Msb0, u64> = BitBox::from_slice(&[0, 1]);
```

## Traits

`bitvec` uses traits to compose the behavior of its data structures, and to
provide bridges between normal Rust objects and `bitvec` structures.

### `BitOrder`

This trait maps from semantic indices to bit positions in memory. It is
responsible for creating the bit-masks and shift amounts used to interact with
the backing storage of a `BitSlice`, and controls how abstract indices relate to
concrete values.

Users are free to implement this trait themselves. The trait documents the rules
it requires implementors to uphold in more detail, but the summary is:

1. a `BitOrder` implementor will never receive an index not less than the bit
   width of a storage type `T`,
1. it must never produce a position value not less than the width of that
   storage type,
1. it must provide a unique, 1:1 mapping between index values and bit positions,
1. its mapping between index and position must be pure, with no stateful or
   varying behavior, and
1. it must never produce a bitmask with zero or multiple bits set `true`.

`BitOrder` requires users to implement a function which translates index values
to position values, and provides a default function which constructs bitmasks
for positions. Users may override the mask function for speed, as long as they
uphold its 1-hot requirement.

### `BitStore`

This trait unifies the memory types used as base units of storage, and allows
users to select which they want to use. It is implemented for `u8`, `u16`, and
`u32` on all systems; it is implemented for `u64` only on 64-bit systems. It is
forbidden for users to implement, only to observe.

The type alias `Word` redirects to the local target’s `usize` equivalent: `u32`
on 32-bit systems, and `u64` on 64-bit. Implementation details prohibit `usize`
from being a storage type at this time.

### `BitField`

This is an extension trait which enables `BitSlice<O, T>` to provide load/store
behavior of values. It is currently only implemented on `BitSlice<Lsb0, T>` and
`BitSlice<Msb0, T>`, but may be extended in the future.

This trait permits a `BitSlice` over any `BitStore` type to load and store
values of any *other* `BitStore` type, at any bit width not greater than the
width of the type being stored/loaded.

This trait, to my knowledge, is the only fully generalized implementation of
C/C++ struct bitfields or Erlang bitstreams in Rust.

```rust
let bits: &mut BitSlice<Msb0, u8> = get_bitslice();
bits[3 .. 14].store::<u16>(0x1234);
assert_eq!(bits[3 .. 14].load::<u16>(), Some(0x1234));
```

### `Bits`

This trait provides conversion methods from Rust data to `BitSlice` handles. It
is implemented on `T`, `[T]`, and `[T; 0 ..= 32]` for all `BitStore` types.

```rust
let immut: u32 = 0;
let bits = immut.bits::<Lsb0>();

let mut mutable: u16 = 0;
let bits_mut = mutable.bits_mut::<Msb0>();
```

## Bit Orderings

Two implementations of `BitOrder` are provided. `Msb0` traverses a memory
element from its most significant bit monotonically down to its least, and
`Lsb0` traverses a memory element from its least significant bit monotonically
up to its most.

The type alias `Local` is provided as a default ordering. It aliases to `Lsb0`
on little-endian byte-ordered targets, and `Msb0` on big-endian byte-ordered
systems, to match the C behavior.

## Macros

When targeting a system that has an allocator, the `bitbox` and `bitvec` macros
provide construction of `BitBox<O, T>` and `BitVec<O, T>` from literals, just as
`vec!` produces `Vec<T>` objects. These macros can take `BitOrder` and
`BitStore` type names, and either a sequence of `1` and `0` or a bit and a
repetition counter.

```rust
bitbox![Msb0, u32; 1, 0, 1, 0];
bitvec![0; 64];
```

# Feature Flags

`bitvec` uses feature flags to control the presence or absence of crate-global
behaviors. The uncommented features below (`alloc`, `atomic`, `std`) are
provided by default and require explicit opt-out; the commented features
(`serde`) require explicit opt-in.

```toml
# Cargo.toml

[dependencies.bitvec]
version = "0.17"
default-features = false
features = [
  "alloc",
  "atomic",
  # "serde",
  "std",
]
```

## `alloc`

The `BitBox` and `BitVec` types require the distribution’s `alloc` crate in
order to allocate their memory. If users are writing for a target that does not
have a dynamic allocator, they may disable this feature to remove those types
and only retain the `BitSlice` region type.

Users targeting an environment that has an allocator, but does not have a
standard library, may reënable this feature.

## `atomic`

`BitSlice` requires safe shared mutability in order to correctly handle the case
of multiple `&/mut BitSlice` handles covering the same memory element. As it is
undefined behavior to ever produced aliased references to a mutating location,
`bitvec` must route access through either the [`core::sync::atomic`] module or
the [`core::cell::Cell<T>`] type.

The `atomic` feature permits `BitSlice` to implement `Send` and `Sync` so that
slice handles may be dispatched across threads for parallelization. Disabling
this feature causes the shared-mutability logic to fall back to `Cell`, which is
not thread-safe, and removes those markers.

`BitBox` and `BitVec` are theoretically thread-safe regardless of this feature,
as the borrow checker’s rules combine with the allocator regime to forbid
shared-mutation faults with these types. However, as a conservative rule and to
maintain consistency, these types also remove their thread-safety markers when
`atomic` is disabled.

## `serde`

Enables support for Serde de/serialization.

`BitSlice` implements `Serialize` but not `Deserialize`, as it cannot allocate
and `serde` does not permit deserializing into preällocated memory.

`BitBox` and `BitVec` implement both `Serialize` and `Deserialize`.

These implementations de/serialize the memory behind a handle into some
protocol. No implementations are provided to de/serialize other types against a
`BitSlice` or `BitVec`. If you need to read typed data out of a `BitSlice`, or
write it into a `BitVec`, you will need to do this yourself. The `BitField`
trait may be of help for this purpose.

## `std`

Links against the standard library.

Currently, this feature does not enable anything not already covered by `alloc`.
This will be removed before the `1.0` release unless `std`-only functionality is
added.

# Warnings

The `BitSlice` type causes memory aliasing. Consider this example:

```rust
let mut data = 0u8;
let bits = data.bits_mut::<Local>();
let (l, r) = bits.split_at_mut(4);
```

The `l` and `r` slices both refer to the `data` element, and both may mutate it.
The implementation of `BitSlice`’s mutating functions, combined with the
`atomic` feature flag, ensure that the crate will never cause undefined
behavior, lost writes, or writes out of bounds. The `BitOrder` implementation in
use must uphold the trait requirements in order to ensure that this behavior is
correct.

The `atomic` feature prevents cross-thread race conditions by making all read
or write access to the memory atomic. When it is disabled, `BitSlice` loses its
ability to cross between threads.

# Planned Features

Contributions of items in this list are *absolutely* welcome! Contributions of
other work are also welcome, but I reserve the right to not merge them into the
crate.

- Creation of specialized pointers corresponding to `Rc<BitSlice>` and
  `Arc<BitSlice>`
- Procedural macros for `bitvec!` and `bitbox!`
- An FFI module, and bindings for other languages

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

<!-- References -->
[`core::cell::Cell<T>`]: https://doc.rust-lang.org/std/cell/struct.Cell.html
[`core::sync::atomic`]: https://doc.rust-lang.org/std/sync/atomic/index.html

<!-- Sections -->
[`BitBox`]: #bitbox
[`BitField`]: #bitfield
[`BitOrder`]: #bitorder
[`BitSlice`]: #bitslice
[`BitStore`]: #bitstore
[`BitVec`]: #bitvec
[`Bits`]: #bits
[`Lsb0`]: #bit-orderings
[`Local`]: #bit-orderings
[`Msb0`]: #bit-orderings
[`Word`]: #bitstore
[`bitbox!`]: #macros
[`bitvec!`]: #macros
