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
precise, user-controlled, in-memory layout of data fields.

# Table of Contents <!-- omit in toc -->

1. [Introduction](#introduction)
   1. [Capabilities](#capabilities)
   1. [Limitations](#limitations)
1. [Usage](#usage)
   1. [Example Use](#example-use)
1. [Feature Flags](#feature-flags)
   1. [`alloc` Feature](#alloc-feature)
   1. [`atomic` Feature](#atomic-feature)
   1. [`serde` Feature](#serde-feature)
   1. [`std` Feature](#std-feature)
1. [API Reference](#api-reference)
   1. [Implementation Details](#implementation-details)
1. [Alias Warning](#alias-warning)

# Introduction

Computers operate on memory in bytes and registers which do not easily permit
partial use. Data that does not use every bit in a byte or wider register thus
wastes those bits by default, rather than drifting across boundaries. This is
acceptable as a default condition, but circumstances can require removing wasted
bits from the electrical representation of data; massive data-sets and network
transmission are two common examples.

`bitvec` creates views of memory that address each bit individually, rather than
resolving only to a byte or register. These views are parametric over the memory
or processor register used to hold a collection of bits, and the order of
traversal within the register’s bits.

## Capabilities

`bitvec` implements the C and Erlang `struct`ural [bitfield] behavior and C++
[`std::bitset<N>`] collection behavior on the referent type [`BitSlice`]. By
taking a pointer to [`BitSlice`], users gain both one-bit-`bool` collections and
arbitrary-bit integer fields. [`BitSlice`] regions can be managed by Rust
references (`&BitSlice` and `&mut BitSlice`) or by owning handles ([`BitBox`]
and [`BitVec`]).

All [`BitSlice`]-based types take two type parameters: an ordering of bits
within a register type, and a register type. This allows users to specify
exactly the memory layout they want. As an example, `bitvec` can be used to
describe an IPv4 packet by setting the type alias
`type Ipv4 = BitSlice<Msb0, u8>;` Indexing within a `BitSlice<Msb0, u8>`
proceeds according to the sequencing that the user would expect: the range
`[0 .. 4]` holds the IPv4 version field, in the high nibble of the first byte,
just as the specification says.

`bitvec` provides two orderings, [`Lsb0`] and [`Msb0`], and leaves the trait
[`BitOrder`] open for depending crates to supply their own. It permits any
unsigned integer type narrower than a processor word to be used as the register
type parameter, and seals the [`BitStore`] trait to forbid external
implementations.

Additionally, `bitvec` uses a custom pointer encoding, enabling it to store
information in reference values, rather than in referent regions. This allows
`&BitSlice` references to be used in type signatures, and to provide the same
slicing behaviors seen in the standard library.

## Limitations

The nature of the pointer encoding used means that region operations on
[`BitSlice`] take more instructions, and are thus slower, than equivalent
operations on ordinary slices. In addition, [`BitSlice`] does not compose with
ordinary Rust pointer types, so it cannot be used as the referent parameter of
`Box`, `Rc`, etc. types.

# Usage

**Minimum Supported Rust Version:** `1.44.0`

The MSRV will only be raised when the language or standard library has changes
that significantly alter the development or API surface of the library. Once
`bitvec` reaches 1.0, it will track the standard library APIs and raise the MSRV
as needed in minor releases. `bitvec` will not feature-gate APIs from newer
versions of the standard library to lower the MSRV for a given release.

To use `bitvec`, depend on it in your Cargo manifest:

```toml
# Cargo.toml

[dependencies]
bitvec = "0.18"
```

and import its prelude into your modules that use it:

```rust
//  src/lib.rs

use bitvec::prelude::*;
```

The prelude brings in the `struct`s, `trait`s, and macros required to use the
crate. Almost all names begin with `Bit` or `bit`, and so are unlikely to
collide with any other symbols. If you have a name collision, or want more
control over what is in scope, consider importing the prelude module with

```rust
//  src/lib.rs

use bitvec::prelude as bv;
```

You can read the [prelude reëxports][prelude] to learn what symbols you need,
and import them directly rather than using a glob import.

## Example Use

This snippet provides a whirlwind tour of the library. You can see more
[examples] in the repository, which showcase more specific user stories.

```rust
use bitvec::prelude::*;

use std::iter::repeat;

fn main() {
  // You can build a static array,
  let arr = bitarr![Lsb0, u32; 0; 64];
  // a hidden static slice,
  let slice = bits![Local, u8; 0; 10];
  // or a boxed slice,
  let boxed = bitbox![0; 20];
  // or a vector, using macros that extend the `vec!` syntax
  let mut bv = bitvec![Msb0, u16; 0, 1, 0, 1];

  // `BitVec` implements the entire `Vec` API
  bv.reserve(8);

  // Like `Vec<bool>`, it can be extended by any iterator of `bool`
  bv.extend([false; 4]);
  bv.extend([true; 4]);

  // `BitSlice`-owning buffers can be viewed as their raw memory
  assert_eq!(
    bv.as_slice(),
    &[0b0101_0000, 0b1111_0000],
    //  ^ index 0       ^ index 11
  );
  assert_eq!(bv.len(), 12);
  assert!(bv.capacity() >= 16);

  bv.push(false);
  bv.push(true);
  bv.push(false);

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

  // range indexing produces subslices
  let last = &bv[12 ..];
  assert_eq!(last.len(), 3);
  assert!(last.any());

  for _ in 0 .. 3 {
    bv.pop();
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
version = "0.18"
features = [
  "alloc",
  "atomic",
  # "serde",
  "std",
  # "unstable",
]
```

You can disable the three uncommented features by using
`default-features = false`, and then reënable the ones you need specifically.

## `alloc` Feature

This feature links `bitvec` against the distribution-provided `alloc` crate, if
your target has one, and enables the [`BitBox`] and [`BitVec`] types. This
feature is a dependency of `std`, and will always be present when building for
targets that have `std`. If you are building for a `#![no_std]` target, you will
need to disable the `std` default feature, and may choose to reënable the
`alloc` feature if your target has an `alloc` library and an allocator.

## `atomic` Feature

This feature is only necessary if your target has some form of concurrent
multiprocessing, usually threads, and you intend to operate concurrently on
[`BitSlice`]s. It is a default feature so that `std` targets can parallelize
[`BitSlice`] operations; when disabled, it removes the `Send` and `Sync` markers
on some [`BitSlice`]s.

> Note: see the documentation on [`BitSlice::split_at_mut`] and the [`domain`]
> module for more information on how `bitvec` detects alias conditions and
> manages thread safety.

This is a default feature so that splitting a [`BitSlice`] still results in
concurrency-safe behavior. If your target does not have atomics, you will need
to disable it. At present, the standard library does not permit crates to select
*some* atomic integers; either all integers have atomic support in `bitvec`, or
none do.

## `serde` Feature

When enabled, [`BitSlice`] implements `serde::Serialize` and the owning buffers
present implement `serde::Deserialize`. This feature allows you to transport
bit collections through I/O protocols. This behavior is **very** different than
using `bitvec` to manage a buffer containing an I/O protocol message! You may
choose to implement a `serde::Serializer`/`serde::Deserializer` protocol using
`bitvec` to control layout of your packets, but the `De`/`Serialize`
implementations provided do not do this work. They only write a collection into
an already-existing transport protocol, and are not required to maintain layout
representation guarantees.

In particular, neither the bit ordering nor the element type are represented in
the serialized form, so there is no means of ensuring that the deserializer is
using the same parameter set as the serializer was.

## `std` Feature

This feature links `bitvec` against the distribution-provide `std` crate, if
your target has one. The only additional features it provides that are not
present in `alloc` are implementations of `io::Read` and `io::Write` on data
structures that have [`BitField`] trait implementations.

# API Reference

The complete API reference can be found on [docs.rs], and will not be duplicated
here. As a summary:

The [`BitSlice`] type describes a region of memory viewed in bit-addressed
precision. It is parameterized by two types, a [`BitOrder`] translation of
indices to positions within a register type, and a [`BitStore`] register type.
It is a region type, and cannot be held as an immediate. It must be held by
reference, `&BitSlice<O, T>` or `&mut BitSlice<O, T>`, or through one of the
pointer types provided by `bitvec`. It cannot, ever, be used as a type parameter
in pointers not provided by this crate.

The [`BitBox`] and [`BitVec`] types are heap-allocated owning buffers,
corresponding to `Box<[bool]>` and `Vec<bool>`, respectively. They defer to
[`BitSlice`] for most data manipulation.

The [`BitArray`] type is a rough equivalent to `[bool; N]`. The Rust
const-generic language implementation is not yet sufficient to correctly port
the C++ `std::bitset<N>`, so this type is instead parameterized over an array of
[`BitStore`] elements, rather than over a number of bits. Hopefully, Rust
const-generics will improve to support the C++-esque parameterization over bit
count.

Each data type has a constructor [macro]: [`bits!`] for [`BitSlice`],
[`bitarr!`] for [`BitArray`], [`bitbox!`] for [`BitBox`], and [`bitvec!`] for
[`BitVec`]. These macros implement a superset of the `vec!` argument grammar,
and allow for the compile-time construction of [`BitSlice`] buffers. [`bitbox!`]
and [`bitvec!`] copy their buffer into a heap allocation at runtime.

The [`BitField`] trait describes how a [`BitSlice`] can be used for value
storage. It is implemented for `BitSlice<Lsb0, _>` and `BitSlice<Msb0, _>`,
enabling those slices to act as memory stores for any unsigned integral value.

The [`BitOrder`] trait provides translations from semantic indices that appear
in user code to the actual shift-and-mask instructions used to operate on
memory. As this trait has very strict requirements for implementations that
cannot (yet) be made into compiler errors, it is marked `unsafe`.
Implementations other than the provided [`Lsb0`] and [`Msb0`] are permitted, but
will have niche applicability and, likely, reduced performance.

The [`BitStore`] trait describes memory cells, and their behavior in CPU
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

In addition to the API surface for general use, `bitvec` exposes APIs that are
useful for developing the crate itself or extensions to it.

The `devel` module contains snippets of type manipulation or value checking used
in the crate internals. These functions are not part of the public API, but are
pieces of logic that occur often enough in crate internals to be worth naming.

The `index` module contains typed indices into register elements. Implementors
of the `BitOrder` trait operate on the types here in order to plug into the rest
of the crate systems.

The `mem` module contains logic for operating on register elements. It is an
implementation detail of the memory modeling system.

The `pointer` module implements the pointer encoding used to drive the
`&BitSlice` reference type. It is explicitly not exposed outside the crate, and
is not planned to be stabilized as an external interface.

# Alias Warning

This library introduces managed memory-alias conditions when performing subslice
partitions. Under the `atomic` feature, aliasing events switch to using atomic
accesses to the affected memory; when it is disabled, the affected slices become
unable to move across threads. You should not be able to introduce race unsafety
in your program through subslice partitions. If you do, this is an error in the
library.

Consider this example:

```rust
use bitvec::prelude::*;

let mut data = 0u8;
let bits = data.view_bits_mut::<Local>();
let (l, r) = bits.split_at_mut(4);
```

The `l` and `r` subslices both refer to the `data` element, and are capable of
effecting writes to it. They use the `AtomicU8` type parameter under
`feature = "atomic"`, and `Cell<u8>` otherwise. The changes to memory types can
cause performance effects (by removing thread-safety or inducing unneeded atomic
accesses), which can be mitigated by using the `.bit_domain{,_mut}()` methods to
further partition the aliased and unaliased regions.

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

<!-- External References -->
[`AsBits<T>`]: https://docs.rs/bitvec/latest/bitvec/view/trait.AsBits.html "AsBits API reference"
[`AsBitsMut<T>`]: https://docs.rs/bitvec/latest/bitvec/view/trait.AsBitsMut.html "AsBitsMut API reference"
[`BitArray`]: https://docs.rs/bitvec/latest/bitvec/array/struct.BitArray.html "BitArray API reference"
[`BitBox`]: https://docs.rs/bitvec/latest/bitvec/boxed/struct.BitBox.html "BitBox API reference"
[`BitField`]: https://docs.rs/bitvec/latest/bitvec/fields/trait.BitField.html "BitField API reference"
[`BitOrder`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html "BitOrder API reference"
[`BitSlice`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html "BitSlice API reference"
[`BitSlice::split_at_mut`]: https://docs.rs/bitvec/latest/bitvec/slice/struct.BitSlice.html#method.split_at_mut "BitSlice::split_at_mut API reference"
[`BitStore`]: https://docs.rs/bitvec/latest/bitvec/store/trait.BitStore.html "BitStore API reference"
[`BitVec`]: https://docs.rs/bitvec/latest/bitvec/vec/struct.BitVec.html "BitVec API reference"
[`BitView`]: https://docs.rs/bitvec/latest/bitvec/view/trait.BitView.html "BitView API reference"
[`Lsb0`]: https://docs.rs/bitvec/latest/bitvec/order/struct.Lsb0.html "Lsb0 API reference"
[`Msb0`]: https://docs.rs/bitvec/latest/bitvec/order/struct.Msb0.html "Msb0 API reference"
[`bitarr!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitarr.html "bitarr! API reference"
[`bitbox!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitbox.html "bitbox! API reference"
[`bits!`]: https://docs.rs/bitvec/latest/bitvec/macro.bits.html "bits! API reference"
[`bitvec!`]: https://docs.rs/bitvec/latest/bitvec/macro.bitvec.html "bitvec! API reference"
[`domain`]: https://docs.rs/bitvec/latest/bitvec/domain "Domain module API reference"
[`std::bitset<N>`]: https://en.cppreference.com/w/cpp/utility/bitset
[bitfield]: https://en.cppreference.com/w/cpp/language/bit_field "C++ bitfields"
[docs.rs]: https://docs.rs/bitvec/latest/bitvec "crate API reference"
[examples]: https://github.com/myrrlyn/bitvec/blob/HEAD/examples
[macro]: https://docs.rs/bitvec/latest/bitvec/#macros
[prelude]: https://docs.rs/bitvec/latest/bitvec/prelude
