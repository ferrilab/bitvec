# `BitVec` – Managing memory bit by bit

[![Crate][crate_img]][crate]
[![Documentation][docs_img]][docs]
[![License][license_img]][license_file]
[![Continuous Integration][travis_img]][travis]
[![Code Coverage][codecov_img]][codecov]
[![Crate Downloads][downloads_img]][crate]
[![Crate Size][loc_img]][loc]

## Summary

This crate provides data structures which allow working with `bool` as if it
were truly one bit wide in memory, rather than a `u8` with only two valid
values. Currently, it only provides `[u1]`, `Box<[u1]>`, and `Vec<u1>`
structures.

In addition to compact memory representation, this crate also allows you to
specify the order in which individual bits are stored in Rust fundamentals, and
which fundamental element (`u8`, `u16`, `u32`, and on 64-bit systems, `u64`) is
used to store the bits.

The data structures provided by this crate track as closely as possible the APIs
and trait implementations of their proper types in the Rust standard library.
`BitSlice` corresponds to `[bool]`, `BitBox` to `Box<[bool]>`, and `BitVec` to
`Vec<bool>`, and each of these types should be drop-in compatible replacements
for their standard library counterparts.

## What Makes `bitvec` Different Than All The Other Bit Vector Crates

The most significant differences are that `bitvec` provides arbitrary bit
ordering through the `Cursor` trait, and provides a full-featured slice type.
Other crates have fixed orderings, and are often unable to produce slices that
begin at any arbitrary bit.

Additionally, the `bitvec` types implement the full extent of the standard
library APIs possible, in both inherent methods and trait implementations.

The `bitvec` types’ handles are exactly the size of their standard library
counterparts, while the other crates carry bit index information in separate
fields, making their handles wider. Depending on your needs, this may sway your
opinion in either direction. `bitvec` is more compact, but mangles the internal
pointer representation and requires more complex logic to use the bit region,
while other crates’ types are larger, but have more straightforward internal
logic.

## Why Would You Use This

- You need to directly control a bitstream’s representation in memory.
- You need to do unpleasant things with communications protocols.
- You need a list of `bool`s that doesn’t waste 7 bits for every bit used.
- You need to do set arithmetic, or numeric arithmetic, on those lists.
- You are running a find/replace command on your repository from `&[bool]` to
  `&BitSlice`, or `Vec<bool>` to `BitVec`, and expect minimal damage as a
  result.

## Why *Wouldn’t* You Use This

Your concern with the memory representation of bitsets includes compression.
`BitSlice` performs absolutely no compression, and maps bits directly into
memory. Compressed bit sets can be found in other crates, such as the
[`compacts`] crate, which uses the [Roaring BitSet] format.

## Usage

**Minimum Rust Version**: `1.34.0`

I wrote this crate because I was unhappy with the other bit-vector crates
available. I specifically need to manage raw memory in bit-level precision, and
this is not a behavior pattern the other bit-vector crates made easily available
to me. This served as the guiding star for my development process on this crate,
and remains the crate’s primary goal.

To this end, the default type parameters for the `BitVec` type use `u8` as the
storage primitive and use big-endian ordering of bits: the forwards direction is
from MSb to LSb, and the backwards direction is from LSb to MSb.

To use this crate, you need to depend on it in `Cargo.toml`:

```toml
[dependencies]
bitvec = "0.12"
```

and include it in your crate root `src/main.rs` or `src/lib.rs`:

```rust,ignore
//  Only if you’re in Rust 2015
#[macro_use]
extern crate bitvec;

use bitvec::prelude::*;
```

This imports the following symbols:

- `bitvec!` – a macro similar to `vec!`, which allows the creation of `BitVec`s
  of any desired cursor, storage type, and contents. The documentation page has
  a detailed explanation of its syntax.

- `BitSlice<C: Cursor, T: BitStore>` – the actual bit-slice reference type. It is
  generic over a cursor type (`C`) and storage type (`T`). Note that `BitSlice`
  is unsized, and can never be held directly; it must always be behind a
  reference such as `&BitSlice` or `&mut BitSlice`.

  Furthermore, it is *impossible* to put `BitSlice` into any kind of intelligent
  pointer such as a `Box` or `Rc`! Any work that involves managing the memory
  behind a bitwise type *must* go through `BitBox` or `BitVec` instead. This may
  change in the future as I learn how to better manage this library, but for now
  this limitation stands.

- `BitBox<C: Cursor, T: BitStore>` – a fixed-size bit collection in owned memory.

- `BitVec<C: Cursor, T: BitStore>` – the actual bit-vector structure type. It is
  generic over a cursor type (`C`) and storage type (`T`). This type is the main
  worker of the crate. It supports the full `Vec<T>` API and trait
  implementations, with the exception that (at this time) it is impossible to
  take a mutable reference to a single bit. This means that everything except
  for `let elt: &mut bool = &mut bv[index];` and `bv[index] = some_bool();` is
  possible to express.

- `Cursor` – an open trait that defines an ordering schema for `BitVec` to use.
  Little and big endian orderings are provided by default. If you wish to
  implement other ordering types, the `Cursor` trait requires one function:

  - `fn at<T: BitStore>(index: u8) -> u8` takes a semantic index and computes a bit
    offset into the primitive `T` for it.

- `BigEndian` – a marker type that implements `Cursor` by defining the forward
  direction as towards LSb and the backward direction as towards MSb.

- `LittleEndian` – a marker type that implements `Cursor` by defining the
  forward direction as towards MSb and the backward direction as towards LSb.

- `BitStore` – a sealed trait that provides generic access to the four Rust
  primitives usable as storage types: `u8`, `u16`, `u32`, and `u64`. `usize`
  and the signed integers do *not* implement `BitStore` and cannot be used as the
  storage type. `u128` also does not implement `BitStore`, as I am not confident in
  its memory representation.

`BitVec` has the same API as `Vec`, and should be easy to use.

The `bitvec!` macro can take type information in its first two arguments.
Because macros do not have access to the type checker, it currently only accepts
the literal tokens `BigEndian` or `LittleEndian` as the first argument, one of
the four unsigned integer primitives as the second argument, and then as many
values as you wish to insert into the collection. It accepts any integer value,
and maps them to bits by comparing against 0. `0` becomes `false` and any other
integer, whether it is odd or not, becomes `true`. While the syntax is loose,
you should only use `0` and `1` to fill the macro, for readability and lack of
surprise.

### `no_std`

This crate can be used in `#![no_std]` libraries, by disabling the default
feature set. In your `Cargo.toml`, write:

```toml
[dependencies]
bitvec = { version = "0.12", default-features = false }
```

or

```toml
[dependencies.bitvec]
version = "0.12"
default-features = false
```

This turns off the standard library imports *and* all usage of dynamic memory
allocation. Without an allocator, the `bitvec!` and `bitbox!` macros, and the
`BitVec` and `BitBox` types, are all disabled and removed from the library,
leaving only the `BitSlice` type.

To use `bitvec` in a `#![no_std]` environment that *does* have an allocator,
re-enable the `alloc` feature, like so:

```toml
[dependencies.bitvec]
version = "0.12"
default-features = false
features = ["alloc"]
```

The `alloc` feature restores the owned-memory types and their macros. The only
difference between `alloc` and `std` is the presence of the standard library
façade and runtime support.

The `std` feature includes allocation, so using this crate without any feature
flags *or* by explicitly enabling the `std` feature will enable full
functionality.

### Serde Support

The `serde` feature, by default, enables serialization for the `BitSlice` type.
Enabling the `alloc` or `std` features enables both serialization and
deserialization for the `BitBox` and `BitVec` types.

The `serde` feature is opt-in, and requires setting it in your `Cargo.toml`:

```toml
# Cargo.toml

[dependencies.bitvec]
version = "0.12"
features = [
  "serde", # enables serialization
  "std", # enables deserialization
]
```

## Example

```rust
extern crate bitvec;

use bitvec::prelude::*;

use std::iter::repeat;

fn main() {
    let mut bv = bitvec![BigEndian, u8; 0, 1, 0, 1];
    bv.reserve(8);
    bv.extend(repeat(false).take(4).chain(repeat(true).take(4)));

    //  Memory access
    assert_eq!(bv.as_slice(), &[0b0101_0000, 0b1111_0000]);
    //                   index 0 -^               ^- index 11
    assert_eq!(bv.len(), 12);
    assert!(bv.capacity() >= 16);

    //  Stack operations
    bv.push(true);
    bv.push(false);
    bv.push(true);

    assert!(bv[12]);
    assert!(!bv[13]);
    assert!(bv[14]);
    assert!(bv.get(15).is_none());

    bv.pop();
    bv.pop();
    bv.pop();

    //  Set operations
    bv &= repeat(true);
    bv = bv | repeat(false);
    bv ^= repeat(true);
    bv = !bv;

    //  Arithmetic operations
    let one = bitvec![1];
    bv += one.clone();
    assert_eq!(bv.as_slice(), &[0b0101_0001, 0b0000_0000]);
    bv -= one.clone();
    assert_eq!(bv.as_slice(), &[0b0101_0000, 0b1111_0000]);

    //  Borrowing iteration
    let mut iter = bv.iter();
    //  index 0
    assert_eq!(iter.next().unwrap(), false);
    //  index 11
    assert_eq!(iter.next_back().unwrap(), true);
    assert_eq!(iter.len(), 10);
}
```

Immutable and mutable access to the underlying memory is provided by the `AsRef`
and `AsMut` implementations, so the `BitVec` can be readily passed to transport
functions.

`BitVec` implements `Borrow` down to `BitSlice`, and `BitSlice` implements
`ToOwned` up to `BitVec`, so they can be used in a `Cow` or wherever this API
is desired. Any case where a `Vec`/`[T]` pair cannot be replaced with a
`BitVec`/`BitSlice` pair is a bug in this library, and a bug report is
appropriate.

`BitVec` can relinquish its owned memory with `.into_vec()` or
`.into_boxed_slice()`, and `BitSlice` can relinquish its borrow by going out
of scope.

## Warnings

The `BitSlice` type is able to cause memory aliasing, as multiple independent
`&mut BitSlice` instances may use the same underlying memory. This crate takes
care to ensure that all observed behavior is exactly as expected, without any
side effects.

The `BitSlice` methods only use whole-element instructions when the slice spans
the full width of the element; when the slice has only partial use, the methods
crawl each bit individually. This is slower on most architectures, but
guarantees safety.

Race conditions are avoided through use of the atomic read/modify/write
instructions stabilized in `1.34.0`.

## Planned Features

Contributions of items in this list are *absolutely* welcome! Contributions of
other features are also welcome, but I’ll have to be sold on them.

- Creation of specialized pointers `Rc<BitSlice>` and `Arc<BitSlice>`.
- Procedural macros for `bitvec!` and `bitbox!`
- An FFI module, and bindings from other languages.

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
[loc_img]: https://tokei.rs/b1/github/myrrlyn/bitvec "Repository Size"
[travis]: https://travis-ci.org/myrrlyn/bitvec "Travis CI"
[travis_img]: https://img.shields.io/travis/myrrlyn/bitvec.svg?logo=travis "Travis CI Display"
[`compacts`]: https://crates.io/crates/compacts
[Roaring BitSet]: https://arxiv.org/pdf/1603.06549.pdf
