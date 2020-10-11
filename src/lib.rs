/*! # Addressable Bits

`bitvec` is a foundation library for memory compaction techniques that rely on
viewing memory as bit-addressed rather than byte-addressed.

The `bitvec` project is designed to provide a comprehensive set of tools for
users who need memory compaction with as low a cost as possible.

# Examples

The [`examples/`] directory of the project repository contains some sample
programs that demonstrate how the library can be used in real programs, and each
data structure’s type documentation contains more focused references.

To begin using the library, you need only import its prelude. Once in scope,
`bitvec` can take over existing memory buffers or create entirely new values:

```rust
# #[cfg(feature = "alloc")] {
use bitvec::prelude::*;

let data = &[0u8, 1, 2, 3];
let data_bits = data.view_bits::<Msb0>();

let literal_bits = bits![Msb0, u8; 1, 0, 1, 1];
assert_eq!(literal_bits.as_slice()[0], 0b1011_0000u8);

let array_bool = bitarr![1; 40];
let vec_bool = bitvec![1; 100];
# }
```

The two easiest entry points into `bitvec` are through the [`BitView`] trait,
which borrows existing memory as a [`BitSlice`] reference, and the
[macro constructors], which convert literal patterns into appropriate buffers
at compile time. Each data structure also has its own constructor functions that
create new buffers or borrow existing memory.

Once in use, `bitvec`’s types obepy all the same patterns and APIs that you have
come to expect from their analogues in the [`core`], [`alloc`] and [`std`]
libraries.

# Usage

`bitvec` provides data structures that specialize the major sequence types in
the standard libraries:

- `[bool]` becomes [`BitSlice`]
- `[bool; N]` becomes [`BitArray`]
- `Box<[bool]>` becomes [`BitBox`]
- `Vec<bool>` becomes [`BitVec`]

You can start using the crate in an existing codebase by replacing types and
chasing compiler errors from there.

As an example,

```rust
# #[cfg(feature = "alloc")] {
let mut io_buf: Vec<u8> = Vec::new();
io_buf.extend(&[0x47, 0xA5]);

let stats: Vec<bool> = vec![
  true, false, true, true,
  false, false, true, false,
];
# }
```

would become

```rust
# #[cfg(feature = "alloc")] {
use bitvec::prelude::*;

let mut io_buf: BitVec<Msb0, u8> = BitVec::new();
io_buf.resize(16, false);
io_buf[.. 4].store(4u8);
io_buf[4 .. 8].store(7u8);
io_buf[8 .. 16].store(0xA5u8);

let stats: BitVec = bitvec![
  1, 0, 1, 1,
  0, 0, 1, 0,
];
# }
```

## Use of Type Arguments

The `bitvec` data structures are all generic over two type parameters that
control how they view and manage the memory they use. These type parameters
allow users to precisely control the memory value patterns and generated
instructions, but most users of the library will not need to be generic over
them. Instead, you probably either do not care about the details of the
underlying memory, or you have a specific and fixed requirement for memory
layout. In either case, you will likely select a specific combination of type
arguments and use it consistently throughout your project.

The default type arguments are chosen for optimal behavior in memory use and
instruction selection. The unadorned types [`BitArray`], [`BitSlice`],
[`BitBox`], and [`BitVec`] can all be used in type-annotation position (`let`
bindings, `struct` fields, and function arguments). Users who need to specify
their type arguments should prefer to do so in a `type` alias, and use that
alias throughout their project instead of the much longer fully-qualified
`bitvec` type names:

```rust
use bitvec::prelude::*;

pub type MySlice = BitSlice<Msb0, u8>;
pub type MyArray20 = bitarr![for 20, in Msb0, u8];
# #[cfg(feature = "alloc")]
pub type MyVec = BitVec<Msb0, u8>;
```

In general, you will probably work with [`BitSlice`] borrows and [`BitVec`]
owned buffers; the [`BitArray`] and [`BitBox`] types are provided for
completeness, but their frozen size renders them less commonly useful.

## Additional Details

As a replacement for `bool` sequences, you should be able to replace old type
definition and value construction sites with their corresponding items from this
project, and the rest of your project should just work with the new types.

To use `bitvec` for structural bitfields or specialized I/O protocol buffers,
you should use [`BitArray`] or [`BitVec`] to manage your data buffers (for
compile-time statically sized and run-time dynamically sized, respectively), and
the [`BitField`] trait to manage transferring values into and out of them.

The [`BitSlice`] type contains most of the behavior that interacts with the
*contents* of a memory buffer. [`BitVec`] adds behavior that operates on
allocations, and specializes [`BitSlice`] behaviors that can take advantage of
owned buffers.

The [`domain`] module, whose types are accessed by the `.{bit_,}domain{,_mut}`
methods on [`BitSlice`], allows users to split their views of memory at aliasing
boundaries, thereby removing synchronization guards where it is provably safe to
do so.

There are many ways to construct a bit-level view of data. The [`BitArray`],
[`BitBox`], and [`BitVec`] types are all owning types that contain a buffer of
memory and dereference to [`BitSlice`] in order to view it. In addition, you can
borrow any piece of ordinary Rust memory as a `BitSlice` view using its
borrowing constructor functions or the [`BitView`] trait methods.

# Capabilities

`bitvec` stands out from other bit-sequence libraries, both in Rust and in other
languages, in a few significant ways.

Unlike other Rust libraries, `bitvec` stores its region information in
specially-encoded pointers *to* memory regions, rather than in the region
itself. By using its own pointer encoding scheme, `bitvec` can use references
(`&BitSlice<_, _>` and `&mut BitSlice<_, _>`) to manage memory accesses and fit
seamlessly into the Rust language rules and API signatures.

Unlike *any* other bit-sequence system, `bitvec` enables users to specify both
the register element type used to store data and also the ordering of bits
within each register element. This sidesteps the problems found in C
[bitfields], C++ [`std::bitset`], Python [`bitstring`], Erlang [`bitstream`],
and other Rust libraries such as [`bit-vec`].

By permitting the in-memory layout to be specified by the user, rather than
hard-coding it within the library, users are able to select the behavior
characteristics they want or need without significant effort on their part.

This works by supplying two type parameters: an `O` [`BitOrder`] ordering of
bits within a register element, and a `T` [`BitStore`] register element used for
storage and memory description. `T` is restricted to be only the raw unsigned
integers, and [`Cell`] and [`Atomic`] variants of them, that fit within
processor registers on your target.

These parameters permit the `bitvec` type system to track memory access rules
and bit addressing, thus enabling a nearly seamless use of [`BitSlice`]s as if
they were ordinary Rust slices.

`bitvec` correctly handles memory aliasing by leveraging the type system to mark
regions that have become subject to concurrency and either require the use of
atomic memory accesses or forbid simultaneous multiprocessing. You will never
need to insert your own guards to prevent race conditions, and [`BitSlice`]
provides APIs to separate any slice into its aliased and unaliased sub-regions.

Where possible, `bitvec` uses its knowledge of bit addressing and memory usage
to accelerate memory accesses from individual, sequential, bit accesses by using
processor registers to operate in larger batches. This is an area of ongoing
development, and is an implementation detail rather than an aspect of public
API.

`bitvec`’s performance even when working with individual bits is as close to
ideal as a general-purpose library can be, but the width of processor registers
means that no amount of performance improvement at the individual bit level can
compete with instructions operating on 32 or 64 bits at once. If you encounter
performance bottlenecks, you can escape `bitvec`’s views to operate on memory
directly, or submit an issue for future work on specialized batch
parallelization.

# Library Structure

You should generally import the library [prelude], with

```rust
use bitvec::prelude::*;
```

The prelude contains all the symbols you will need to make use of the crate.
Almost all symbols begin with the prefix `Bit`; only the orderings [`Lsb0`],
[`Msb0`], and [`LocalBits`] do not. This will reduce the likelihood of name
collisions.

Each major component in the library is divided into its own module. This
includes each data structure and trait, as well as utility objects used for
implementation. The data structures that mirror the language distribution have
submodules for each part of their mirroring: `api` ports inherent methods,
`iter` contains iteration logic, `ops` overrides operator sigils, and `traits`
holds all other trait implementations. The data structure’s own module typically
only contains its own definition and its inherent methods that are not ports of
the standard libraries.

[`Atomic`]: core::sync::atomic
[`BitArray`]: crate::array::BitArray
[`BitBox`]: crate::boxed::BitBox
[`BitField`]: crate::field::BitField
[`BitOrder`]: crate::order::BitOrder
[`BitSlice`]: crate::slice::BitSlice
[`BitStore`]: crate::store::BitStore
[`BitVec`]: crate::vec::BitVec
[`BitView`]: crate::view::BitView
[`Cell`]: core::cell::Cell
[`LocalBits`]: crate::order::LocalBits
[`Lsb0`]: crate::order::Lsb0
[`Msb0`]: crate::order::Msb0

[`alloc`]: https://doc.rust-lang.org/stable/alloc
[`bitstream`]: https://erlang.org/doc/programming_examples/bit_syntax.html
[`bitstring`]: https://pypi.org/project/bitstring/
[`bit-vec`]: https://crates.io/crates/bit-vec
[`core`]: https://doc.rust-lang.org/stable/core
[`domain`]: crate::domain
[`examples/`]: https://github.com/myrrlyn/bitvec/tree/HEAD/examples
[`std`]: https://doc.rust-lang.org/stable/std
[`std::bitset`]: https://en.cppreference.com/w/cpp/utility/bitset

[bitfields]: https://en.cppreference.com/w/c/language/bit_field
[macro constructors]: #macros
[prelude]: crate::prelude
!*/

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(debug_assertions, warn(missing_docs))]
#![cfg_attr(not(debug_assertions), deny(missing_docs))]
#![deny(unconditional_recursion)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[macro_use]
pub mod macros;

pub mod access;
pub mod array;
pub mod domain;
pub mod field;
pub mod index;
pub mod mem;
pub mod order;
pub mod prelude;
pub mod ptr;
pub mod slice;
pub mod store;
pub mod view;

#[cfg(feature = "alloc")]
pub mod boxed;

#[cfg(feature = "alloc")]
pub mod vec;

#[cfg(not(feature = "devel"))]
mod devel;

#[cfg(feature = "devel")]
pub mod devel;

#[cfg(feature = "serde")]
mod serdes;
