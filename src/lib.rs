/*! `bitvec` – `[bool]` in overdrive.

This crate provides views into slices of bits that are truly `[u1]`. Each bit in
the data segment is used, unlike `[bool]` which ignores seven bits out of every
byte.

`bitvec`’s data structures provide strong guarantees about, and fine-grained
control of, the bit-level representation of a sequence of memory. The user is
empowered to choose the fundamental type underlying the store – `u8`, `u16`,
`u32`, or `u64` – and the order in which each primitive is traversed – `Msb0`,
from the most significant bit to the least, or `Lsb0`, from the least
significant bit to the most.

This level of control is not necessary for most use cases where users just want
to put bits in a sequence, but it is critically important for users making
packets that leave main memory and hit some external device like a peripheral
controller or a network socket. In order to provide convenience to users for
whom the storage details do not matter, `bitvec` types default to using the
local C bitfield ordering and CPU word size.

In addition to providing compact, efficient, and powerful storage and
manipulation of bits in memory, the `bitvec` structures are capable of acting as
a queue, set, or stream of bits. They implement the bit-wise operators for
Boolean arithmetic, arithmetic operators for 2’s-complement numeric arithmetic,
read indexing, bit shifts, and access to the underlying storage fundamental
elements as a slice.

(Write indexing is impossible in Rust semantics.)
!*/

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(debug_assertions, warn(missing_docs))]
#![cfg_attr(not(debug_assertions), deny(missing_docs))]
#![deny(unconditional_recursion)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "serde")]
extern crate serde;

#[cfg(all(test, feature = "serde"))]
extern crate serde_test;

#[macro_use]
pub mod macros;

mod access;
pub mod bits;
mod domain;
pub mod indices;
pub mod fields;
pub mod order;
mod pointer;
pub mod prelude;
pub mod slice;
pub mod store;

#[cfg(feature = "alloc")]
pub mod boxed;

#[cfg(feature = "alloc")]
pub mod vec;

#[cfg(feature = "serde")]
mod serdes;

/** Perform single-bit ripple-carry addition.

This function performs carry-aware binary addition on single bits of each
addend. It is used in multiple places throughout the library, and so is pulled
here for deduplication.

# Parameters

- `a: bool`: One bit of addend.
- `b: bool`: One bit of addend.
- `c: bool`: The carry-bit input.

# Returns

- `.0: bool`: The sum of `a + b + c`.
- `.1: bool`: The carry-out of `a + b + c`.
**/
#[inline]
fn rca1(a: bool, b: bool, c: bool) -> (bool, bool) {
	// Ripple-carry addition is a reduction operation from three bits of input
	// (a, b, carry-in) to two outputs (sum, carry-out).
	//  Compute the sum from left, right and carry-in
	let yz = a as u8 + b as u8 + c as u8;
	//  Split them
	(yz & 0b01 != 0, yz & 0b10 != 0)
}
