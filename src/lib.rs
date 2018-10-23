/*! `BitVec` – `Vec<bool>` in overdrive.

A `BitVec` stores bits with the same behavior, API, and compactness guarantees
as `Vec`. It is as close to an implementation of `Vec<u1>`, if `u1` were a type
that Rust could meaningfully express, as is possible to express given the
limitations of the language and our machines.

`BitVec` provides strong guarantees about, and fine-grained control of, the
bit-level representation of a collection in memory. The user is empowered to
choose the primitive type that underlies the `BitVec` – `u8`, `u16`, `u32`, or
`u64` – and the order in which each primitive is traversed – big-endian, from
the most significant bit to the least, or little-endian, from the least
significant bit to the most.

This level of control is not necessary for most use cases where people just want
to put bits in a sequence, but is critically important for people making packets
that leave main memory and hit some external device like a peripheral controller
or a network socket. In order to provide convenience to users for whom the
storage details do not matter, `BitVec` defaults to using big-endian order of
bits on a `u8`. This order means that the bits you write down on paper match up
to the bits as stored in memory.

For example, if you have the bit sequence `[ 0, 1, 1, 0, 1, 0, 0, 1 ]` and
insert this into a `BitVec` without any extra specification, the `BitVec` will
hold the byte `0b01101001`. If the `BitVec` was in little-endian order, it would
be `0b10010110` (reversed order!).

In addition to providing compact, efficient, powerful storage and manipulation
of bits in memory, `BitVec` is capable of acting as a queue, set, and stream of
bits. It implements the bit-wise operators for Boolean arithmetic, read indexing
(write indexing to bits is impossible in Rust semantics on almost all machines),
iteration in both directions, bit shifts, and, of course, access to the
underlying storage as a slice.
!*/

#[macro_use]
mod macros;

mod bits;
mod endian;
mod slice;
mod vec;

pub use {
	bits::Bits,
	endian::*,
	macros::*,
	slice::BitSlice,
	vec::BitVec,
};

//  The `Index` trait returns references to bools, and it is impossible to make
//  an address for a bit in the middle of a byte. Therefore, `Index::index`
//  references these static values depending on the value of the bit.
//
//  This is *such* a hack, but, That’s Rust For Ya.
static TRUE: bool = true;
static FALSE: bool = false;
