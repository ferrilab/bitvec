/*! Demonstrates construction and use of a big-endian, u8, `BitVec`

This example uses `bitvec!` to construct a `BitVec` from literals, then shows
a sample of the various operations that can be applied to it.

This example prints **a lot** of text to the console.
!*/

#[macro_use]
extern crate bitvec;

use bitvec::*;
use std::iter::repeat;

fn main() {
	let bv = bitvec![
		0, 0, 0, 0, 0, 0, 0, 1,
		0, 0, 0, 0, 0, 0, 1, 0,
		0, 0, 0, 0, 0, 1, 0, 0,
		0, 0, 0, 0, 1, 0, 0, 0,
		0, 0, 0, 1, 0, 0, 0, 0,
		0, 0, 1, 0, 0, 0, 0, 0,
		0, 1, 0, 0, 0, 0, 0, 0,
		1, 0, 0, 0, 0, 0, 0, 0,
		1, 0, 0, 0, 0, 0, 0, 0,
		0, 1, 0, 0, 0, 0, 0, 0,
		0, 0, 1, 0, 0, 0, 0, 0,
		0, 0, 0, 1, 0, 0, 0, 0,
		0, 0, 0, 0, 1, 0, 0, 0,
		0, 0, 0, 0, 0, 1, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 0,
		0, 0, 0, 0, 0, 0, 0, 1,
		1, 0, 1, 0,
	];
	println!("A BigEndian BitVec has the same layout in memory as it does semantically");
	render(&bv);

	//  BitVec can turn into iterators, and be built from iterators.
	let bv: BitVec<LittleEndian, u8> = bv.into_iter().collect();
	println!("A LittleEndian BitVec has the opposite layout in memory as it does semantically");
	render(&bv);

	let bv: BitVec<BigEndian, u16> = bv.into_iter().collect();
	println!("A BitVec can use storage other than u8");
	render(&bv);

	println!("BitVec can participate in Boolean arithmetic");
	let full = bv.clone() | repeat(true);
	render(&full);
	let empty = full & repeat(false);
	render(&empty);
	let flip = bv ^ repeat(true);
	render(&flip);
	let bv = !flip;
	render(&bv);

	println!("\
Notice that `^` did not affect the parts of the tail that were not in
use, while `!` did affect them. `^` requires a second source, while `!`
can just flip all elements. `!` is faster, but `^` is less likely to
break your assumptions about what the memory looks like.\
	");

	//  Push and pop to the bitvec
	let mut bv = bv;
	for _ in 0 .. 12 {
		bv.push(false);
	}
	for _ in 0 .. 12 {
		bv.pop();
	}
	render(&bv);

	println!("End example");
}

fn render<E: Endian, T: Bits>(bv: &BitVec<E, T>) {
	println!("Memory information: {} {} {}", bv.elts(), bv.bits(), bv.len());
	println!("Print out the semantic contents");
	println!("{:#?}", bv);
	println!("Print out the memory contents");
	println!("{:?}", bv.as_ref());
	println!("Show the bits in memory");
	for elt in bv.as_ref() {
		println!("{:0w$b} ", elt, w=::std::mem::size_of::<T>() * 8);
	}
	println!();
}
