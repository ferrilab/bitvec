/*! Demonstrates construction and use of a `BitVec<Msb0, u8>`.

This example uses `bitvec!` to construct a `BitVec` from literals, then shows
a sample of the various operations that can be applied to it.

This example prints **a lot** of text to the console.
!*/

#[cfg(feature = "std")]
use bitvec::prelude::{
	//  `bitvec!` macro
	bitvec,
	//  memory information about the underlying type (for debugging info)
	BitMemory,
	//  element-traversal trait (you shouldn’t explicitly need this)
	BitOrder,
	//  slice type, analagous to `[u1]`
	BitSlice,
	//  trait unifying the primitives (you shouldn’t explicitly need this)
	BitStore,
	//  vector type, analagous to `Vec<u1>`
	BitVec,
	Lsb0,
	//  directionality type markers
	Msb0,
};

#[cfg(feature = "std")]
use std::iter::repeat;

#[cfg(feature = "std")]
fn main() {
	let bv = bitvec![Msb0, u8;  //  Default types are `order::Local` and `usize`
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
	println!(
		"A Msb0 BitVec has the same layout in memory as it does semantically"
	);
	render(&bv);

	//  BitVec can turn into iterators, and be built from iterators.
	let bv: BitVec<Lsb0, u8> = bv.into_iter().collect();
	println!(
		"An Lsb0 BitVec has the opposite layout in memory as it does \
		 semantically"
	);
	render(&bv);

	let bv: BitVec<Msb0, u16> = bv.into_iter().collect();
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

	println!(
		"\
Bit slice operations will never affect or observe memory outside the domain of
the slice descriptor. This can result in slow behavior when operations must work
bit-by-bit on partial outer elements, especially as the slice uses more of the
outer, but any whole elements in the slice will always use the full-element
operations. This makes `u8` faster than `u32` in cases where the partially-used
edge elements dominate, but `u32` faster than `u8` when wholly-used elements
are dominant."
	);

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

	fn render<O, T>(bs: &BitSlice<O, T>)
	where
		O: BitOrder,
		T: BitStore,
	{
		println!(
			"Memory information: {} elements, {} bits",
			bs.as_slice().len(),
			bs.len(),
		);
		println!("Print out the semantic contents");
		println!("{:#?}", bs);
		println!("Print out the memory contents");
		println!("{:?}", bs.domain());
		println!("Show the bits in memory");
		for elt in bs.domain() {
			println!("{:0w$b} ", elt, w = T::Mem::BITS as usize);
		}
		println!();
	}
}

#[cfg(not(feature = "std"))]
fn main() {
	//  This example requires the standard library.
}
