/*! Demonstrates construction and use of bit vectors.

This example uses `bitvec!` to construct a `BitVec` from literals, then shows
a sample of the various operations that can be applied to it.

This example prints **a lot** of text to the console.
!*/

use bitvec::prelude::{
	bits,
	BitOrder,
	BitSlice,
	BitStore,
	BitVec,
	Lsb0,
	Msb0,
};

macro_rules! qprintln {
	($($t:tt)*) => {
		if !cfg!(feature = "testing") {
			println!($($t)*);
		}
	};
}

fn main() {
	//  Default types are `order::Lsb0` and `usize`
	let bits = bits![u8, Msb0;
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
	qprintln!(
		"A Msb0 BitSlice has the same left-to-right order in memory as it does \
		 semantically"
	);
	render(bits);

	//  BitVec can turn into iterators, and be built from iterators.
	let bv: BitVec<u8, Lsb0> = bits.iter().collect();
	qprintln!(
		"An Lsb0 BitVec has the opposite layout in memory as it does \
		 semantically"
	);
	render(&bv);

	let bv: BitVec<u16, Msb0> = bv.into_iter().collect();
	qprintln!("A BitVec can use storage other than u8");
	render(&bv);

	qprintln!("BitVec can participate in Boolean arithmetic");
	let full = bv.clone() | bits![1; 132];
	render(&full);
	let empty = full & bits![0; 132];
	render(&empty);
	let flip = bv ^ bits![1; 132];
	render(&flip);
	let bv = !flip;
	render(&bv);

	qprintln!(
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

	qprintln!("End example");

	fn render<T, O>(bs: &BitSlice<T, O>)
	where
		O: BitOrder,
		T: BitStore,
	{
		qprintln!(
			"Memory information: {} elements, {} bits",
			bs.domain().len(),
			bs.len(),
		);
		qprintln!("Print out the semantic contents");
		qprintln!("{:#?}", bs);
		qprintln!("Print out the memory contents");
		qprintln!("{:?}", bs.domain());
		qprintln!("Show the bits in memory");
		for elt in bs.domain() {
			qprintln!("{:0w$b} ", elt, w = bitvec::mem::bits_of::<T::Mem>());
		}
		qprintln!();
	}
}

#[cfg(not(feature = "std"))]
compile_error!("This example requires the standard library.");
