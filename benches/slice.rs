#![feature(test)]

extern crate test;

use core::ops::AddAssign;

use bitvec::prelude::*;
use test::{
	Bencher,
	bench::black_box,
};

/* `BitSlice::empty` is not benched, because the compiler const-folds it. It
is not a `const fn`, but it has exactly one function call, which is `const`, and
creates a value object from that function. As such, the compiler can prove that
the return value is a `const` value, and insert the value at all
`BitSlice::empty` call sites. It takes 0ns.
*/

#[bench]
fn element(b: &mut Bencher) {
	b.iter(|| BitSlice::<Msb0, u8>::from_element(&!0));
	b.iter(|| BitSlice::<Lsb0, u8>::from_element(&!0));
	b.iter(|| BitSlice::<Msb0, u16>::from_element(&!0));
	b.iter(|| BitSlice::<Lsb0, u16>::from_element(&!0));
	b.iter(|| BitSlice::<Msb0, u32>::from_element(&!0));
	b.iter(|| BitSlice::<Lsb0, u32>::from_element(&!0));

	#[cfg(target_pointer_width = "64")] {

	b.iter(|| BitSlice::<Msb0, u64>::from_element(&!0));
	b.iter(|| BitSlice::<Lsb0, u64>::from_element(&!0));

	}
}

#[bench]
fn slice(b: &mut Bencher) {
	b.iter(|| BitSlice::<Msb0, u8>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Lsb0, u8>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Msb0, u16>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Lsb0, u16>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Msb0, u32>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Lsb0, u32>::from_slice(&[0, 1, !0 - 1, !0][..]));

	#[cfg(target_pointer_width = "64")] {

	b.iter(|| BitSlice::<Msb0, u64>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<Lsb0, u64>::from_slice(&[0, 1, !0 - 1, !0][..]));

	}
}

#[bench]
fn len(b: &mut Bencher) {
	let bsb08 = [0u8; 16].bits::<Msb0>();
	let bsl08 = [0u8; 16].bits::<Lsb0>();
	b.iter(|| bsb08.len());
	b.iter(|| bsl08.len());

	let bsb16 = [0u16; 8].bits::<Msb0>();
	let bsl16 = [0u16; 8].bits::<Lsb0>();
	b.iter(|| bsb16.len());
	b.iter(|| bsl16.len());

	let bsb32 = [0u32; 4].bits::<Msb0>();
	let bsl32 = [0u32; 4].bits::<Lsb0>();
	b.iter(|| bsb32.len());
	b.iter(|| bsl32.len());

	#[cfg(target_pointer_width = "64")] {

	let bsb64 = [0u64; 2].bits::<Msb0>();
	let bsl64 = [0u64; 2].bits::<Lsb0>();
	b.iter(|| bsb64.len());
	b.iter(|| bsl64.len());

	}
}

//  This index value is not only "nice", it also ensures that the hard path is
//  hit in `BitIdx::offset`.
#[bench]
fn index(b: &mut Bencher) {
	let bsb08 = [0u8; 16].bits::<Msb0>();
	let bsl08 = [0u8; 16].bits::<Lsb0>();
	b.iter(|| assert!(!black_box(bsb08)[black_box(69)]));
	b.iter(|| assert!(!black_box(bsl08)[black_box(69)]));

	let bsb16 = [0u16; 8].bits::<Msb0>();
	let bsl16 = [0u16; 8].bits::<Lsb0>();
	b.iter(|| assert!(!black_box(bsb16)[black_box(69)]));
	b.iter(|| assert!(!black_box(bsl16)[black_box(69)]));

	let bsb32 = [0u32; 4].bits::<Msb0>();
	let bsl32 = [0u32; 4].bits::<Lsb0>();
	b.iter(|| assert!(!black_box(bsb32)[black_box(69)]));
	b.iter(|| assert!(!black_box(bsl32)[black_box(69)]));

	#[cfg(target_pointer_width = "64")] {

	let bsb64 = [0u64; 2].bits::<Msb0>();
	let bsl64 = [0u64; 2].bits::<Lsb0>();
	b.iter(|| assert!(!black_box(bsb64)[black_box(69)]));
	b.iter(|| assert!(!black_box(bsl64)[black_box(69)]));

	}
}

/* This routine has more work to do: index, create a reference struct, and drop
it. The compiler *should* be able to properly arrange immediate drops, though.
*/
#[bench]
fn at(b: &mut Bencher) {
	let mut src = [0u8; 16];
	let bsb08 = src.bits_mut::<Msb0>();
	b.iter(|| *bsb08.at(69) = true);
	let mut src = [0u8; 16];
	let bsl08 = src.bits_mut::<Lsb0>();
	b.iter(|| *bsl08.at(69) = true);

	let mut src = [0u16; 8];
	let bsb16 = src.bits_mut::<Msb0>();
	b.iter(|| *bsb16.at(69) = true);
	let mut src = [0u16; 8];
	let bsl16 = src.bits_mut::<Lsb0>();
	b.iter(|| *bsl16.at(69) = true);

	let mut src = [0u32; 4];
	let bsb32 = src.bits_mut::<Msb0>();
	b.iter(|| *bsb32.at(69) = true);
	let mut src = [0u32; 4];
	let bsl32 = src.bits_mut::<Lsb0>();
	b.iter(|| *bsl32.at(69) = true);

	#[cfg(target_pointer_width = "64")] {

	let mut src = [0u64; 2];
	let bsb64 = src.bits_mut::<Msb0>();
	b.iter(|| *bsb64.at(69) = true);
	let mut src = [0u64; 2];
	let bsl64 = src.bits_mut::<Lsb0>();
	b.iter(|| *bsl64.at(69) = true);

	}
}

#[bench]
fn add_assign(b: &mut Bencher) {
	let mut src = [0u8; 16];
	let bsb08a = src.bits_mut::<Msb0>();
	let bsb08b = [0u8; 16].bits::<Msb0>();
	let mut src = [0u8; 16];
	let bsl08a = src.bits_mut::<Lsb0>();
	let bsl08b = [0u8; 16].bits::<Lsb0>();
	b.iter(|| bsb08a.add_assign(bsb08b.iter().copied()));
	b.iter(|| bsl08a.add_assign(bsl08b.iter().copied()));

	let mut src = [0u16; 8];
	let bsb16a = src.bits_mut::<Msb0>();
	let bsb16b = [0u16; 8].bits::<Msb0>();
	let mut src = [0u16; 8];
	let bsl16a = src.bits_mut::<Lsb0>();
	let bsl16b = [0u16; 8].bits::<Lsb0>();
	b.iter(|| bsb16a.add_assign(bsb16b.iter().copied()));
	b.iter(|| bsl16a.add_assign(bsl16b.iter().copied()));

	let mut src = [0u32; 4];
	let bsb32a = src.bits_mut::<Msb0>();
	let bsb32b = [0u32; 4].bits::<Msb0>();
	let mut src = [0u32; 4];
	let bsl32a = src.bits_mut::<Lsb0>();
	let bsl32b = [0u32; 4].bits::<Lsb0>();
	b.iter(|| bsb32a.add_assign(bsb32b.iter().copied()));
	b.iter(|| bsl32a.add_assign(bsl32b.iter().copied()));

	#[cfg(target_pointer_width = "64")] {

	let mut src = [0u64; 2];
	let bsb64a = src.bits_mut::<Msb0>();
	let bsb64b = [0u64; 2].bits::<Msb0>();
	let mut src = [0u64; 2];
	let bsl64a = src.bits_mut::<Lsb0>();
	let bsl64b = [0u64; 2].bits::<Lsb0>();
	b.iter(|| bsb64a.add_assign(bsb64b.iter().copied()));
	b.iter(|| bsl64a.add_assign(bsl64b.iter().copied()));

	}
}
