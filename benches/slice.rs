#![feature(test)]

extern crate test;

use core::ops::AddAssign;

use bitvec::prelude::*;
use test::Bencher;

//  `BitSlice::empty` is not benched, because the compiler const-folds it. It
//  is not a `const fn`, but it has exactly one function call, which is `const`,
//  and creates a value object from that function. As such, the compiler can
//  prove that the return value is a `const` value, and insert the value at all
//  `BitSlice::empty` call sites. It takes 0ns.

#[bench]
fn element(b: &mut Bencher) {
	b.iter(|| BitSlice::<BigEndian, u8>::from_element(&!0));
	b.iter(|| BitSlice::<LittleEndian, u8>::from_element(&!0));
	b.iter(|| BitSlice::<BigEndian, u16>::from_element(&!0));
	b.iter(|| BitSlice::<LittleEndian, u16>::from_element(&!0));
	b.iter(|| BitSlice::<BigEndian, u32>::from_element(&!0));
	b.iter(|| BitSlice::<LittleEndian, u32>::from_element(&!0));

	#[cfg(target_pointer_width = "64")] {

	b.iter(|| BitSlice::<BigEndian, u64>::from_element(&!0));
	b.iter(|| BitSlice::<LittleEndian, u64>::from_element(&!0));

	}
}

#[bench]
fn slice(b: &mut Bencher) {
	b.iter(|| BitSlice::<BigEndian, u8>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<LittleEndian, u8>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<BigEndian, u16>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<LittleEndian, u16>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<BigEndian, u32>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<LittleEndian, u32>::from_slice(&[0, 1, !0 - 1, !0][..]));

	#[cfg(target_pointer_width = "64")] {

	b.iter(|| BitSlice::<BigEndian, u64>::from_slice(&[0, 1, !0 - 1, !0][..]));
	b.iter(|| BitSlice::<LittleEndian, u64>::from_slice(&[0, 1, !0 - 1, !0][..]));

	}
}

#[bench]
fn len(b: &mut Bencher) {
	let bsb08 = [0u8; 16].as_bitslice::<BigEndian>();
	let bsl08 = [0u8; 16].as_bitslice::<LittleEndian>();
	b.iter(|| bsb08.len());
	b.iter(|| bsl08.len());

	let bsb16 = [0u16; 8].as_bitslice::<BigEndian>();
	let bsl16 = [0u16; 8].as_bitslice::<LittleEndian>();
	b.iter(|| bsb16.len());
	b.iter(|| bsl16.len());

	let bsb32 = [0u32; 4].as_bitslice::<BigEndian>();
	let bsl32 = [0u32; 4].as_bitslice::<LittleEndian>();
	b.iter(|| bsb32.len());
	b.iter(|| bsl32.len());

	#[cfg(target_pointer_width = "64")] {

	let bsb64 = [0u64; 2].as_bitslice::<BigEndian>();
	let bsl64 = [0u64; 2].as_bitslice::<LittleEndian>();
	b.iter(|| bsb64.len());
	b.iter(|| bsl64.len());

	}
}

//  This index value is not only "nice", it also ensures that the hard path is
//  hit in `BitIdx::offset`.
#[bench]
fn index(b: &mut Bencher) {
	let bsb08 = [0u8; 16].as_bitslice::<BigEndian>();
	let bsl08 = [0u8; 16].as_bitslice::<LittleEndian>();
	b.iter(|| bsb08[69]);
	b.iter(|| bsl08[69]);

	let bsb16 = [0u16; 8].as_bitslice::<BigEndian>();
	let bsl16 = [0u16; 8].as_bitslice::<LittleEndian>();
	b.iter(|| bsb16[69]);
	b.iter(|| bsl16[69]);

	let bsb32 = [0u32; 4].as_bitslice::<BigEndian>();
	let bsl32 = [0u32; 4].as_bitslice::<LittleEndian>();
	b.iter(|| bsb32[69]);
	b.iter(|| bsl32[69]);

	#[cfg(target_pointer_width = "64")] {

	let bsb64 = [0u64; 2].as_bitslice::<BigEndian>();
	let bsl64 = [0u64; 2].as_bitslice::<LittleEndian>();
	b.iter(|| bsb64[69]);
	b.iter(|| bsl64[69]);

	}
}

//  This routine has more work to do: index, create a reference struct, and drop
//  it. The compiler *should* be able to properly arrange immediate drops,
//  though.
#[bench]
fn at(b: &mut Bencher) {
	let mut src = [0u8; 16];
	let bsb08 = src.as_mut_bitslice::<BigEndian>();
	b.iter(|| *bsb08.at(69) = true);
	let mut src = [0u8; 16];
	let bsl08 = src.as_mut_bitslice::<LittleEndian>();
	b.iter(|| *bsl08.at(69) = true);

	let mut src = [0u16; 8];
	let bsb16 = src.as_mut_bitslice::<BigEndian>();
	b.iter(|| *bsb16.at(69) = true);
	let mut src = [0u16; 8];
	let bsl16 = src.as_mut_bitslice::<LittleEndian>();
	b.iter(|| *bsl16.at(69) = true);

	let mut src = [0u32; 4];
	let bsb32 = src.as_mut_bitslice::<BigEndian>();
	b.iter(|| *bsb32.at(69) = true);
	let mut src = [0u32; 4];
	let bsl32 = src.as_mut_bitslice::<LittleEndian>();
	b.iter(|| *bsl32.at(69) = true);

	#[cfg(target_pointer_width = "64")] {

	let mut src = [0u64; 2];
	let bsb64 = src.as_mut_bitslice::<BigEndian>();
	b.iter(|| *bsb64.at(69) = true);
	let mut src = [0u64; 2];
	let bsl64 = src.as_mut_bitslice::<LittleEndian>();
	b.iter(|| *bsl64.at(69) = true);

	}
}

#[bench]
fn add_assign(b: &mut Bencher) {
	let mut src = [0u8; 16];
	let bsb08a = src.as_mut_bitslice::<BigEndian>();
	let bsb08b = [0u8; 16].as_bitslice::<BigEndian>();
	let mut src = [0u8; 16];
	let bsl08a = src.as_mut_bitslice::<LittleEndian>();
	let bsl08b = [0u8; 16].as_bitslice::<LittleEndian>();
	b.iter(|| bsb08a.add_assign(bsb08b));
	b.iter(|| bsl08a.add_assign(bsl08b));

	let mut src = [0u16; 8];
	let bsb16a = src.as_mut_bitslice::<BigEndian>();
	let bsb16b = [0u16; 8].as_bitslice::<BigEndian>();
	let mut src = [0u16; 8];
	let bsl16a = src.as_mut_bitslice::<LittleEndian>();
	let bsl16b = [0u16; 8].as_bitslice::<LittleEndian>();
	b.iter(|| bsb16a.add_assign(bsb16b));
	b.iter(|| bsl16a.add_assign(bsl16b));

	let mut src = [0u32; 4];
	let bsb32a = src.as_mut_bitslice::<BigEndian>();
	let bsb32b = [0u32; 4].as_bitslice::<BigEndian>();
	let mut src = [0u32; 4];
	let bsl32a = src.as_mut_bitslice::<LittleEndian>();
	let bsl32b = [0u32; 4].as_bitslice::<LittleEndian>();
	b.iter(|| bsb32a.add_assign(bsb32b));
	b.iter(|| bsl32a.add_assign(bsl32b));

	#[cfg(target_pointer_width = "64")] {

	let mut src = [0u64; 2];
	let bsb64a = src.as_mut_bitslice::<BigEndian>();
	let bsb64b = [0u64; 2].as_bitslice::<BigEndian>();
	let mut src = [0u64; 2];
	let bsl64a = src.as_mut_bitslice::<LittleEndian>();
	let bsl64b = [0u64; 2].as_bitslice::<LittleEndian>();
	b.iter(|| bsb64a.add_assign(bsb64b));
	b.iter(|| bsl64a.add_assign(bsl64b));

	}
}
