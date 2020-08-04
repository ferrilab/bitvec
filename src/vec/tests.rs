#![cfg(test)]

use crate::prelude::*;

#[test]
fn push() {
	let mut bvm08 = BitVec::<Msb0, u8>::new();
	assert!(bvm08.is_empty());

	bvm08.push(false);
	assert_eq!(bvm08.len(), 1);
	assert!(!bvm08[0]);

	bvm08.push(true);
	assert_eq!(bvm08.len(), 2);
	assert!(bvm08[1]);

	bvm08.extend(&[true; 3]);
	bvm08.extend(&[false; 3]);
	assert_eq!(bvm08, bits![0, 1, 1, 1, 1, 0, 0, 0]);
}

#[test]
fn inspect() {
	let bv = bitvec![Local, u16; 0; 40];
	assert_eq!(bv.elements(), 3);
}

#[test]
fn force_align() {
	let data = 0xA5u8;
	let bits = data.view_bits::<Msb0>();

	let mut bv = bits[2 ..].to_bitvec();
	assert_eq!(bv.as_slice(), &[0xA5u8]);
	bv.force_align();
	assert_eq!(bv.as_slice(), &[0b1001_0101]);
	bv.force_align();
	assert_eq!(bv.as_slice(), &[0b1001_0101]);
}
