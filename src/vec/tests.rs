/*! Unit tests for `BitVec`
!*/

#![cfg(all(test, feature = "std"))]

use crate::cursor::BigEndian;

//  Tests that the `rotate_left` function behaves as expected in all edge cases
#[test]
fn rotate_left_minor() {
	let mut bv = bitvec![
		BigEndian, u8;
		1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 1, 0, 1,
	];

	assert_eq!(bv.len(), 13);
	assert_eq!(*bv.pointer.head(), 0);
	assert_eq!(*bv.pointer.tail(), 5);

	bv.rotate_left(3);
	assert_eq!(bv.len(), 13);
	assert_eq!(*bv.pointer.head(), 3);
	assert_eq!(*bv.pointer.tail(), 8);
	assert_eq!(bv, bitvec![
		BigEndian, u8;
		         0, 0, 0, 0, 0,
		0, 0, 1, 0, 1, 1, 0, 0,
	]);

	//  Make room in the back element for more than the live bits in the front.
	bv.truncate(7);
	*bv.at(0) = true;
	*bv.at(6) = true;
	bv.rotate_left(5);
	assert_eq!(bv.as_slice(), &[0b0110000_0]);
}

#[test]
fn rotate_left_major() {
	let mut bv = bitvec![
		BigEndian, u8;
		1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 1, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 1,
	];
	bv.rotate_left(10);
	assert_eq!(bv, bitvec![
		BigEndian, u8;
		      1, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 1, 1, 0, 0,
		0, 0, 0, 0, 0, 0, 0,
	]);
}
