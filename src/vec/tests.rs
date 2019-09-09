/*! Unit tests for `BitVec`
!*/

#![cfg(all(test, feature = "std"))]

#[test]
fn rotate_left_minor() {
	let mut bv = bitvec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1];

	assert_eq!(bv.len(), 13);
	assert_eq!(*bv.pointer.head(), 0);
	assert_eq!(*bv.pointer.tail(), 5);

	bv.rotate_left(3);
	assert_eq!(bv.len(), 13);
	assert_eq!(*bv.pointer.head(), 3);
	assert_eq!(*bv.pointer.tail(), 8);
	assert_eq!(bv, bitvec![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]);

	//  Make room in the back element for more than the live bits in the front.
	bv.truncate(7);
	assert_eq!(bv.len(), 7);
	assert_eq!(*bv.pointer.tail(), 2);
}
