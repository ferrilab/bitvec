/*! The `PartialEq` and `PartialOrd` trait implementations are *surprisingly*
hard to correctly implement. This test suite is built to ensure that all
combinations of equality and comparison are correctly present.
!*/

use bitvec::prelude::*;

#[test]
fn no_alloc() {
	let a = bits![mut Msb0, u8; 0, 1];
	let b = bits![mut Lsb0, u16; 0, 1];
	let c = bits![mut 1, 0];

	//  BitSlice as PartialEq<BitSlice>
	assert_eq!(*a, *b);
	//  BitSlice as PartialEq<&mut BitSlice>
	assert_eq!(*a, b);
	//  &mut BitSlice as PartialEq<BitSlice>
	assert_eq!(a, *b);
	//  &mut BitSlice as PartialEq<&mut BitSlice>
	assert_eq!(a, b);

	//  &BitSlice as PartialEq<&BitSlice>
	assert_eq!(&*a, &*b);
	//  &BitSlice as PartialEq<BitSlice>
	assert_eq!(&*a, *b);
	//  BitSlice as PartialEq<&BitSlice>
	assert_eq!(*a, &*b);

	//  &mut BitSlice as PartialEq<&BitSlice>
	assert_eq!(a, &*b);
	//  &BitSlice as PartialEq<&mut BitSlice>
	assert_eq!(&*a, b);

	//  BitSlice as PartialOrd<BitSlice>
	assert!(*b < *c);
	//  BitSlice as PartialOrd<&mut BitSlice>
	assert!(*b < c);
	//  &mut BitSlice as PartialOrd<BitSlice>
	assert!(b < *c);
	//  &mut BitSlice as PartialOrd<&mut BitSlice>
	assert!(b < c);

	#[allow(clippy::op_ref)]
	{
		//  &BitSlice as PartialOrd<&BitSlice>
		assert!(&*b < &*c);
		//  &BitSlice as PartialOrd<&mut BitSlice>
		assert!(&*b < c);
		//  &mut BitSlice as PartialOrd<&BitSlice>
		assert!(b < &*c);
	}
}

#[test]
#[rustfmt::skip]
#[cfg(feature = "alloc")]
fn with_alloc() {
	let a = bits![Msb0, u8; 0, 1];
	let b = bitbox![Lsb0, u16; 0, 1];
	let c = bitvec![0, 1];

	assert_eq!(a, a); assert_eq!(a, b); assert_eq!(a, c);
	assert_eq!(b, a); assert_eq!(b, b); assert_eq!(b, c);
	assert_eq!(c, a); assert_eq!(c, b); assert_eq!(c, c);
}
