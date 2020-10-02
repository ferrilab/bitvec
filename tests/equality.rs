/*! The `PartialEq` and `PartialOrd` trait implementations are *surprisingly*
hard to correctly implement. This test suite is built to ensure that all
combinations of equality and comparison are correctly present.
!*/

use bitvec::prelude::*;

use core::cmp::Ordering;

#[test]
fn no_alloc() {
	let a = bits![mut Msb0, u8; 0, 1];
	let b = bits![mut Lsb0, u16; 0, 1];
	let c = bits![mut 1, 0];

	//  BitSlice as PartialEq<BitSlice>
	assert!(<BitSlice<_, _> as PartialEq<BitSlice<_, _>>>::eq(&*a, &*b));
	//  BitSlice as PartialEq<&mut BitSlice>
	assert!(<BitSlice<_, _> as PartialEq<&mut BitSlice<_, _>>>::eq(
		&*a, &b
	));
	//  &mut BitSlice as PartialEq<BitSlice>
	assert!(<&mut BitSlice<_, _> as PartialEq<BitSlice<_, _>>>::eq(
		&a, &*b
	));
	//  &mut BitSlice as PartialEq<&mut BitSlice>
	assert!(<&mut BitSlice<_, _> as PartialEq<&mut BitSlice<_, _>>>::eq(
		&a, &b
	));

	//  &BitSlice as PartialEq<&BitSlice>
	assert!(<&BitSlice<_, _> as PartialEq<&BitSlice<_, _>>>::eq(
		&&*a, &&*b
	));
	//  &BitSlice as PartialEq<BitSlice>
	assert!(<&BitSlice<_, _> as PartialEq<BitSlice<_, _>>>::eq(
		&&*a, &*b
	));
	//  BitSlice as PartialEq<&BitSlice>
	assert!(<BitSlice<_, _> as PartialEq<&BitSlice<_, _>>>::eq(
		&*a, &&*b
	));

	//  &mut BitSlice as PartialEq<&BitSlice>
	assert!(<&mut BitSlice<_, _> as PartialEq<&BitSlice<_, _>>>::eq(
		&a, &&*b
	));
	//  &BitSlice as PartialEq<&mut BitSlice>
	assert!(<&BitSlice<_, _> as PartialEq<&mut BitSlice<_, _>>>::eq(
		&&*a, &b
	));

	//  BitSlice as PartialOrd<BitSlice>
	assert_eq!(
		<BitSlice<_, _> as PartialOrd<BitSlice<_, _>>>::partial_cmp(&*b, &*c),
		Some(Ordering::Less)
	);
	//  BitSlice as PartialOrd<&mut BitSlice>
	assert_eq!(
		<BitSlice<_, _> as PartialOrd<&mut BitSlice<_, _>>>::partial_cmp(
			&*b, &c
		),
		Some(Ordering::Less)
	);
	//  &mut BitSlice as PartialOrd<BitSlice>
	assert_eq!(
		<&mut BitSlice<_, _> as PartialOrd<BitSlice<_, _>>>::partial_cmp(
			&b, &*c
		),
		Some(Ordering::Less)
	);
	//  &mut BitSlice as PartialOrd<&mut BitSlice>
	assert_eq!(
		<&mut BitSlice<_, _> as PartialOrd<&mut BitSlice<_, _>>>::partial_cmp(
			&b, &c
		),
		Some(Ordering::Less)
	);

	//  &BitSlice as PartialOrd<&BitSlice>
	assert_eq!(
		<&BitSlice<_, _> as PartialOrd<&BitSlice<_, _>>>::partial_cmp(
			&&*b, &&*c
		),
		Some(Ordering::Less)
	);
	//  &BitSlice as PartialOrd<&mut BitSlice>
	assert_eq!(
		<&BitSlice<_, _> as PartialOrd<&mut BitSlice<_, _>>>::partial_cmp(
			&&*b, &c
		),
		Some(Ordering::Less)
	);
	//  &mut BitSlice as PartialOrd<&BitSlice>
	assert_eq!(
		<&mut BitSlice<_, _> as PartialOrd<&BitSlice<_, _>>>::partial_cmp(
			&b, &&*c
		),
		Some(Ordering::Less)
	);
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
