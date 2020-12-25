/*! The `PartialEq` and `PartialOrd` trait implementations are *surprisingly*
hard to correctly implement. This test suite is built to ensure that all
combinations of equality and comparison are correctly present.
!*/

use core::cmp::Ordering;

use bitvec::prelude::*;

#[test]
fn slice_only() {
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
	let b = bits![mut Lsb0, u16; 0, 1];
	let c = bitbox![Lsb0, u32; 0, 1];
	let d = bitvec![Msb0, usize; 0, 1];

	assert_eq!(a, a); assert_eq!(a, b); assert_eq!(a, c); assert_eq!(a, d);
	assert_eq!(b, a); assert_eq!(b, b); assert_eq!(b, c); assert_eq!(b, d);
	assert_eq!(c, a); assert_eq!(c, b); assert_eq!(c, c); assert_eq!(c, d);
	assert_eq!(d, a); assert_eq!(d, b); assert_eq!(d, c); assert_eq!(d, d);

	assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));
	assert_eq!(a.partial_cmp(&b), Some(Ordering::Equal));
	assert_eq!(a.partial_cmp(&c), Some(Ordering::Equal));
	assert_eq!(a.partial_cmp(&d), Some(Ordering::Equal));

	assert_eq!(b.partial_cmp(&a), Some(Ordering::Equal));
	assert_eq!(b.partial_cmp(&b), Some(Ordering::Equal));
	assert_eq!(b.partial_cmp(&c), Some(Ordering::Equal));
	assert_eq!(b.partial_cmp(&d), Some(Ordering::Equal));

	assert_eq!(c.partial_cmp(&a), Some(Ordering::Equal));
	assert_eq!(c.partial_cmp(&b), Some(Ordering::Equal));
	assert_eq!(c.partial_cmp(&c), Some(Ordering::Equal));
	assert_eq!(c.partial_cmp(&d), Some(Ordering::Equal));

	assert_eq!(d.partial_cmp(&a), Some(Ordering::Equal));
	assert_eq!(d.partial_cmp(&b), Some(Ordering::Equal));
	assert_eq!(d.partial_cmp(&c), Some(Ordering::Equal));
	assert_eq!(d.partial_cmp(&d), Some(Ordering::Equal));

}
