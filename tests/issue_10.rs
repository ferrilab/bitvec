/*! Test case for [Issue #10], opened by [@overminder]

Issue #10 is a bug in the implementation of `<BitSlice as ToOwned>::to_owned`.
That trait implementation used `BitVec::from_bitslice`, which had the incorrect
behavior of cloning the underlying `&[T]` slice into a vector. Bit slices are
capable of partial-element heads, while bit vectors are not (at time of issue).
This meant that cloning an intermediate span copied from the start of the first
element, rather than from the first bit.

The fix was to use `<BitVec as FromIterator<bool>>::from_iter` to power both
`BitVec::from_bitslice` and `<BitSlice as ToOwned>::to_owned`.

In the future, it may be possible to revert to the original
`<[T] as ToOwned>::to_owned` implementation, if `BitVec` becomes capable of
partial heads without loss of pointer information.

[Issue #10]: https://github.com/myrrlyn/bitvec/issues/10
[@overminder]: https://github.com/overminder
!*/

#[cfg(feature = "alloc")]
extern crate bitvec;

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[cfg(feature = "alloc")]
#[test]
fn issue_10() {
	let bv = bitvec![Local, u8;
		0, 0, 0, 0,
		0, 0, 0, 1,
		1, 0, 0, 0,
		0, 0, 0, 1,
	];

	let slice = &bv[4 .. 12];
	assert_eq!(slice.len(), 8);
	assert!(!slice[0]);
	assert!(slice[3]);
	assert!(slice[4]);
	assert!(!slice[7]);

	let mut bv2 = slice.to_owned();
	assert_eq!(bv2, slice);
	assert!(!bv2[0]);
	assert!(bv2[3]);
	assert!(bv2[4]);
	assert!(!bv2[7]);

	bv2.force_align();
	//  These may be removed in the future.
	assert_eq!(bv2.as_slice().len(), 1);
	assert_eq!(bv2.as_slice()[0], 0x18);
}
