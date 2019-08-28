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

2019-08-28: I implemented partial-head capability in `BitVec` (no effort other
than having `from_bitslice` preserve the head index) and added `::force_align`
to bring misaligned bit vectors to their expected memory layout.

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
	let bv = bitvec![
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

	//  2019-08-28: Cloning a partial-head slice uses the slice clone for speed,
	//  but preserves the head information so that the live bitslice remains
	//  unaffected.
	assert!(!bv2[0]);
	assert!(bv2[3]);
	assert!(bv2[4]);
	assert!(!bv2[7]);

	//  The raw memory uses the source as written,
	assert_eq!(bv2.as_slice().len(), 2);
	assert_eq!(bv2.as_slice(), &[0x01, 0x81]);
	//  until it is forced to align at the element boundary,
	bv2.force_align();
	//  at which point it rotates down and behaves as expected.
	assert_eq!(bv2.as_slice().len(), 1);
	assert_eq!(bv2.as_slice()[0], 0x18);
}
