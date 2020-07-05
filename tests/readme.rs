/*! Prove that the example code in `README.md` executes.

Until the README.md file can be linked into the library directly for `rustdoc`
to use, this file must be consistently updated whenever the README’s code
samples are modified.
!*/

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[cfg(feature = "alloc")]
use std::iter::repeat;

#[cfg(feature = "alloc")]
#[test]
fn readme() {
	//  macro constructor
	let mut bv = bitvec![Msb0, u8; 0, 1, 0, 1];

	//  `BitVec` has the `Vec` inherent API
	bv.reserve(8);

	//  and can be filled from any source of `bool`
	bv.extend(repeat(false).take(4));
	bv.extend(repeat(true).take(4));

	//  `BitSlice` can yield its raw memory
	assert_eq!(
		bv.as_slice(),
		&[0b0101_0000, 0b1111_0000],
		//  ^ index 0       ^ index 11
	);
	assert_eq!(bv.len(), 12);
	assert!(bv.capacity() >= 16);

	//  `BitVec`, like `Vec`, is a LIFO stack
	bv.push(true);
	bv.push(false);
	bv.push(true);

	//  `BitSlice` has indexing
	assert!(bv[12]);
	assert!(!bv[13]);
	assert!(bv[14]);
	assert!(bv.get(15).is_none());

	//  … and range indexing
	let last = &bv[12 ..];
	assert_eq!(last.len(), 3);
	assert!(last.any());

	(0 .. 3).for_each(|_| {
		bv.pop();
	});

	//  `BitSlice` provides set arithmetic against any `bool` source
	bv &= repeat(true);
	bv |= repeat(false);
	//  Invert all live bits
	bv ^= repeat(true);
	//  And again
	bv = !bv;

	//  It can iterate
	let mut count = 0;
	for bit in bv.iter() {
		if *bit {
			count += 1;
		}
	}
	assert_eq!(count, 6);

	//  … mutably
	for (idx, mut bit) in bv.iter_mut().enumerate() {
		*bit ^= idx % 2 == 0;
	}

	//  `BitSlice` can store variables
	bv[1 .. 7].store(0x3Fu8);
	//  and fetch them
	assert_eq!(bv[1 .. 7].load::<u8>(), 0x3F);
}
