/*! Issue 77 notes a segfault discovered when using the `.rev()` adapter.

The bug is due to an incorrect multiplication of the difference between base and
last pointers in the iterators. I incorrectly treated the pointers as being
element-stepped, rather than byte-stepped, and was multiplying the difference by
too much a factor when computing `.len()`. This breach of contract in the
`ExactSizeIterator` caused `core::iter::Rev` to misbehave, and address memory
out of bounds.
!*/

#[test]
#[cfg(feature = "alloc")]
fn issue_77() {
	use bitvec::vec::BitVec;

	// The argument of `take`. If above "SOME" threshold, it will panic!
	// If below "the" threshold, the assert will fail instead.
	//
	// It appears that the threshold for normal execution is 4,
	// but when executing the binary via `gdb` it is 6.
	const N: usize = 6;

	let mut bv: BitVec = BitVec::new();
	// Must be at least the 'register size', but may be much larger
	bv.resize(64, true);

	// Here the complete iter-rev-take-rev-sequence is mandatory to reproduce the
	// error, just the `collect` is here for convenience.
	let last_few: Vec<_> = bv
		.iter()
		.rev()
		.take(N)
		.rev()
		.collect();

	// Also notice, `bv` only contains `true`, but with `N` < 4, the `last_few`
	// are all `false`!!!
	assert_eq!(&[&true; N], last_few.as_slice());
}
