/*! Run the `macro_rules!` expressions to ensure that they operate correctly.

!*/

extern crate bitvec;

use bitvec::prelude::*;

#[test]
fn bits() {
	let bits: &BitSlice<Local, Word> = bits![1, 0, 1, 1, 0, 1, 0, 0, 1, 0];
	assert_eq!(bits.len(), 10);
	assert!(bits[0]);
}
