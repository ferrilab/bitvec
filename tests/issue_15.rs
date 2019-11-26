/*! Reserving space when a BitVec is filled to a boundary induces false panic.

This is due to a faulty validity check (`BitIdx::span` calls `BitIdx::is_valid`)
called during `BitVec::reserve` using the *tail* of the vector, which at the
boundary, is a valid tail but not a valid head.

This is a regression.
!*/

#![cfg(feature = "alloc")]

use bitvec::prelude::*;

#[test]
fn issue_15() {
	let mut bv = bitvec![0; 8];
	bv.reserve(16);
}
