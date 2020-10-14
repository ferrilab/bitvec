/*! Third-party crates should be able to implement [`BitOrder`] usefully.

This test ensures that [`bitvec`] provides a sufficient API to implement
[`BitOrder`] in foreign crates and have these orderings work in the `bitvec`
system as peers of the provided orderings.
!*/

extern crate bitvec;

use bitvec::{
	index::{
		BitIdx,
		BitPos,
	},
	mem::BitRegister,
	prelude::*,
};

pub struct Swizzle;

unsafe impl BitOrder for Swizzle {
	fn at<R>(index: BitIdx<R>) -> BitPos<R>
	where R: BitRegister {
		match R::BITS {
			8 => BitPos::new(index.value() ^ 0b100).unwrap(),
			16 => BitPos::new(index.value() ^ 0b1100).unwrap(),
			32 => BitPos::new(index.value() ^ 0b11100).unwrap(),
			64 => BitPos::new(index.value() ^ 0b111100).unwrap(),
			_ => unreachable!("No other integers are supported"),
		}
	}
}

#[test]
#[cfg(not(miri))]
fn check_impl() {
	bitvec::order::verify::<Swizzle>(cfg!(feature = "testing"));
}
