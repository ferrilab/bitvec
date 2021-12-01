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
	mem::{
		bits_of,
		BitRegister,
	},
	order::verify_for_type,
	prelude::*,
};

pub struct Swizzle;

unsafe impl BitOrder for Swizzle {
	fn at<R>(index: BitIdx<R>) -> BitPos<R>
	where R: BitRegister {
		match bits_of::<R>() {
			8 => BitPos::new(index.into_inner() ^ 0b100).unwrap(),
			16 => BitPos::new(index.into_inner() ^ 0b1100).unwrap(),
			32 => BitPos::new(index.into_inner() ^ 0b11100).unwrap(),
			64 => BitPos::new(index.into_inner() ^ 0b111100).unwrap(),
			_ => unreachable!("No other integers are supported"),
		}
	}
}

#[test]
fn verify_u8() {
	verify_for_type::<u8, Swizzle>(cfg!(feature = "verbose"));
}

#[test]
#[cfg(not(tarpaulin))]
fn verify_u16() {
	verify_for_type::<u16, Swizzle>(cfg!(feature = "verbose"));
}

#[test]
#[cfg(not(tarpaulin))]
fn verify_u32() {
	verify_for_type::<u32, Swizzle>(cfg!(feature = "verbose"));
}

#[test]
#[cfg(not(tarpaulin))]
#[cfg(target_pointer_width = "64")]
fn verify_u64() {
	verify_for_type::<u64, Swizzle>(cfg!(feature = "verbose"));
}

#[test]
#[cfg(not(tarpaulin))]
fn verify_usize() {
	verify_for_type::<usize, Swizzle>(cfg!(feature = "verbose"));
}
