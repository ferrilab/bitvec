//! Unit tests for the `slice` module.

#![cfg(test)]

use crate::prelude::*;

#[test]
fn construction() {
	let data = 0u8;
	let bits = data.view_bits::<Local>();
	assert_eq!(bits.len(), 8);
}

#[test]
fn get_set() {
	let mut data = 0u8;
	let bits = data.view_bits_mut::<Local>();

	for n in 0 .. 8 {
		assert!(!bits.get(n).unwrap());
		bits.set(n, true);
		assert!(bits.get(n).unwrap());
	}

	assert_eq!(bits.first(), Some(&true));
	*bits.first_mut().unwrap() = false;
	assert_eq!(bits.last(), Some(&true));
	*bits.last_mut().unwrap() = false;
}
