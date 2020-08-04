//! Unit tests for the `slice` module.

#![cfg(test)]

use crate::prelude::*;

#[test]
fn construction() {
	use core::slice;
	let data = 0u8;
	let bits = data.view_bits::<Local>();
	assert_eq!(bits.len(), 8);

	assert!(
		BitSlice::<Local, u8>::from_slice(unsafe {
			slice::from_raw_parts(
				1usize as *const _,
				BitSlice::<Local, u8>::MAX_ELTS,
			)
		})
		.is_none()
	);

	assert!(
		BitSlice::<Local, u8>::from_slice_mut(unsafe {
			slice::from_raw_parts_mut(
				1usize as *mut _,
				BitSlice::<Local, u8>::MAX_ELTS,
			)
		})
		.is_none()
	);

	assert_eq!(
		unsafe { crate::slice::bits_from_raw_parts(&data, 0, 8) },
		Some(bits)
	);
	assert!(
		unsafe { crate::slice::bits_from_raw_parts::<Local, _>(&data, 0, !0) }
			.is_none()
	);

	let mut data = 0u8;
	assert_eq!(
		unsafe {
			crate::slice::bits_from_raw_parts_mut(&mut data as *mut _, 0, 8)
		},
		Some(data.view_bits_mut::<Local>())
	);
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

#[test]
fn query() {
	let data = [0x0Fu8, !0, 0xF0, 0, 0x0E];
	let bits = data.view_bits::<Msb0>();

	assert!(bits[36 .. 39].all());
	assert!(bits[4 .. 20].all());
	assert!(bits[.. 8].any());
	assert!(bits[4 .. 20].any());
	assert!(bits[32 ..].not_all());
	assert!(bits[.. 4].not_any());
	assert!(bits[.. 8].some());

	assert_eq!(bits[1 .. 7].count_ones(), 3);
	assert_eq!(bits[1 .. 7].count_zeros(), 3);
	assert_eq!(bits[.. 24].count_ones(), 16);
	assert_eq!(bits[16 ..].count_zeros(), 17);
}

#[test]
fn modify() {
	let mut data = 0b0000_1111u8;
	let bits = data.view_bits_mut::<Local>();

	bits.swap(3, 4);
	assert_eq!(data, 0b0001_0111);

	let bits = data.view_bits_mut::<Msb0>();
	bits.copy_within(2 .. 4, 0);
	assert_eq!(data, 0b0101_0111);

	let bits = data.view_bits_mut::<Msb0>();
	bits.copy_within(5 .., 2);
	assert_eq!(data, 0b0111_1111);
}
