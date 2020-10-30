#![cfg(test)]

use crate::prelude::*;

#[test]
fn create_arrays() {
	macro_rules! make {
		($($elts:literal),+ $(,)?) => { $(
			let _ = BitArray::<LocalBits, [u8; $elts]>::zeroed();
			let _ = BitArray::<LocalBits, [u16; $elts]>::zeroed();
			let _ = BitArray::<LocalBits, [u32; $elts]>::zeroed();
			let _ = BitArray::<LocalBits, [usize; $elts]>::zeroed();

			#[cfg(target_pointer_width = "64")] {
			let _ = BitArray::<LocalBits, [u64; $elts]>::zeroed();
			}
		)+ };
	}

	make!(
		0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
		20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32
	);
}

#[test]
fn wrap_unwrap() {
	let data: [u8; 15] = *b"Saluton, mondo!";
	let bits = BitArray::<LocalBits, _>::new(data);
	assert_eq!(bits.value(), data);
}

#[test]
fn views() {
	let mut arr = bitarr![Msb0, u8; 0; 20];

	let s: &mut [u8] = arr.as_mut_slice();
	s[0] = !0u8;
	let s: &[u8] = arr.as_slice();
	assert_eq!(s, &[!0, 0, 0]);

	let a: &mut [u8; 3] = arr.as_mut_buffer();
	*a = [!0u8; 3];
	let a: &[u8; 3] = arr.as_buffer();
	assert_eq!(*a, [!0u8; 3]);
}

#[test]
fn iter() {
	let mut iter = bitarr![0, 0, 0, 1, 1, 1, 0, 0, 0].into_iter();
	let width = <[usize; 1] as BitView>::const_bits();

	let iter_slice = iter.as_bitslice();
	assert_eq!(iter_slice.count_ones(), 3);
	assert_eq!(iter_slice.len(), width);

	iter.as_mut_bitslice().set(0, true);
	assert_eq!(iter.as_bitslice().count_ones(), 4);

	assert!(iter.next().unwrap());
	//  get the last bit of the literal
	assert!(!iter.nth_back(width - 9).unwrap());
	//  advance to the first `0` bit after the `1`s in the literal
	assert!(!iter.nth_back(1).unwrap());
	assert!(!iter.nth(1).unwrap());
	assert_eq!(iter.as_bitslice(), bits![1; 3]);

	assert!(iter.next().unwrap());
	assert!(iter.clone().last().unwrap());
	assert_eq!(iter.size_hint(), (2, Some(2)));
	assert_eq!(iter.clone().count(), 2);

	//  Reference iterators

	assert!((&bitarr![0]).into_iter().all(|b| !*b));
	assert!((&bitarr![1]).into_iter().any(|b| *b));

	let mut arr = bitarr![0];
	assert!(arr.not_any());
	for mut bit in &mut arr {
		*bit = !*bit;
	}
	assert!(arr.all(), "{:?}", arr);
}
