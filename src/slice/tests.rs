/*! Unit tests for the `slice` module.
!*/

use crate::{
	order::{
		Local,
		Msb0,
	},
	slice::{
		AsBits,
		BitSlice,
	},
};

#[test]
fn all() {
	assert!(BitSlice::<Local, usize>::empty().all());

	let bits = &(!0u32).bits::<Local>()[2 ..][.. 28];
	assert!(bits.all());
	let bits = &0xA5u8.bits::<Local>()[1 ..][.. 6];
	assert!(bits.not_all());

	let bits = &[!0u8; 3].bits::<Local>()[2 ..][.. 20];
	assert!(bits.all());
	let bits = &[0xA5u8; 3].bits::<Local>()[2 ..][.. 20];
	assert!(bits.not_all());

	let bits = &[!0u8; 2].bits::<Local>()[4 ..];
	assert!(bits.all());
	let bits = &[0xA5u8; 2].bits::<Local>()[4 ..];
	assert!(bits.not_all());

	let bits = &[!0u8; 2].bits::<Local>()[.. 12];
	assert!(bits.all());
	let bits = &[!0xA5u8; 2].bits::<Local>()[.. 12];
	assert!(bits.not_all());

	assert!((!0u8).bits::<Local>().all());
	assert!(0xA5u8.bits::<Local>().not_all());
}

#[test]
fn any() {
	assert!(!BitSlice::<Local, usize>::empty().any());

	let bits = &(0xA5u8).bits::<Local>()[1 ..][.. 6];
	assert!(bits.any());
	let bits = &0u32.bits::<Local>()[2 ..][.. 28];
	assert!(bits.not_any());

	let bits = &[0u8, 0xA5, 0].bits::<Local>()[2 ..][.. 20];
	assert!(bits.any());
	let bits = &[0u8; 3].bits::<Local>()[2 ..][.. 20];
	assert!(bits.not_any());

	let bits = &[0u8, 0xA5].bits::<Local>()[4 ..];
	assert!(bits.any());
	let bits = &[0u8; 2].bits::<Local>()[4 ..];
	assert!(bits.not_any());

	let bits = &[0xA5u8, 0].bits::<Local>()[.. 12];
	assert!(bits.any());
	let bits = &[0u8; 2].bits::<Local>()[.. 12];
	assert!(bits.not_any());

	assert!(4u8.bits::<Local>().any());
	assert!(0u8.bits::<Local>().not_any());
}

#[test]
fn count_ones() {
	assert_eq!(BitSlice::<Local, usize>::empty().count_ones(), 0);
	assert_eq!(0xA5u8.bits::<Local>()[1 ..][.. 6].count_ones(), 2);

	// BE: bits=BitSlice<Msb0, u8> [00001111, 11111111, 11110000] = 16
	// LE: bits=BitSlice<Lsb0, u8> [11110000, 11111111, 00001111] = 12
	let ones = [0x0Fu8, !0, 0xF0].bits::<Local>()[2 ..][.. 20].count_ones();
	#[cfg(target_endian = "little")]
	assert_eq!(ones, 12);
	#[cfg(target_endian = "big")]
	assert_eq!(ones, 16);

	// BE: bits=BitSlice<Msb0, u8> [00001111, 11111111] = 12
	// LE: bits=BitSlice<Lsb0, u8> [11111111, 00001111] = 10
	let ones = [0x0Fu8, !0].bits::<Local>()[2 ..].count_ones();
	#[cfg(target_endian = "little")]
	assert_eq!(ones, 10);
	#[cfg(target_endian = "big")]
	assert_eq!(ones, 12);

	// BE: bits=BitSlice<Msb0, u8> [11111111, 11110000] = 12
	// LE: bits=BitSlice<Lsb0, u8> [11110000, 11111111] = 10
	let ones = [!0u8, 0xF0].bits::<Local>()[.. 14].count_ones();
	#[cfg(target_endian = "little")]
	assert_eq!(ones, 10);
	#[cfg(target_endian = "big")]
	assert_eq!(ones, 12);

	assert_eq!((!0u8).bits::<Local>().count_ones(), 8);
}

#[test]
fn count_zeros() {
	assert_eq!(BitSlice::<Local, usize>::empty().count_zeros(), 0);
	assert_eq!(0xA5u8.bits::<Local>()[1 ..][.. 6].count_zeros(), 4);

	// BE: bits=BitSlice<Lsb0, u8> [11110000, 00000000, 00001111] = 16
	// LE: bits=BitSlice<Msb0, u8> [00001111, 00000000, 11110000] = 11
	let zeros = [0xF0u8, 0, 0x0F].bits::<Local>()[2 ..][.. 20].count_zeros();
	#[cfg(target_endian = "little")]
	assert_eq!(zeros, 12);
	#[cfg(target_endian = "big")]
	assert_eq!(zeros, 16);

	// BE: bits=BitSlice<Msb0, u8> [11110000, 00000000] = 12
	// LE: bits=BitSlice<Lsb0, u8> [00000000, 11110000] = 10
	let zeros = [0xF0u8, 0].bits::<Local>()[2 ..].count_zeros();
	#[cfg(target_endian = "little")]
	assert_eq!(zeros, 10);
	#[cfg(target_endian = "big")]
	assert_eq!(zeros, 12);

	// BE: bits=BitSlice<Msb0, u8> [00000000, 00001111] = 12
	// LE: bits=BitSlice<Lsb0, u8> [00001111, 00000000] = 10
	let zeros = [0u8, 0x0F].bits::<Local>()[.. 14].count_zeros();
	#[cfg(target_endian = "little")]
	assert_eq!(zeros, 10);
	#[cfg(target_endian = "big")]
	assert_eq!(zeros, 12);

	assert_eq!(0u8.bits::<Local>().count_zeros(), 8);
}

#[test]
fn set_all() {
	let mut data = [0u8; 5];
	let bits = data.bits_mut::<Msb0>();

	bits[18 .. 22].set_all(true);
	assert_eq!(bits.as_slice(), [0, 0, 0b0011_1100, 0, 0]);
	bits[12 .. 28].set_all(true);
	assert_eq!(bits.as_slice(), [0, 0x0F, !0, 0xF0, 0]);
	bits[4 .. 16].set_all(false);
	assert_eq!(bits.as_slice(), [0, 0, !0, 0xF0, 0]);
	bits[16 .. 28].set_all(false);
	assert_eq!(bits.as_slice(), [0; 5]);
	bits.set_all(true);
	assert_eq!(data, [!0; 5]);
}
