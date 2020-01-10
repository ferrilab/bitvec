/*! Permutation testing

This module contains tests to check boundary conditions on all permutations of
the six variables present in `BitField` functions:

1. `Lsb0` and `Msb0` slice orderings
2. `u8`, `u16`, `u32`, `u64` slice storage types
3. `load` and `store` trait behaviors
4. `_le` and `_be` element orderings
5. `u8`, `u16`, `u32`, `u64` value transfer types
6. Empty slice and too-wide slice conditions
!*/

#![cfg(test)]

use super::*;
use crate::prelude::*;

#[test]
fn check_mask() {
	for (n, mask) in &[
		(0, 0x00),
		(1, 0x01),
		(7, 0x7F),
		(8, 0xFF),
		][..] {
		assert_eq!(mask_for::<u8>(*n), *mask);
	}

	for (n, mask) in &[
		(0,  0x0000),
		(1,  0x0001),
		(15, 0x7FFF),
		(16, 0xFFFF),
	][..] {
		assert_eq!(mask_for::<u16>(*n), *mask);
	}

	for (n, mask) in &[
		(0,  0x0000_0000),
		(1,  0x0000_0001),
		(31, 0x7FFF_FFFF),
		(32, 0xFFFF_FFFF),
	][..] {
		assert_eq!(mask_for::<u32>(*n), *mask);
	}

	#[cfg(target_pointer_width = "64")]
	for (n, mask) in &[
		(0,  0x0000_0000_0000_0000),
		(1,  0x0000_0000_0000_0001),
		(63, 0x7FFF_FFFF_FFFF_FFFF),
		(64, 0xFFFF_FFFF_FFFF_FFFF),
		][..] {
		assert_eq!(mask_for::<u64>(*n), *mask);
	}
}

#[test]
fn check_resize() {
	assert_eq!(resize::<u8, u8>(0xA5u8), 0xA5u8);
	assert_eq!(resize::<u8, u16>(0xA5u8), 0xA5u16);
	assert_eq!(resize::<u8, u32>(0xA5u8), 0xA5u32);

	assert_eq!(resize::<u16, u8>(0x1234u16), 0x34u8);
	assert_eq!(resize::<u16, u16>(0x1234u16), 0x1234u16);
	assert_eq!(resize::<u16, u32>(0x1234u16), 0x1234u32);

	assert_eq!(resize::<u32, u8>(0x1234_5678u32), 0x78u8);
	assert_eq!(resize::<u32, u16>(0x1234_5678u32), 0x5678u16);
	assert_eq!(resize::<u32, u32>(0x1234_5678u32), 0x1234_5678u32);

	#[cfg(target_pointer_width = "64")] {

	assert_eq!(resize::<u8, u64>(0xA5u8), 0xA5u64);
	assert_eq!(resize::<u16, u64>(0x1234u16), 0x1234u64);
	assert_eq!(resize::<u32, u64>(0x1234_5678u32), 0x1234_5678u64);

	assert_eq!(resize::<u64, u8>(0x0123_4567_89AB_CDEFu64), 0xEFu8);
	assert_eq!(resize::<u64, u16>(0x0123_4567_89AB_CDEFu64), 0xCDEFu16);
	assert_eq!(resize::<u64, u32>(0x0123_4567_89AB_CDEFu64), 0x89AB_CDEFu32);
	assert_eq!(resize::<u64, u64>(0x0123_4567_89AB_CDEFu64), 0x0123_4567_89AB_CDEFu64);

	}
}

#[test]
#[should_panic]
fn bsl08_ll08_empty() { BitSlice::<Lsb0, u8>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl08_ll16_empty() { BitSlice::<Lsb0, u8>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl08_ll32_empty() { BitSlice::<Lsb0, u8>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_ll64_empty() { BitSlice::<Lsb0, u8>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl08_lb08_empty() { BitSlice::<Lsb0, u8>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl08_lb16_empty() { BitSlice::<Lsb0, u8>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl08_lb32_empty() { BitSlice::<Lsb0, u8>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_lb64_empty() { BitSlice::<Lsb0, u8>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl16_ll08_empty() { BitSlice::<Lsb0, u16>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl16_ll16_empty() { BitSlice::<Lsb0, u16>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl16_ll32_empty() { BitSlice::<Lsb0, u16>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_ll64_empty() { BitSlice::<Lsb0, u16>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl16_lb08_empty() { BitSlice::<Lsb0, u16>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl16_lb16_empty() { BitSlice::<Lsb0, u16>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl16_lb32_empty() { BitSlice::<Lsb0, u16>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_lb64_empty() { BitSlice::<Lsb0, u16>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl32_ll08_empty() { BitSlice::<Lsb0, u32>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl32_ll16_empty() { BitSlice::<Lsb0, u32>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl32_ll32_empty() { BitSlice::<Lsb0, u32>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_ll64_empty() { BitSlice::<Lsb0, u32>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl32_lb08_empty() { BitSlice::<Lsb0, u32>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl32_lb16_empty() { BitSlice::<Lsb0, u32>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl32_lb32_empty() { BitSlice::<Lsb0, u32>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_lb64_empty() { BitSlice::<Lsb0, u32>::empty().load_be::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll08_empty() { BitSlice::<Lsb0, u64>::empty().load_le::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll16_empty() { BitSlice::<Lsb0, u64>::empty().load_le::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll32_empty() { BitSlice::<Lsb0, u64>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll64_empty() { BitSlice::<Lsb0, u64>::empty().load_le::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb08_empty() { BitSlice::<Lsb0, u64>::empty().load_be::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb16_empty() { BitSlice::<Lsb0, u64>::empty().load_be::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb32_empty() { BitSlice::<Lsb0, u64>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb64_empty() { BitSlice::<Lsb0, u64>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm08_ll08_empty() { BitSlice::<Msb0, u8>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm08_ll16_empty() { BitSlice::<Msb0, u8>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm08_ll32_empty() { BitSlice::<Msb0, u8>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_ll64_empty() { BitSlice::<Msb0, u8>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm08_lb08_empty() { BitSlice::<Msb0, u8>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm08_lb16_empty() { BitSlice::<Msb0, u8>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm08_lb32_empty() { BitSlice::<Msb0, u8>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_lb64_empty() { BitSlice::<Msb0, u8>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm16_ll08_empty() { BitSlice::<Msb0, u16>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm16_ll16_empty() { BitSlice::<Msb0, u16>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm16_ll32_empty() { BitSlice::<Msb0, u16>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_ll64_empty() { BitSlice::<Msb0, u16>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm16_lb08_empty() { BitSlice::<Msb0, u16>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm16_lb16_empty() { BitSlice::<Msb0, u16>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm16_lb32_empty() { BitSlice::<Msb0, u16>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_lb64_empty() { BitSlice::<Msb0, u16>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm32_ll08_empty() { BitSlice::<Msb0, u32>::empty().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm32_ll16_empty() { BitSlice::<Msb0, u32>::empty().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm32_ll32_empty() { BitSlice::<Msb0, u32>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_ll64_empty() { BitSlice::<Msb0, u32>::empty().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm32_lb08_empty() { BitSlice::<Msb0, u32>::empty().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm32_lb16_empty() { BitSlice::<Msb0, u32>::empty().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm32_lb32_empty() { BitSlice::<Msb0, u32>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_lb64_empty() { BitSlice::<Msb0, u32>::empty().load_be::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll08_empty() { BitSlice::<Msb0, u64>::empty().load_le::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll16_empty() { BitSlice::<Msb0, u64>::empty().load_le::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll32_empty() { BitSlice::<Msb0, u64>::empty().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll64_empty() { BitSlice::<Msb0, u64>::empty().load_le::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb08_empty() { BitSlice::<Msb0, u64>::empty().load_be::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb16_empty() { BitSlice::<Msb0, u64>::empty().load_be::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb32_empty() { BitSlice::<Msb0, u64>::empty().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb64_empty() { BitSlice::<Msb0, u64>::empty().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl08_ll08_full() { [0u8; 2].bits::<Lsb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl08_ll16_full() { [0u8; 3].bits::<Lsb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl08_ll32_full() { [0u8; 5].bits::<Lsb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_ll64_full() { [0u8; 9].bits::<Lsb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl08_lb08_full() { [0u8; 2].bits::<Lsb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl08_lb16_full() { [0u8; 3].bits::<Lsb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl08_lb32_full() { [0u8; 5].bits::<Lsb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_lb64_full() { [0u8; 9].bits::<Lsb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl16_ll08_full() { [0u16; 1].bits::<Lsb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl16_ll16_full() { [0u16; 2].bits::<Lsb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl16_ll32_full() { [0u16; 3].bits::<Lsb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_ll64_full() { [0u16; 35].bits::<Lsb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl16_lb08_full() { [0u16; 1].bits::<Lsb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl16_lb16_full() { [0u16; 2].bits::<Lsb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl16_lb32_full() { [0u16; 3].bits::<Lsb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_lb64_full() { [0u16; 5].bits::<Lsb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl32_ll08_full() { [0u32; 1].bits::<Lsb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsl32_ll16_full() { [0u32; 1].bits::<Lsb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsl32_ll32_full() { [0u32; 2].bits::<Lsb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_ll64_full() { [0u32; 3].bits::<Lsb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsl32_lb08_full() { [0u32; 1].bits::<Lsb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsl32_lb16_full() { [0u32; 1].bits::<Lsb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsl32_lb32_full() { [0u32; 2].bits::<Lsb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_lb64_full() { [0u32; 3].bits::<Lsb0>().load_be::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll08_full() { [0u64; 1].bits::<Lsb0>().load_le::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll16_full() { [0u64; 1].bits::<Lsb0>().load_le::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll32_full() { [0u64; 1].bits::<Lsb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_ll64_full() { [0u64; 2].bits::<Lsb0>().load_le::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb08_full() { [0u64; 1].bits::<Lsb0>().load_be::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb16_full() { [0u64; 1].bits::<Lsb0>().load_be::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb32_full() { [0u64; 1].bits::<Lsb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_lb64_full() { [0u64; 2].bits::<Lsb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm08_ll08_full() { [0u8; 2].bits::<Msb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm08_ll16_full() { [0u8; 3].bits::<Msb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm08_ll32_full() { [0u8; 5].bits::<Msb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_ll64_full() { [0u8; 9].bits::<Msb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm08_lb08_full() { [0u8; 2].bits::<Msb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm08_lb16_full() { [0u8; 3].bits::<Msb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm08_lb32_full() { [0u8; 5].bits::<Msb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_lb64_full() { [0u8; 9].bits::<Msb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm16_ll08_full() { [0u16; 1].bits::<Msb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm16_ll16_full() { [0u16; 2].bits::<Msb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm16_ll32_full() { [0u16; 3].bits::<Msb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_ll64_full() { [0u16; 5].bits::<Msb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm16_lb08_full() { [0u16; 1].bits::<Msb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm16_lb16_full() { [0u16; 2].bits::<Msb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm16_lb32_full() { [0u16; 3].bits::<Msb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_lb64_full() { [0u16; 5].bits::<Msb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsm32_ll08_full() { [0u32; 1].bits::<Msb0>().load_le::<u8>(); }

#[test]
#[should_panic]
fn bsm32_ll16_full() { [0u32; 1].bits::<Msb0>().load_le::<u16>(); }

#[test]
#[should_panic]
fn bsm32_ll32_full() { [0u32; 2].bits::<Msb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_ll64_full() { [0u32; 3].bits::<Msb0>().load_le::<u64>(); }

#[test]
#[should_panic]
fn bsm32_lb08_full() { [0u32; 1].bits::<Msb0>().load_be::<u8>(); }

#[test]
#[should_panic]
fn bsm32_lb16_full() { [0u32; 1].bits::<Msb0>().load_be::<u16>(); }

#[test]
#[should_panic]
fn bsm32_lb32_full() { [0u32; 2].bits::<Msb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_lb64_full() { [0u32; 3].bits::<Msb0>().load_be::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll08_full() { [0u64; 1].bits::<Msb0>().load_le::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll16_full() { [0u64; 1].bits::<Msb0>().load_le::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll32_full() { [0u64; 1].bits::<Msb0>().load_le::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_ll64_full() { [0u64; 2].bits::<Msb0>().load_le::<u64>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb08_full() { [0u64; 1].bits::<Msb0>().load_be::<u8>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb16_full() { [0u64; 1].bits::<Msb0>().load_be::<u16>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb32_full() { [0u64; 1].bits::<Msb0>().load_be::<u32>(); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_lb64_full() { [0u64; 2].bits::<Msb0>().load_be::<u64>(); }

#[test]
#[should_panic]
fn bsl08_sl08_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl08_sl16_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl08_sl32_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_sl64_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl08_sb08_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl08_sb16_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl08_sb32_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_sb64_empty() { BitSlice::<Lsb0, u8>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsl16_sl08_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl16_sl16_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl16_sl32_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_sl64_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl16_sb08_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl16_sb16_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl16_sb32_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_sb64_empty() { BitSlice::<Lsb0, u16>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsl32_sl08_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl32_sl16_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl32_sl32_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_sl64_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl32_sb08_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl32_sb16_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl32_sb32_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_sb64_empty() { BitSlice::<Lsb0, u32>::empty_mut().store_be::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl08_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_le::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl16_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_le::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl32_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl64_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_le::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb08_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_be::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb16_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_be::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb32_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb64_empty() { BitSlice::<Lsb0, u64>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm08_sl08_empty() { BitSlice::<Msb0, u8>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm08_sl16_empty() { BitSlice::<Msb0, u8>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm08_sl32_empty() { BitSlice::<Msb0, u8>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_sl64_empty() { BitSlice::<Msb0, u8>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm08_sb08_empty() { BitSlice::<Msb0, u8>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm08_sb16_empty() { BitSlice::<Msb0, u8>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm08_sb32_empty() { BitSlice::<Msb0, u8>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_sb64_empty() { BitSlice::<Msb0, u8>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm16_sl08_empty() { BitSlice::<Msb0, u16>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm16_sl16_empty() { BitSlice::<Msb0, u16>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm16_sl32_empty() { BitSlice::<Msb0, u16>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_sl64_empty() { BitSlice::<Msb0, u16>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm16_sb08_empty() { BitSlice::<Msb0, u16>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm16_sb16_empty() { BitSlice::<Msb0, u16>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm16_sb32_empty() { BitSlice::<Msb0, u16>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_sb64_empty() { BitSlice::<Msb0, u16>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm32_sl08_empty() { BitSlice::<Msb0, u32>::empty_mut().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm32_sl16_empty() { BitSlice::<Msb0, u32>::empty_mut().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm32_sl32_empty() { BitSlice::<Msb0, u32>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_sl64_empty() { BitSlice::<Msb0, u32>::empty_mut().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm32_sb08_empty() { BitSlice::<Msb0, u32>::empty_mut().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm32_sb16_empty() { BitSlice::<Msb0, u32>::empty_mut().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm32_sb32_empty() { BitSlice::<Msb0, u32>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_sb64_empty() { BitSlice::<Msb0, u32>::empty_mut().store_be::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl08_empty() { BitSlice::<Msb0, u64>::empty_mut().store_le::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl16_empty() { BitSlice::<Msb0, u64>::empty_mut().store_le::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl32_empty() { BitSlice::<Msb0, u64>::empty_mut().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl64_empty() { BitSlice::<Msb0, u64>::empty_mut().store_le::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb08_empty() { BitSlice::<Msb0, u64>::empty_mut().store_be::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb16_empty() { BitSlice::<Msb0, u64>::empty_mut().store_be::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb32_empty() { BitSlice::<Msb0, u64>::empty_mut().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb64_empty() { BitSlice::<Msb0, u64>::empty_mut().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsl08_sl08_full() { [0u8; 2].bits_mut::<Lsb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl08_sl16_full() { [0u8; 3].bits_mut::<Lsb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl08_sl32_full() { [0u8; 5].bits_mut::<Lsb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_sl64_full() { [0u8; 9].bits_mut::<Lsb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl08_sb08_full() { [0u8; 2].bits_mut::<Lsb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl08_sb16_full() { [0u8; 3].bits_mut::<Lsb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl08_sb32_full() { [0u8; 5].bits_mut::<Lsb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl08_sb64_full() { [0u8; 9].bits_mut::<Lsb0>().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsl16_sl08_full() { [0u16; 1].bits_mut::<Lsb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl16_sl16_full() { [0u16; 2].bits_mut::<Lsb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl16_sl32_full() { [0u16; 3].bits_mut::<Lsb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_sl64_full() { [0u16; 5].bits_mut::<Lsb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl16_sb08_full() { [0u16; 1].bits_mut::<Lsb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl16_sb16_full() { [0u16; 2].bits_mut::<Lsb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl16_sb32_full() { [0u16; 3].bits_mut::<Lsb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl16_sb64_full() { [0u16; 5].bits_mut::<Lsb0>().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsl32_sl08_full() { [0u32; 1].bits_mut::<Lsb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsl32_sl16_full() { [0u32; 1].bits_mut::<Lsb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsl32_sl32_full() { [0u32; 2].bits_mut::<Lsb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_sl64_full() { [0u32; 3].bits_mut::<Lsb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsl32_sb08_full() { [0u32; 1].bits_mut::<Lsb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsl32_sb16_full() { [0u32; 1].bits_mut::<Lsb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsl32_sb32_full() { [0u32; 2].bits_mut::<Lsb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl32_sb64_full() { [0u32; 3].bits_mut::<Lsb0>().store_be::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl08_full() { [0u64; 1].bits_mut::<Lsb0>().store_le::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl16_full() { [0u64; 1].bits_mut::<Lsb0>().store_le::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl32_full() { [0u64; 1].bits_mut::<Lsb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sl64_full() { [0u64; 2].bits_mut::<Lsb0>().store_le::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb08_full() { [0u64; 1].bits_mut::<Lsb0>().store_be::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb16_full() { [0u64; 1].bits_mut::<Lsb0>().store_be::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb32_full() { [0u64; 1].bits_mut::<Lsb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsl64_sb64_full() { [0u64; 2].bits_mut::<Lsb0>().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm08_sl08_full() { [0u8; 2].bits_mut::<Msb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm08_sl16_full() { [0u8; 3].bits_mut::<Msb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm08_sl32_full() { [0u8; 5].bits_mut::<Msb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_sl64_full() { [0u8; 9].bits_mut::<Msb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm08_sb08_full() { [0u8; 2].bits_mut::<Msb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm08_sb16_full() { [0u8; 3].bits_mut::<Msb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm08_sb32_full() { [0u8; 5].bits_mut::<Msb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm08_sb64_full() { [0u8; 9].bits_mut::<Msb0>().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm16_sl08_full() { [0u16; 1].bits_mut::<Msb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm16_sl16_full() { [0u16; 2].bits_mut::<Msb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm16_sl32_full() { [0u16; 3].bits_mut::<Msb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_sl64_full() { [0u16; 5].bits_mut::<Msb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm16_sb08_full() { [0u16; 1].bits_mut::<Msb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm16_sb16_full() { [0u16; 2].bits_mut::<Msb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm16_sb32_full() { [0u16; 3].bits_mut::<Msb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm16_sb64_full() { [0u16; 5].bits_mut::<Msb0>().store_be::<u64>(0); }

#[test]
#[should_panic]
fn bsm32_sl08_full() { [0u32; 1].bits_mut::<Msb0>().store_le::<u8>(0); }

#[test]
#[should_panic]
fn bsm32_sl16_full() { [0u32; 1].bits_mut::<Msb0>().store_le::<u16>(0); }

#[test]
#[should_panic]
fn bsm32_sl32_full() { [0u32; 2].bits_mut::<Msb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_sl64_full() { [0u32; 3].bits_mut::<Msb0>().store_le::<u64>(0); }

#[test]
#[should_panic]
fn bsm32_sb08_full() { [0u32; 1].bits_mut::<Msb0>().store_be::<u8>(0); }

#[test]
#[should_panic]
fn bsm32_sb16_full() { [0u32; 1].bits_mut::<Msb0>().store_be::<u16>(0); }

#[test]
#[should_panic]
fn bsm32_sb32_full() { [0u32; 2].bits_mut::<Msb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm32_sb64_full() { [0u32; 3].bits_mut::<Msb0>().store_be::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl08_full() { [0u64; 1].bits_mut::<Msb0>().store_le::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl16_full() { [0u64; 1].bits_mut::<Msb0>().store_le::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl32_full() { [0u64; 1].bits_mut::<Msb0>().store_le::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sl64_full() { [0u64; 2].bits_mut::<Msb0>().store_le::<u64>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb08_full() { [0u64; 1].bits_mut::<Msb0>().store_be::<u8>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb16_full() { [0u64; 1].bits_mut::<Msb0>().store_be::<u16>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb32_full() { [0u64; 1].bits_mut::<Msb0>().store_be::<u32>(0); }

#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic]
fn bsm64_sb64_full() { [0u64; 2].bits_mut::<Msb0>().store_be::<u64>(0); }
