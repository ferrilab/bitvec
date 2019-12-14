// Not publiC API
//
// Helper methods and re-exports used by macros.

use core::mem;
use crate::store::BitStore;
use crate::indices::BitIdx;

// Not public API
pub const fn word_len<T>(bit_len: usize) -> usize {
	let width = mem::size_of::<T>() * 8;
	(bit_len + width - 1) / width
}

// Not public API
pub const fn u8_from_le_bits(
	a: bool,
	b: bool,
	c: bool,
	d: bool,
	e: bool,
	f: bool,
	g: bool,
	h: bool,
) -> u8 {
	(a as u8)
		| ((b as u8) << 1)
		| ((c as u8) << 2)
		| ((d as u8) << 3)
		| ((e as u8) << 4)
		| ((f as u8) << 5)
		| ((g as u8) << 6)
		| ((h as u8) << 7)
}

// Not public API
pub const fn u8_from_be_bits(
	a: bool,
	b: bool,
	c: bool,
	d: bool,
	e: bool,
	f: bool,
	g: bool,
	h: bool,
) -> u8 {
	(h as u8)
		| ((g as u8) << 1)
		| ((f as u8) << 2)
		| ((e as u8) << 3)
		| ((d as u8) << 4)
		| ((c as u8) << 5)
		| ((b as u8) << 6)
		| ((a as u8) << 7)
}

#[cfg(target_endian = "little")]
pub use self::u8_from_le_bits as u8_from_local_bits;

#[cfg(target_endian = "big")]
pub use self::u8_from_be_bits as u8_from_local_bits;

// Not public API
pub unsafe fn bitidx_new_unchecked<T: BitStore>(idx: u8) -> BitIdx<T> {
	BitIdx::new_unchecked(idx)
}
