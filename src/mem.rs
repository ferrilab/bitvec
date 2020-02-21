/*! Memory description.

This module defines the properties of bare chunks of memory. It deals only with
register-type widths, and has no information on the means by which addressed
memory is accessed.
!*/

use core::mem;

use radium::marker::BitOps;

/** Describes properties of register types.

This trait describes raw memory, without any access modifiers. It provides
information about the width of a memory element and useful constants.
**/
pub trait BitMemory: BitOps + Sized {
	/// The width, in bits, of the memory element.
	const BITS: u8 = mem::size_of::<Self>() as u8 * 8;
	/// The number of bits required to hold a bit index into the element.
	const INDX: u8 = Self::BITS.trailing_zeros() as u8;
	/// The maximum value of a bit index for the element.
	const MASK: u8 = Self::BITS - 1;

	/// The element value with all bits low.
	const ZERO: Self;
	/// The element value with only the least significant bit high.
	const ONE: Self;
	/// The element value with all bits high.
	const ALL: Self;

	/// The element’s name.
	const TYPENAME: &'static str;

	/// Counts the number of bits in an eleent set to `1`.
	fn count_ones(self) -> usize;

	/// Counts the number of bits in an element set to `0`.
	fn count_zeros(self) -> usize;
}

/** Compute the number of elements required to store a number of bits.

# Parameters

- `bits`: The number of bits to store in an element `T` array.

# Returns

The number of elements `T` required to store `bits`.

Because this is a const function, when `bits` is a const-expr, this function can
be used in array types `[T; elts(len)]`.
**/
#[doc(hidden)]
pub const fn elts<T>(bits: usize) -> usize {
	let width = mem::size_of::<T>() * 8;
	bits / width + (bits % width != 0) as usize
}

macro_rules! memory {
	($($t:ty),* $(,)?) => { $(
		impl BitMemory for $t {
			const ZERO: Self = 0;
			const ONE: Self = 1;
			const ALL: Self = !0;

			const TYPENAME: &'static str = stringify!($t);

			fn count_ones(self) -> usize {
				Self::count_ones(self) as usize
			}

			fn count_zeros(self) -> usize {
				Self::count_zeros(self) as usize
			}
		}
	)* };
}

memory!(u8, u16, u32, usize);

#[cfg(target_pointer_width = "u64")]
memory!(u64);
