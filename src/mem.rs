/*! Descriptions of register types

This module describes the register types used to hold bare data. This module
governs the way the processor manipulates values held in registers, without
concern for interaction with memory locations.
!*/

use core::mem;

use funty::IsUnsigned;

use radium::marker::BitOps;

/** Description of a register type.

This trait provides information used for the manipulation of values in processor
registers, and the computation of the state of system memory. It has no bearing
on the behavior used to perform loads or stores between the processor and the
memory bus.

This trait cannot be implemented outside this crate.
**/
pub trait BitMemory: IsUnsigned + BitOps + seal::Sealed {
	/// The bit width of the register element.
	///
	/// `mem::size_of` returns the size in bytes, and bytes are always eight
	/// bits on architectures Rust targets.
	const BITS: u8 = mem::size_of::<Self>() as u8 * 8;
	/// The number of bits required to store an index in the range `0 .. BITS`.
	const INDX: u8 = Self::BITS.trailing_zeros() as u8;
	/// A mask over all bits that can be used as an index within the element.
	const MASK: u8 = Self::BITS - 1;

	/// The value with only its least significant bit set to `1`.
	const ONE: Self;
	/// The value with all of its bits set to `1`.
	const ALL: Self;
}

macro_rules! memory {
	($($t:ty),+ $(,)?) => { $(
		impl BitMemory for $t {
			const ONE: Self = 1;
			const ALL: Self = !0;
		}
		impl seal::Sealed for $t {}
	)+ };
}

memory!(u8, u16, u32, usize);

#[cfg(target_pointer_width = "64")]
memory!(u64);

/** Computes the number of elements required to store some number of bits.

# Parameters

- `bits`: The number of bits to store in a `[T]` array.

# Returns

The number of elements `T` required to store `bits`.

As this is a const function, when `bits` is a constant expression, this can be
used to compute the size of an array type `[T; elts(bits)]`.
**/
#[doc(hidden)]
pub const fn elts<T>(bits: usize) -> usize {
	let width = mem::size_of::<T>() * 8;
	bits / width + (bits % width != 0) as usize
}

/** Tests that a type is aligned to its size.

This property is not necessarily true for all integers; for instance, `u64` on
32-bit x86 is permitted to be 4-byte-aligned. `bitvec` requires this property to
hold for the pointer representation to correctly function.

# Type Parameters

- `T`: A type whose alignment and size are to be compared

# Returns

`0` if the alignment matches the size; `1` if they differ
**/
#[doc(hidden)]
pub(crate) const fn aligned_to_size<T>() -> usize {
	(mem::align_of::<T>() != mem::size_of::<T>()) as usize
}

#[doc(hidden)]
pub(crate) const fn cmp_layout<A, B>() -> usize {
	(mem::align_of::<A>() != mem::align_of::<B>()) as usize
		+ (mem::size_of::<A>() != mem::size_of::<B>()) as usize
}

#[doc(hidden)]
mod seal {
	#[doc(hidden)]
	pub trait Sealed {}
}
