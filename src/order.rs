/*! Bit Ordering

`bitvec` structures are parametric over any ordering of bits within an element.
The `BitOrder` trait maps a cursor position (indicated by the `BitIdx` type) to an
electrical position (indicated by the `BitPos` type) within that element, and
also defines the order of traversal over an element.

The only requirement on implementors of `BitOrder` is that the transform function
from cursor (`BitIdx`) to position (`BitPos`) is *total* (every integer in the
domain `0 .. T::BITS` is used) and *unique* (each cursor maps to one and only
one position, and each position is mapped by one and only one cursor).
Contiguity is not required.

`BitOrder` is a stateless trait, and implementors should be zero-sized types.
!*/

use crate::{
	indices::{
		BitIdx,
		BitMask,
		BitPos,
		Indexable,
	},
	store::BitStore,
};

/// Traverses an element from `MSbit` to `LSbit`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Msb0;

/// Traverses an element from `LSbit` to `MSbit`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Lsb0;

/** An ordering over an element.

# Usage

`bitvec` structures store and operate on semantic counts, not bit positions. The
`BitOrder::at` function takes a semantic ordering, `BitIdx`, and produces an
electrical position, `BitPos`.
**/
pub trait BitOrder {
	/// Name of the ordering type, for use in text display.
	const TYPENAME: &'static str;

	/// Translate a semantic bit index into an electrical bit position.
	///
	/// # Parameters
	///
	/// - `place`: The semantic bit value.
	///
	/// # Returns
	///
	/// - A concrete position. This value can be used for shifting and masking
	///   to extract a bit from an element. This must be in the domain
	///   `0 .. T::BITS`.
	///
	/// # Type Parameters
	///
	/// - `T: BitStore`: The storage type for which the position will be
	///   calculated.
	///
	/// # Invariants
	///
	/// The function **must** be *total* for the domain `.. T::BITS`. All values
	/// in this domain are valid indices that the library will pass to it, and
	/// which this function must satisfy.
	///
	/// The function **must** be *bijective* over the domain `.. T::BITS`. All
	/// input values in this domain must have one and only one correpsonding
	/// output, which must also be in this domain.
	///
	/// The function *may* support input in the domain `T::BITS ..`. The library
	/// will not produce any values in this domain as input indices. The
	/// function **must not** produce output in the domain `T::BITS ..`. It must
	/// choose between panicking, or producing an output in `.. T::BITS`. The
	/// reduction in domain from `T::BITS ..` to `.. T::BITS` removes the
	/// requirement for inputs in `T::BITS ..` to have unique outputs in
	/// `.. T::BITS`.
	///
	/// This function **must** be *pure*. Calls which have the same input must
	/// produce the same output. This invariant is only required to be upheld
	/// for the lifetime of all data structures which use an implementor. The
	/// behavior of the function *may* be modified after all existing dependent
	/// data structures are destroyed and before any new dependent data
	/// structures are created.
	///
	/// # Non-Invariants
	///
	/// This function is *not* required to be stateless. It *may* refer to
	/// immutable global state, subject to the purity requirement on lifetimes.
	///
	/// # Safety
	///
	/// This function requires that the output be in the domain `.. T::BITS`.
	/// Implementors must uphold this themselves. Outputs in the domain
	/// `T::BITS ..` will induce panics elsewhere in the library.
	fn at<T>(place: BitIdx<T>) -> BitPos<T>
	where T: BitStore;

	/// Translate a semantic bit index into an electrical bit mask.
	///
	/// This is an optional function; a default implementation is provided for
	/// you.
	///
	/// The default implementation of this function calls `Self::at` to produce
	/// an electrical position, then turns that into a bitmask by setting the
	/// `n`th bit more significant than the least significant bit of the
	/// element. `BitOrder` implementations may choose to provide a faster mask
	/// production here, but they must satisfy the invariants listed below.
	///
	/// # Parameters
	///
	/// - `place`: A semantic bit index into a memory element.
	///
	/// # Returns
	///
	/// A one-hot encoding of the provided `BitOrder`’s electrical position in the
	/// `T` element.
	///
	/// # Type Parameters
	///
	/// - `T`: The storage type for which the mask will be calculated. The mask
	///   must also be this type, as it will be applied to an element of `T` in
	///   order to set, clear, or test a single bit.
	///
	/// # Invariants
	///
	/// A one-hot encoding means that there is exactly one bit set in the
	/// produced value. It must be equivalent to `1 << *Self::at(place)`.
	///
	/// As with `at`, this function must produce a unique mapping from each
	/// legal index in the `T` domain to a one-hot value of `T`.
	///
	/// # Safety
	///
	/// This function requires that the output is always a one-hot value. It is
	/// illegal to produce a value with more than one bit set, and doing so will
	/// cause uncontrolled side effects.
	fn mask<T>(place: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		let place = Self::at::<T>(place);
		debug_assert!(
			*place < T::BITS,
			"Bit position {} must not exceed the type width {}",
			*place,
			T::BITS,
		);
		unsafe { BitMask::new_unchecked(T::from(1) << *place) }
	}
}

impl BitOrder for Msb0 {
	const TYPENAME: &'static str = "Msb0";

	/// Maps a semantic count to a concrete position.
	///
	/// `Msb0` order moves from `MSbit` first to `LSbit` last.
	fn at<T>(place: BitIdx<T>) -> BitPos<T>
	where T: BitStore {
		(T::MASK - *place).pos()
	}

	fn mask<T>(place: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		//  Set the MSbit, then shift it down. The left expr is const-folded.
		//  Note: this is not equivalent to `1 << (mask - place)`, because
		//  that requires a subtraction every time, but the expression below is
		//  only a single right-shift.
		unsafe { BitMask::new_unchecked((T::from(1) << T::MASK) >> *place) }
	}
}

impl BitOrder for Lsb0 {
	const TYPENAME: &'static str = "Lsb0";

	/// Maps a semantic count to a concrete position.
	///
	/// `Lsb0` order moves from `LSbit` first to `MSbit` last.
	fn at<T>(place: BitIdx<T>) -> BitPos<T>
	where T: BitStore {
		(*place).pos()
	}

	fn mask<T>(place: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		//  Set the LSbit, then shift it up.
		unsafe { BitMask::new_unchecked(T::from(1) << *place) }
	}
}

/** A default bit ordering.

The target has big-endian byte ordering, so the default bit ordering is set to
big-endian as well, as a convenience. These two orderings are not related.
**/
#[cfg(target_endian = "big")]
pub type Local = Msb0;

/** A default bit ordering.

The target has little-endian byte ordering, so the default bit ordering is set
to little-endian as well, as a convenience. These two orderings are not related.
**/
#[cfg(target_endian = "little")]
pub type Local = Lsb0;

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_fail!("This architecture is currently not supported. File an issue at https://github.com/myrrlyn/bitvec");

#[cfg(test)]
#[allow(clippy::cognitive_complexity)] // Permit large test functions
mod tests {
	use super::*;

	#[test]
	fn be_u8_range() {
		assert_eq!(Msb0::at::<u8>(0u8.idx()), 7u8.pos());
		assert_eq!(Msb0::at::<u8>(1u8.idx()), 6u8.pos());
		assert_eq!(Msb0::at::<u8>(2u8.idx()), 5u8.pos());
		assert_eq!(Msb0::at::<u8>(3u8.idx()), 4u8.pos());
		assert_eq!(Msb0::at::<u8>(4u8.idx()), 3u8.pos());
		assert_eq!(Msb0::at::<u8>(5u8.idx()), 2u8.pos());
		assert_eq!(Msb0::at::<u8>(6u8.idx()), 1u8.pos());
		assert_eq!(Msb0::at::<u8>(7u8.idx()), 0u8.pos());
	}

	#[test]
	fn be_u16_range() {
		assert_eq!(Msb0::at::<u16>(0u8.idx()), 15u8.pos());
		assert_eq!(Msb0::at::<u16>(1u8.idx()), 14u8.pos());
		assert_eq!(Msb0::at::<u16>(2u8.idx()), 13u8.pos());
		assert_eq!(Msb0::at::<u16>(3u8.idx()), 12u8.pos());
		assert_eq!(Msb0::at::<u16>(4u8.idx()), 11u8.pos());
		assert_eq!(Msb0::at::<u16>(5u8.idx()), 10u8.pos());
		assert_eq!(Msb0::at::<u16>(6u8.idx()), 9u8.pos());
		assert_eq!(Msb0::at::<u16>(7u8.idx()), 8u8.pos());
		assert_eq!(Msb0::at::<u16>(8u8.idx()), 7u8.pos());
		assert_eq!(Msb0::at::<u16>(9u8.idx()), 6u8.pos());
		assert_eq!(Msb0::at::<u16>(10u8.idx()), 5u8.pos());
		assert_eq!(Msb0::at::<u16>(11u8.idx()), 4u8.pos());
		assert_eq!(Msb0::at::<u16>(12u8.idx()), 3u8.pos());
		assert_eq!(Msb0::at::<u16>(13u8.idx()), 2u8.pos());
		assert_eq!(Msb0::at::<u16>(14u8.idx()), 1u8.pos());
		assert_eq!(Msb0::at::<u16>(15u8.idx()), 0u8.pos());
	}

	#[test]
	fn be_u32_range() {
		assert_eq!(Msb0::at::<u32>(0u8.idx()), 31u8.pos());
		assert_eq!(Msb0::at::<u32>(1u8.idx()), 30u8.pos());
		assert_eq!(Msb0::at::<u32>(2u8.idx()), 29u8.pos());
		assert_eq!(Msb0::at::<u32>(3u8.idx()), 28u8.pos());
		assert_eq!(Msb0::at::<u32>(4u8.idx()), 27u8.pos());
		assert_eq!(Msb0::at::<u32>(5u8.idx()), 26u8.pos());
		assert_eq!(Msb0::at::<u32>(6u8.idx()), 25u8.pos());
		assert_eq!(Msb0::at::<u32>(7u8.idx()), 24u8.pos());
		assert_eq!(Msb0::at::<u32>(8u8.idx()), 23u8.pos());
		assert_eq!(Msb0::at::<u32>(9u8.idx()), 22u8.pos());
		assert_eq!(Msb0::at::<u32>(10u8.idx()), 21u8.pos());
		assert_eq!(Msb0::at::<u32>(11u8.idx()), 20u8.pos());
		assert_eq!(Msb0::at::<u32>(12u8.idx()), 19u8.pos());
		assert_eq!(Msb0::at::<u32>(13u8.idx()), 18u8.pos());
		assert_eq!(Msb0::at::<u32>(14u8.idx()), 17u8.pos());
		assert_eq!(Msb0::at::<u32>(15u8.idx()), 16u8.pos());
		assert_eq!(Msb0::at::<u32>(16u8.idx()), 15u8.pos());
		assert_eq!(Msb0::at::<u32>(17u8.idx()), 14u8.pos());
		assert_eq!(Msb0::at::<u32>(18u8.idx()), 13u8.pos());
		assert_eq!(Msb0::at::<u32>(19u8.idx()), 12u8.pos());
		assert_eq!(Msb0::at::<u32>(20u8.idx()), 11u8.pos());
		assert_eq!(Msb0::at::<u32>(21u8.idx()), 10u8.pos());
		assert_eq!(Msb0::at::<u32>(22u8.idx()), 9u8.pos());
		assert_eq!(Msb0::at::<u32>(23u8.idx()), 8u8.pos());
		assert_eq!(Msb0::at::<u32>(24u8.idx()), 7u8.pos());
		assert_eq!(Msb0::at::<u32>(25u8.idx()), 6u8.pos());
		assert_eq!(Msb0::at::<u32>(26u8.idx()), 5u8.pos());
		assert_eq!(Msb0::at::<u32>(27u8.idx()), 4u8.pos());
		assert_eq!(Msb0::at::<u32>(28u8.idx()), 3u8.pos());
		assert_eq!(Msb0::at::<u32>(29u8.idx()), 2u8.pos());
		assert_eq!(Msb0::at::<u32>(30u8.idx()), 1u8.pos());
		assert_eq!(Msb0::at::<u32>(31u8.idx()), 0u8.pos());
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn be_u64_range() {
		assert_eq!(Msb0::at::<u64>(0u8.idx()), 63u8.pos());
		assert_eq!(Msb0::at::<u64>(1u8.idx()), 62u8.pos());
		assert_eq!(Msb0::at::<u64>(2u8.idx()), 61u8.pos());
		assert_eq!(Msb0::at::<u64>(3u8.idx()), 60u8.pos());
		assert_eq!(Msb0::at::<u64>(4u8.idx()), 59u8.pos());
		assert_eq!(Msb0::at::<u64>(5u8.idx()), 58u8.pos());
		assert_eq!(Msb0::at::<u64>(6u8.idx()), 57u8.pos());
		assert_eq!(Msb0::at::<u64>(7u8.idx()), 56u8.pos());
		assert_eq!(Msb0::at::<u64>(8u8.idx()), 55u8.pos());
		assert_eq!(Msb0::at::<u64>(9u8.idx()), 54u8.pos());
		assert_eq!(Msb0::at::<u64>(10u8.idx()), 53u8.pos());
		assert_eq!(Msb0::at::<u64>(11u8.idx()), 52u8.pos());
		assert_eq!(Msb0::at::<u64>(12u8.idx()), 51u8.pos());
		assert_eq!(Msb0::at::<u64>(13u8.idx()), 50u8.pos());
		assert_eq!(Msb0::at::<u64>(14u8.idx()), 49u8.pos());
		assert_eq!(Msb0::at::<u64>(15u8.idx()), 48u8.pos());
		assert_eq!(Msb0::at::<u64>(16u8.idx()), 47u8.pos());
		assert_eq!(Msb0::at::<u64>(17u8.idx()), 46u8.pos());
		assert_eq!(Msb0::at::<u64>(18u8.idx()), 45u8.pos());
		assert_eq!(Msb0::at::<u64>(19u8.idx()), 44u8.pos());
		assert_eq!(Msb0::at::<u64>(20u8.idx()), 43u8.pos());
		assert_eq!(Msb0::at::<u64>(21u8.idx()), 42u8.pos());
		assert_eq!(Msb0::at::<u64>(22u8.idx()), 41u8.pos());
		assert_eq!(Msb0::at::<u64>(23u8.idx()), 40u8.pos());
		assert_eq!(Msb0::at::<u64>(24u8.idx()), 39u8.pos());
		assert_eq!(Msb0::at::<u64>(25u8.idx()), 38u8.pos());
		assert_eq!(Msb0::at::<u64>(26u8.idx()), 37u8.pos());
		assert_eq!(Msb0::at::<u64>(27u8.idx()), 36u8.pos());
		assert_eq!(Msb0::at::<u64>(28u8.idx()), 35u8.pos());
		assert_eq!(Msb0::at::<u64>(29u8.idx()), 34u8.pos());
		assert_eq!(Msb0::at::<u64>(30u8.idx()), 33u8.pos());
		assert_eq!(Msb0::at::<u64>(31u8.idx()), 32u8.pos());
		assert_eq!(Msb0::at::<u64>(32u8.idx()), 31u8.pos());
		assert_eq!(Msb0::at::<u64>(33u8.idx()), 30u8.pos());
		assert_eq!(Msb0::at::<u64>(34u8.idx()), 29u8.pos());
		assert_eq!(Msb0::at::<u64>(35u8.idx()), 28u8.pos());
		assert_eq!(Msb0::at::<u64>(36u8.idx()), 27u8.pos());
		assert_eq!(Msb0::at::<u64>(37u8.idx()), 26u8.pos());
		assert_eq!(Msb0::at::<u64>(38u8.idx()), 25u8.pos());
		assert_eq!(Msb0::at::<u64>(39u8.idx()), 24u8.pos());
		assert_eq!(Msb0::at::<u64>(40u8.idx()), 23u8.pos());
		assert_eq!(Msb0::at::<u64>(41u8.idx()), 22u8.pos());
		assert_eq!(Msb0::at::<u64>(42u8.idx()), 21u8.pos());
		assert_eq!(Msb0::at::<u64>(43u8.idx()), 20u8.pos());
		assert_eq!(Msb0::at::<u64>(44u8.idx()), 19u8.pos());
		assert_eq!(Msb0::at::<u64>(45u8.idx()), 18u8.pos());
		assert_eq!(Msb0::at::<u64>(46u8.idx()), 17u8.pos());
		assert_eq!(Msb0::at::<u64>(47u8.idx()), 16u8.pos());
		assert_eq!(Msb0::at::<u64>(48u8.idx()), 15u8.pos());
		assert_eq!(Msb0::at::<u64>(49u8.idx()), 14u8.pos());
		assert_eq!(Msb0::at::<u64>(50u8.idx()), 13u8.pos());
		assert_eq!(Msb0::at::<u64>(51u8.idx()), 12u8.pos());
		assert_eq!(Msb0::at::<u64>(52u8.idx()), 11u8.pos());
		assert_eq!(Msb0::at::<u64>(53u8.idx()), 10u8.pos());
		assert_eq!(Msb0::at::<u64>(54u8.idx()), 9u8.pos());
		assert_eq!(Msb0::at::<u64>(55u8.idx()), 8u8.pos());
		assert_eq!(Msb0::at::<u64>(56u8.idx()), 7u8.pos());
		assert_eq!(Msb0::at::<u64>(57u8.idx()), 6u8.pos());
		assert_eq!(Msb0::at::<u64>(58u8.idx()), 5u8.pos());
		assert_eq!(Msb0::at::<u64>(59u8.idx()), 4u8.pos());
		assert_eq!(Msb0::at::<u64>(60u8.idx()), 3u8.pos());
		assert_eq!(Msb0::at::<u64>(61u8.idx()), 2u8.pos());
		assert_eq!(Msb0::at::<u64>(62u8.idx()), 1u8.pos());
		assert_eq!(Msb0::at::<u64>(63u8.idx()), 0u8.pos());
	}

	#[test]
	fn le_u8_range() {
		assert_eq!(Lsb0::at::<u8>(0u8.idx()), 0u8.pos());
		assert_eq!(Lsb0::at::<u8>(1u8.idx()), 1u8.pos());
		assert_eq!(Lsb0::at::<u8>(2u8.idx()), 2u8.pos());
		assert_eq!(Lsb0::at::<u8>(3u8.idx()), 3u8.pos());
		assert_eq!(Lsb0::at::<u8>(4u8.idx()), 4u8.pos());
		assert_eq!(Lsb0::at::<u8>(5u8.idx()), 5u8.pos());
		assert_eq!(Lsb0::at::<u8>(6u8.idx()), 6u8.pos());
		assert_eq!(Lsb0::at::<u8>(7u8.idx()), 7u8.pos());
	}

	#[test]
	fn le_u16_range() {
		assert_eq!(Lsb0::at::<u16>(0u8.idx()), 0u8.pos());
		assert_eq!(Lsb0::at::<u16>(1u8.idx()), 1u8.pos());
		assert_eq!(Lsb0::at::<u16>(2u8.idx()), 2u8.pos());
		assert_eq!(Lsb0::at::<u16>(3u8.idx()), 3u8.pos());
		assert_eq!(Lsb0::at::<u16>(4u8.idx()), 4u8.pos());
		assert_eq!(Lsb0::at::<u16>(5u8.idx()), 5u8.pos());
		assert_eq!(Lsb0::at::<u16>(6u8.idx()), 6u8.pos());
		assert_eq!(Lsb0::at::<u16>(7u8.idx()), 7u8.pos());
		assert_eq!(Lsb0::at::<u16>(8u8.idx()), 8u8.pos());
		assert_eq!(Lsb0::at::<u16>(9u8.idx()), 9u8.pos());
		assert_eq!(Lsb0::at::<u16>(10u8.idx()), 10u8.pos());
		assert_eq!(Lsb0::at::<u16>(11u8.idx()), 11u8.pos());
		assert_eq!(Lsb0::at::<u16>(12u8.idx()), 12u8.pos());
		assert_eq!(Lsb0::at::<u16>(13u8.idx()), 13u8.pos());
		assert_eq!(Lsb0::at::<u16>(14u8.idx()), 14u8.pos());
		assert_eq!(Lsb0::at::<u16>(15u8.idx()), 15u8.pos());
	}

	#[test]
	fn le_u32_range() {
		assert_eq!(Lsb0::at::<u32>(0u8.idx()), 0u8.pos());
		assert_eq!(Lsb0::at::<u32>(1u8.idx()), 1u8.pos());
		assert_eq!(Lsb0::at::<u32>(2u8.idx()), 2u8.pos());
		assert_eq!(Lsb0::at::<u32>(3u8.idx()), 3u8.pos());
		assert_eq!(Lsb0::at::<u32>(4u8.idx()), 4u8.pos());
		assert_eq!(Lsb0::at::<u32>(5u8.idx()), 5u8.pos());
		assert_eq!(Lsb0::at::<u32>(6u8.idx()), 6u8.pos());
		assert_eq!(Lsb0::at::<u32>(7u8.idx()), 7u8.pos());
		assert_eq!(Lsb0::at::<u32>(8u8.idx()), 8u8.pos());
		assert_eq!(Lsb0::at::<u32>(9u8.idx()), 9u8.pos());
		assert_eq!(Lsb0::at::<u32>(10u8.idx()), 10u8.pos());
		assert_eq!(Lsb0::at::<u32>(11u8.idx()), 11u8.pos());
		assert_eq!(Lsb0::at::<u32>(12u8.idx()), 12u8.pos());
		assert_eq!(Lsb0::at::<u32>(13u8.idx()), 13u8.pos());
		assert_eq!(Lsb0::at::<u32>(14u8.idx()), 14u8.pos());
		assert_eq!(Lsb0::at::<u32>(15u8.idx()), 15u8.pos());
		assert_eq!(Lsb0::at::<u32>(16u8.idx()), 16u8.pos());
		assert_eq!(Lsb0::at::<u32>(17u8.idx()), 17u8.pos());
		assert_eq!(Lsb0::at::<u32>(18u8.idx()), 18u8.pos());
		assert_eq!(Lsb0::at::<u32>(19u8.idx()), 19u8.pos());
		assert_eq!(Lsb0::at::<u32>(20u8.idx()), 20u8.pos());
		assert_eq!(Lsb0::at::<u32>(21u8.idx()), 21u8.pos());
		assert_eq!(Lsb0::at::<u32>(22u8.idx()), 22u8.pos());
		assert_eq!(Lsb0::at::<u32>(23u8.idx()), 23u8.pos());
		assert_eq!(Lsb0::at::<u32>(24u8.idx()), 24u8.pos());
		assert_eq!(Lsb0::at::<u32>(25u8.idx()), 25u8.pos());
		assert_eq!(Lsb0::at::<u32>(26u8.idx()), 26u8.pos());
		assert_eq!(Lsb0::at::<u32>(27u8.idx()), 27u8.pos());
		assert_eq!(Lsb0::at::<u32>(28u8.idx()), 28u8.pos());
		assert_eq!(Lsb0::at::<u32>(29u8.idx()), 29u8.pos());
		assert_eq!(Lsb0::at::<u32>(30u8.idx()), 30u8.pos());
		assert_eq!(Lsb0::at::<u32>(31u8.idx()), 31u8.pos());
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn le_u64_range() {
		assert_eq!(Lsb0::at::<u64>(0u8.idx()), 0u8.pos());
		assert_eq!(Lsb0::at::<u64>(1u8.idx()), 1u8.pos());
		assert_eq!(Lsb0::at::<u64>(2u8.idx()), 2u8.pos());
		assert_eq!(Lsb0::at::<u64>(3u8.idx()), 3u8.pos());
		assert_eq!(Lsb0::at::<u64>(4u8.idx()), 4u8.pos());
		assert_eq!(Lsb0::at::<u64>(5u8.idx()), 5u8.pos());
		assert_eq!(Lsb0::at::<u64>(6u8.idx()), 6u8.pos());
		assert_eq!(Lsb0::at::<u64>(7u8.idx()), 7u8.pos());
		assert_eq!(Lsb0::at::<u64>(8u8.idx()), 8u8.pos());
		assert_eq!(Lsb0::at::<u64>(9u8.idx()), 9u8.pos());
		assert_eq!(Lsb0::at::<u64>(10u8.idx()), 10u8.pos());
		assert_eq!(Lsb0::at::<u64>(11u8.idx()), 11u8.pos());
		assert_eq!(Lsb0::at::<u64>(12u8.idx()), 12u8.pos());
		assert_eq!(Lsb0::at::<u64>(13u8.idx()), 13u8.pos());
		assert_eq!(Lsb0::at::<u64>(14u8.idx()), 14u8.pos());
		assert_eq!(Lsb0::at::<u64>(15u8.idx()), 15u8.pos());
		assert_eq!(Lsb0::at::<u64>(16u8.idx()), 16u8.pos());
		assert_eq!(Lsb0::at::<u64>(17u8.idx()), 17u8.pos());
		assert_eq!(Lsb0::at::<u64>(18u8.idx()), 18u8.pos());
		assert_eq!(Lsb0::at::<u64>(19u8.idx()), 19u8.pos());
		assert_eq!(Lsb0::at::<u64>(20u8.idx()), 20u8.pos());
		assert_eq!(Lsb0::at::<u64>(21u8.idx()), 21u8.pos());
		assert_eq!(Lsb0::at::<u64>(22u8.idx()), 22u8.pos());
		assert_eq!(Lsb0::at::<u64>(23u8.idx()), 23u8.pos());
		assert_eq!(Lsb0::at::<u64>(24u8.idx()), 24u8.pos());
		assert_eq!(Lsb0::at::<u64>(25u8.idx()), 25u8.pos());
		assert_eq!(Lsb0::at::<u64>(26u8.idx()), 26u8.pos());
		assert_eq!(Lsb0::at::<u64>(27u8.idx()), 27u8.pos());
		assert_eq!(Lsb0::at::<u64>(28u8.idx()), 28u8.pos());
		assert_eq!(Lsb0::at::<u64>(29u8.idx()), 29u8.pos());
		assert_eq!(Lsb0::at::<u64>(30u8.idx()), 30u8.pos());
		assert_eq!(Lsb0::at::<u64>(31u8.idx()), 31u8.pos());
		assert_eq!(Lsb0::at::<u64>(32u8.idx()), 32u8.pos());
		assert_eq!(Lsb0::at::<u64>(33u8.idx()), 33u8.pos());
		assert_eq!(Lsb0::at::<u64>(34u8.idx()), 34u8.pos());
		assert_eq!(Lsb0::at::<u64>(35u8.idx()), 35u8.pos());
		assert_eq!(Lsb0::at::<u64>(36u8.idx()), 36u8.pos());
		assert_eq!(Lsb0::at::<u64>(37u8.idx()), 37u8.pos());
		assert_eq!(Lsb0::at::<u64>(38u8.idx()), 38u8.pos());
		assert_eq!(Lsb0::at::<u64>(39u8.idx()), 39u8.pos());
		assert_eq!(Lsb0::at::<u64>(40u8.idx()), 40u8.pos());
		assert_eq!(Lsb0::at::<u64>(41u8.idx()), 41u8.pos());
		assert_eq!(Lsb0::at::<u64>(42u8.idx()), 42u8.pos());
		assert_eq!(Lsb0::at::<u64>(43u8.idx()), 43u8.pos());
		assert_eq!(Lsb0::at::<u64>(44u8.idx()), 44u8.pos());
		assert_eq!(Lsb0::at::<u64>(45u8.idx()), 45u8.pos());
		assert_eq!(Lsb0::at::<u64>(46u8.idx()), 46u8.pos());
		assert_eq!(Lsb0::at::<u64>(47u8.idx()), 47u8.pos());
		assert_eq!(Lsb0::at::<u64>(48u8.idx()), 48u8.pos());
		assert_eq!(Lsb0::at::<u64>(49u8.idx()), 49u8.pos());
		assert_eq!(Lsb0::at::<u64>(50u8.idx()), 50u8.pos());
		assert_eq!(Lsb0::at::<u64>(51u8.idx()), 51u8.pos());
		assert_eq!(Lsb0::at::<u64>(52u8.idx()), 52u8.pos());
		assert_eq!(Lsb0::at::<u64>(53u8.idx()), 53u8.pos());
		assert_eq!(Lsb0::at::<u64>(54u8.idx()), 54u8.pos());
		assert_eq!(Lsb0::at::<u64>(55u8.idx()), 55u8.pos());
		assert_eq!(Lsb0::at::<u64>(56u8.idx()), 56u8.pos());
		assert_eq!(Lsb0::at::<u64>(57u8.idx()), 57u8.pos());
		assert_eq!(Lsb0::at::<u64>(58u8.idx()), 58u8.pos());
		assert_eq!(Lsb0::at::<u64>(59u8.idx()), 59u8.pos());
		assert_eq!(Lsb0::at::<u64>(60u8.idx()), 60u8.pos());
		assert_eq!(Lsb0::at::<u64>(61u8.idx()), 61u8.pos());
		assert_eq!(Lsb0::at::<u64>(62u8.idx()), 62u8.pos());
		assert_eq!(Lsb0::at::<u64>(63u8.idx()), 63u8.pos());
	}
}
