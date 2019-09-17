/*! Bit Cursors

`bitvec` structures are parametric over any ordering of bits within an element.
The `Cursor` trait maps a cursor position (indicated by the `BitIdx` type) to an
electrical position (indicated by the `BitPos` type) within that element, and
also defines the order of traversal over an element.

The only requirement on implementors of `Cursor` is that the transform function
from cursor (`BitIdx`) to position (`BitPos`) is *total* (every integer in the
domain `0 .. T::BITS` is used) and *unique* (each cursor maps to one and only
one position, and each position is mapped by one and only one cursor).
Contiguity is not required.

`Cursor` is a stateless trait, and implementors should be zero-sized types.
!*/

use crate::store::{
	BitIdx,
	BitMask,
	BitPos,
	BitStore,
};

/** Traverses an element from `MSbit` to `LSbit`.

This is currently the default ordering used by the `BitSlice`, `BitBox` and
`BitVec` data structures the crate exports. It counts from “left” to “right” as
a single byte would be written in English text.

The custom in almost all CS literature and actual hardware is to number bit
indices in an element from `0` at the `LSbit` to the maximal at the `MSbit`,
which is little-endian ordering. If you require that behavior, use the
`LittleEndian` ordering also exported by this module.

This ordering is useful for interfacing with I²C and some serial controllers.

The crate selects it as the default solely based on the author’s observation
that it was the more common ordering in the network serialization protocols used
at his work.
**/
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BigEndian;

#[cfg(target_endian = "big")]
pub type Local = BigEndian;

/** Traverses an element from `LSbit` to `MSbit`.

Almost all CS literature and processors use little-endian numbering to index
bits within an element. This ordering is suitable for building up numbers in
memory, or for interfacing with some networking bit-serial protocols.

If your application is compute-bound and is agnostic to buffer layout, then this
is a better cursor than `BigEndian` because its implementation is a noöp, while
the `BigEndian` implementation performs one subtraction each call. Production of
a bit-mask from a position always requires a left-shift, but in a heavily-used
loop, the difference between two instructions and one may be meaningful.

The RS-232, Ethernet, and USB protocols use this ordering.
**/
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LittleEndian;

#[cfg(target_endian = "little")]
pub type Local = LittleEndian;

/** A cursor over an element.

# Usage

`bitvec` structures store and operate on semantic counts, not bit positions. The
`Cursor::at` function takes a semantic cursor, `BitIdx`, and produces an
electrical position, `BitPos`.
**/
pub trait Cursor {
	/// Name of the cursor type, for use in text display.
	const TYPENAME: &'static str;

	/// Translate a semantic bit index into an electrical bit position.
	///
	/// # Parameters
	///
	/// - `cursor`: The semantic bit index.
	///
	/// # Returns
	///
	/// A concrete position. This value can be used for shifting and masking to
	/// extract a bit from an element. This must be in the domain
	/// `0 .. T::BITS`.
	///
	/// # Type Parameters
	///
	/// - `T`: The storage type for which the position will be calculated.
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
	fn at<T>(cursor: BitIdx<T>) -> BitPos<T>
	where T: BitStore;

	/// Translate a semantic bit index into an electrical bit mask.
	///
	/// This is an optional function; a default implementation is provided for
	/// you.
	///
	/// The default implementation of this function calls `C::at` to produce an
	/// electrical position, then produces a mask by setting the nth bit more
	/// significant than the least significant bit of the elemnet. `Cursor`
	/// implementors may choose to provide a faster mask production here, but
	/// they must satisfy the invariants listed below.
	///
	/// # Parameters
	///
	/// - `cursor`: The semantic bit index.
	///
	/// # Returns
	///
	/// A one-hot encoding of the provided `cursor`’s electrical position in the
	/// `T` element`.
	///
	/// # Type Parameters
	///
	/// - `T`: the storage type for which the mask will be calculated. The mask
	///   must also be this type, as it will be applied to an element of `T` in
	///   order to set, clear, or test a single bit.
	///
	/// # Invariants
	///
	/// A one-hot encoding means that there is exactly one bit set in the
	/// produced value. It must be equivalent to `1 << C::at::<T>(cursor)`.
	///
	/// As with `at`, this function must produce a unique mapping from each
	/// legal index in the `T` domain to a one-hot value of `T`.
	///
	/// # Safety
	///
	/// This function requires that the output is always a one-hot value. It is
	/// illegal to produce a value with more than one bit set, and doing so will
	/// cause uncontrolled side effects.
	fn mask<T>(cursor: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		let place = Self::at(cursor);
		debug_assert!(
			*place < T::BITS,
			"Bit position {} must be less than the width {}",
			*place,
			T::BITS,
		);
		BitMask::new(T::from(1) << *place)
	}
}

impl Cursor for BigEndian {
	const TYPENAME: &'static str = "BigEndian";

	/// Maps a semantic count to a concrete position.
	///
	/// `BigEndian` order moves from `MSbit` first to `LSbit` last.
	#[inline(always)]
	fn at<T>(cursor: BitIdx<T>) -> BitPos<T>
	where T: BitStore {
		unsafe { BitPos::new_unchecked(T::MASK - *cursor) }
	}

	#[inline(always)]
	fn mask<T>(cursor: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		//  Set the MSbit, then shift it down. The left expr is const-folded.
		//  Note: this is not equivalent to `1 << (mask - cursor)`, because that
		//  requires a subtraction every time, but the expression below is only
		//  a single shift.
		unsafe { BitMask::new_unchecked((T::from(1) << T::MASK) >> *cursor) }
	}
}

impl Cursor for LittleEndian {
	const TYPENAME: &'static str = "LittleEndian";

	/// Maps a semantic count to a concrete position.
	///
	/// `LittleEndian` order moves from `LSbit` first to `MSbit` last.
	#[inline(always)]
	fn at<T>(cursor: BitIdx<T>) -> BitPos<T>
	where T: BitStore {
		unsafe { BitPos::new_unchecked(*cursor) }
	}

	#[inline(always)]
	fn mask<T>(cursor: BitIdx<T>) -> BitMask<T>
	where T: BitStore {
		//  Set the LSbit, then shift it up.
		unsafe { BitMask::new_unchecked(T::from(1) << *cursor) }
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::store::IntoBitIdx;

	#[test]
	fn be_u8_range() {
		assert_eq!(BigEndian::at::<u8>(0.idx()), BitPos::new(7));
		assert_eq!(BigEndian::at::<u8>(1.idx()), BitPos::new(6));
		assert_eq!(BigEndian::at::<u8>(2.idx()), BitPos::new(5));
		assert_eq!(BigEndian::at::<u8>(3.idx()), BitPos::new(4));
		assert_eq!(BigEndian::at::<u8>(4.idx()), BitPos::new(3));
		assert_eq!(BigEndian::at::<u8>(5.idx()), BitPos::new(2));
		assert_eq!(BigEndian::at::<u8>(6.idx()), BitPos::new(1));
		assert_eq!(BigEndian::at::<u8>(7.idx()), BitPos::new(0));
	}

	#[test]
	fn be_u16_range() {
		assert_eq!(BigEndian::at::<u16>(0.idx()), BitPos::new(15));
		assert_eq!(BigEndian::at::<u16>(1.idx()), BitPos::new(14));
		assert_eq!(BigEndian::at::<u16>(2.idx()), BitPos::new(13));
		assert_eq!(BigEndian::at::<u16>(3.idx()), BitPos::new(12));
		assert_eq!(BigEndian::at::<u16>(4.idx()), BitPos::new(11));
		assert_eq!(BigEndian::at::<u16>(5.idx()), BitPos::new(10));
		assert_eq!(BigEndian::at::<u16>(6.idx()), BitPos::new(9));
		assert_eq!(BigEndian::at::<u16>(7.idx()), BitPos::new(8));
		assert_eq!(BigEndian::at::<u16>(8.idx()), BitPos::new(7));
		assert_eq!(BigEndian::at::<u16>(9.idx()), BitPos::new(6));
		assert_eq!(BigEndian::at::<u16>(10.idx()), BitPos::new(5));
		assert_eq!(BigEndian::at::<u16>(11.idx()), BitPos::new(4));
		assert_eq!(BigEndian::at::<u16>(12.idx()), BitPos::new(3));
		assert_eq!(BigEndian::at::<u16>(13.idx()), BitPos::new(2));
		assert_eq!(BigEndian::at::<u16>(14.idx()), BitPos::new(1));
		assert_eq!(BigEndian::at::<u16>(15.idx()), BitPos::new(0));
	}

	#[test]
	fn be_u32_range() {
		assert_eq!(BigEndian::at::<u32>(0.idx()), BitPos::new(31));
		assert_eq!(BigEndian::at::<u32>(1.idx()), BitPos::new(30));
		assert_eq!(BigEndian::at::<u32>(2.idx()), BitPos::new(29));
		assert_eq!(BigEndian::at::<u32>(3.idx()), BitPos::new(28));
		assert_eq!(BigEndian::at::<u32>(4.idx()), BitPos::new(27));
		assert_eq!(BigEndian::at::<u32>(5.idx()), BitPos::new(26));
		assert_eq!(BigEndian::at::<u32>(6.idx()), BitPos::new(25));
		assert_eq!(BigEndian::at::<u32>(7.idx()), BitPos::new(24));
		assert_eq!(BigEndian::at::<u32>(8.idx()), BitPos::new(23));
		assert_eq!(BigEndian::at::<u32>(9.idx()), BitPos::new(22));
		assert_eq!(BigEndian::at::<u32>(10.idx()), BitPos::new(21));
		assert_eq!(BigEndian::at::<u32>(11.idx()), BitPos::new(20));
		assert_eq!(BigEndian::at::<u32>(12.idx()), BitPos::new(19));
		assert_eq!(BigEndian::at::<u32>(13.idx()), BitPos::new(18));
		assert_eq!(BigEndian::at::<u32>(14.idx()), BitPos::new(17));
		assert_eq!(BigEndian::at::<u32>(15.idx()), BitPos::new(16));
		assert_eq!(BigEndian::at::<u32>(16.idx()), BitPos::new(15));
		assert_eq!(BigEndian::at::<u32>(17.idx()), BitPos::new(14));
		assert_eq!(BigEndian::at::<u32>(18.idx()), BitPos::new(13));
		assert_eq!(BigEndian::at::<u32>(19.idx()), BitPos::new(12));
		assert_eq!(BigEndian::at::<u32>(20.idx()), BitPos::new(11));
		assert_eq!(BigEndian::at::<u32>(21.idx()), BitPos::new(10));
		assert_eq!(BigEndian::at::<u32>(22.idx()), BitPos::new(9));
		assert_eq!(BigEndian::at::<u32>(23.idx()), BitPos::new(8));
		assert_eq!(BigEndian::at::<u32>(24.idx()), BitPos::new(7));
		assert_eq!(BigEndian::at::<u32>(25.idx()), BitPos::new(6));
		assert_eq!(BigEndian::at::<u32>(26.idx()), BitPos::new(5));
		assert_eq!(BigEndian::at::<u32>(27.idx()), BitPos::new(4));
		assert_eq!(BigEndian::at::<u32>(28.idx()), BitPos::new(3));
		assert_eq!(BigEndian::at::<u32>(29.idx()), BitPos::new(2));
		assert_eq!(BigEndian::at::<u32>(30.idx()), BitPos::new(1));
		assert_eq!(BigEndian::at::<u32>(31.idx()), BitPos::new(0));
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn be_u64_range() {
		assert_eq!(BigEndian::at::<u64>(0.idx()), BitPos::new(63));
		assert_eq!(BigEndian::at::<u64>(1.idx()), BitPos::new(62));
		assert_eq!(BigEndian::at::<u64>(2.idx()), BitPos::new(61));
		assert_eq!(BigEndian::at::<u64>(3.idx()), BitPos::new(60));
		assert_eq!(BigEndian::at::<u64>(4.idx()), BitPos::new(59));
		assert_eq!(BigEndian::at::<u64>(5.idx()), BitPos::new(58));
		assert_eq!(BigEndian::at::<u64>(6.idx()), BitPos::new(57));
		assert_eq!(BigEndian::at::<u64>(7.idx()), BitPos::new(56));
		assert_eq!(BigEndian::at::<u64>(8.idx()), BitPos::new(55));
		assert_eq!(BigEndian::at::<u64>(9.idx()), BitPos::new(54));
		assert_eq!(BigEndian::at::<u64>(10.idx()), BitPos::new(53));
		assert_eq!(BigEndian::at::<u64>(11.idx()), BitPos::new(52));
		assert_eq!(BigEndian::at::<u64>(12.idx()), BitPos::new(51));
		assert_eq!(BigEndian::at::<u64>(13.idx()), BitPos::new(50));
		assert_eq!(BigEndian::at::<u64>(14.idx()), BitPos::new(49));
		assert_eq!(BigEndian::at::<u64>(15.idx()), BitPos::new(48));
		assert_eq!(BigEndian::at::<u64>(16.idx()), BitPos::new(47));
		assert_eq!(BigEndian::at::<u64>(17.idx()), BitPos::new(46));
		assert_eq!(BigEndian::at::<u64>(18.idx()), BitPos::new(45));
		assert_eq!(BigEndian::at::<u64>(19.idx()), BitPos::new(44));
		assert_eq!(BigEndian::at::<u64>(20.idx()), BitPos::new(43));
		assert_eq!(BigEndian::at::<u64>(21.idx()), BitPos::new(42));
		assert_eq!(BigEndian::at::<u64>(22.idx()), BitPos::new(41));
		assert_eq!(BigEndian::at::<u64>(23.idx()), BitPos::new(40));
		assert_eq!(BigEndian::at::<u64>(24.idx()), BitPos::new(39));
		assert_eq!(BigEndian::at::<u64>(25.idx()), BitPos::new(38));
		assert_eq!(BigEndian::at::<u64>(26.idx()), BitPos::new(37));
		assert_eq!(BigEndian::at::<u64>(27.idx()), BitPos::new(36));
		assert_eq!(BigEndian::at::<u64>(28.idx()), BitPos::new(35));
		assert_eq!(BigEndian::at::<u64>(29.idx()), BitPos::new(34));
		assert_eq!(BigEndian::at::<u64>(30.idx()), BitPos::new(33));
		assert_eq!(BigEndian::at::<u64>(31.idx()), BitPos::new(32));
		assert_eq!(BigEndian::at::<u64>(32.idx()), BitPos::new(31));
		assert_eq!(BigEndian::at::<u64>(33.idx()), BitPos::new(30));
		assert_eq!(BigEndian::at::<u64>(34.idx()), BitPos::new(29));
		assert_eq!(BigEndian::at::<u64>(35.idx()), BitPos::new(28));
		assert_eq!(BigEndian::at::<u64>(36.idx()), BitPos::new(27));
		assert_eq!(BigEndian::at::<u64>(37.idx()), BitPos::new(26));
		assert_eq!(BigEndian::at::<u64>(38.idx()), BitPos::new(25));
		assert_eq!(BigEndian::at::<u64>(39.idx()), BitPos::new(24));
		assert_eq!(BigEndian::at::<u64>(40.idx()), BitPos::new(23));
		assert_eq!(BigEndian::at::<u64>(41.idx()), BitPos::new(22));
		assert_eq!(BigEndian::at::<u64>(42.idx()), BitPos::new(21));
		assert_eq!(BigEndian::at::<u64>(43.idx()), BitPos::new(20));
		assert_eq!(BigEndian::at::<u64>(44.idx()), BitPos::new(19));
		assert_eq!(BigEndian::at::<u64>(45.idx()), BitPos::new(18));
		assert_eq!(BigEndian::at::<u64>(46.idx()), BitPos::new(17));
		assert_eq!(BigEndian::at::<u64>(47.idx()), BitPos::new(16));
		assert_eq!(BigEndian::at::<u64>(48.idx()), BitPos::new(15));
		assert_eq!(BigEndian::at::<u64>(49.idx()), BitPos::new(14));
		assert_eq!(BigEndian::at::<u64>(50.idx()), BitPos::new(13));
		assert_eq!(BigEndian::at::<u64>(51.idx()), BitPos::new(12));
		assert_eq!(BigEndian::at::<u64>(52.idx()), BitPos::new(11));
		assert_eq!(BigEndian::at::<u64>(53.idx()), BitPos::new(10));
		assert_eq!(BigEndian::at::<u64>(54.idx()), BitPos::new(9));
		assert_eq!(BigEndian::at::<u64>(55.idx()), BitPos::new(8));
		assert_eq!(BigEndian::at::<u64>(56.idx()), BitPos::new(7));
		assert_eq!(BigEndian::at::<u64>(57.idx()), BitPos::new(6));
		assert_eq!(BigEndian::at::<u64>(58.idx()), BitPos::new(5));
		assert_eq!(BigEndian::at::<u64>(59.idx()), BitPos::new(4));
		assert_eq!(BigEndian::at::<u64>(60.idx()), BitPos::new(3));
		assert_eq!(BigEndian::at::<u64>(61.idx()), BitPos::new(2));
		assert_eq!(BigEndian::at::<u64>(62.idx()), BitPos::new(1));
		assert_eq!(BigEndian::at::<u64>(63.idx()), BitPos::new(0));
	}

	#[test]
	fn le_u8_range() {
		assert_eq!(LittleEndian::at::<u8>(0.idx()), BitPos::new(0));
		assert_eq!(LittleEndian::at::<u8>(1.idx()), BitPos::new(1));
		assert_eq!(LittleEndian::at::<u8>(2.idx()), BitPos::new(2));
		assert_eq!(LittleEndian::at::<u8>(3.idx()), BitPos::new(3));
		assert_eq!(LittleEndian::at::<u8>(4.idx()), BitPos::new(4));
		assert_eq!(LittleEndian::at::<u8>(5.idx()), BitPos::new(5));
		assert_eq!(LittleEndian::at::<u8>(6.idx()), BitPos::new(6));
		assert_eq!(LittleEndian::at::<u8>(7.idx()), BitPos::new(7));
	}

	#[test]
	fn le_u16_range() {
		assert_eq!(LittleEndian::at::<u16>(0.idx()), BitPos::new(0));
		assert_eq!(LittleEndian::at::<u16>(1.idx()), BitPos::new(1));
		assert_eq!(LittleEndian::at::<u16>(2.idx()), BitPos::new(2));
		assert_eq!(LittleEndian::at::<u16>(3.idx()), BitPos::new(3));
		assert_eq!(LittleEndian::at::<u16>(4.idx()), BitPos::new(4));
		assert_eq!(LittleEndian::at::<u16>(5.idx()), BitPos::new(5));
		assert_eq!(LittleEndian::at::<u16>(6.idx()), BitPos::new(6));
		assert_eq!(LittleEndian::at::<u16>(7.idx()), BitPos::new(7));
		assert_eq!(LittleEndian::at::<u16>(8.idx()), BitPos::new(8));
		assert_eq!(LittleEndian::at::<u16>(9.idx()), BitPos::new(9));
		assert_eq!(LittleEndian::at::<u16>(10.idx()), BitPos::new(10));
		assert_eq!(LittleEndian::at::<u16>(11.idx()), BitPos::new(11));
		assert_eq!(LittleEndian::at::<u16>(12.idx()), BitPos::new(12));
		assert_eq!(LittleEndian::at::<u16>(13.idx()), BitPos::new(13));
		assert_eq!(LittleEndian::at::<u16>(14.idx()), BitPos::new(14));
		assert_eq!(LittleEndian::at::<u16>(15.idx()), BitPos::new(15));
	}

	#[test]
	fn le_u32_range() {
		assert_eq!(LittleEndian::at::<u32>(0.idx()), BitPos::new(0));
		assert_eq!(LittleEndian::at::<u32>(1.idx()), BitPos::new(1));
		assert_eq!(LittleEndian::at::<u32>(2.idx()), BitPos::new(2));
		assert_eq!(LittleEndian::at::<u32>(3.idx()), BitPos::new(3));
		assert_eq!(LittleEndian::at::<u32>(4.idx()), BitPos::new(4));
		assert_eq!(LittleEndian::at::<u32>(5.idx()), BitPos::new(5));
		assert_eq!(LittleEndian::at::<u32>(6.idx()), BitPos::new(6));
		assert_eq!(LittleEndian::at::<u32>(7.idx()), BitPos::new(7));
		assert_eq!(LittleEndian::at::<u32>(8.idx()), BitPos::new(8));
		assert_eq!(LittleEndian::at::<u32>(9.idx()), BitPos::new(9));
		assert_eq!(LittleEndian::at::<u32>(10.idx()), BitPos::new(10));
		assert_eq!(LittleEndian::at::<u32>(11.idx()), BitPos::new(11));
		assert_eq!(LittleEndian::at::<u32>(12.idx()), BitPos::new(12));
		assert_eq!(LittleEndian::at::<u32>(13.idx()), BitPos::new(13));
		assert_eq!(LittleEndian::at::<u32>(14.idx()), BitPos::new(14));
		assert_eq!(LittleEndian::at::<u32>(15.idx()), BitPos::new(15));
		assert_eq!(LittleEndian::at::<u32>(16.idx()), BitPos::new(16));
		assert_eq!(LittleEndian::at::<u32>(17.idx()), BitPos::new(17));
		assert_eq!(LittleEndian::at::<u32>(18.idx()), BitPos::new(18));
		assert_eq!(LittleEndian::at::<u32>(19.idx()), BitPos::new(19));
		assert_eq!(LittleEndian::at::<u32>(20.idx()), BitPos::new(20));
		assert_eq!(LittleEndian::at::<u32>(21.idx()), BitPos::new(21));
		assert_eq!(LittleEndian::at::<u32>(22.idx()), BitPos::new(22));
		assert_eq!(LittleEndian::at::<u32>(23.idx()), BitPos::new(23));
		assert_eq!(LittleEndian::at::<u32>(24.idx()), BitPos::new(24));
		assert_eq!(LittleEndian::at::<u32>(25.idx()), BitPos::new(25));
		assert_eq!(LittleEndian::at::<u32>(26.idx()), BitPos::new(26));
		assert_eq!(LittleEndian::at::<u32>(27.idx()), BitPos::new(27));
		assert_eq!(LittleEndian::at::<u32>(28.idx()), BitPos::new(28));
		assert_eq!(LittleEndian::at::<u32>(29.idx()), BitPos::new(29));
		assert_eq!(LittleEndian::at::<u32>(30.idx()), BitPos::new(30));
		assert_eq!(LittleEndian::at::<u32>(31.idx()), BitPos::new(31));
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn le_u64_range() {
		assert_eq!(LittleEndian::at::<u64>(0.idx()), BitPos::new(0));
		assert_eq!(LittleEndian::at::<u64>(1.idx()), BitPos::new(1));
		assert_eq!(LittleEndian::at::<u64>(2.idx()), BitPos::new(2));
		assert_eq!(LittleEndian::at::<u64>(3.idx()), BitPos::new(3));
		assert_eq!(LittleEndian::at::<u64>(4.idx()), BitPos::new(4));
		assert_eq!(LittleEndian::at::<u64>(5.idx()), BitPos::new(5));
		assert_eq!(LittleEndian::at::<u64>(6.idx()), BitPos::new(6));
		assert_eq!(LittleEndian::at::<u64>(7.idx()), BitPos::new(7));
		assert_eq!(LittleEndian::at::<u64>(8.idx()), BitPos::new(8));
		assert_eq!(LittleEndian::at::<u64>(9.idx()), BitPos::new(9));
		assert_eq!(LittleEndian::at::<u64>(10.idx()), BitPos::new(10));
		assert_eq!(LittleEndian::at::<u64>(11.idx()), BitPos::new(11));
		assert_eq!(LittleEndian::at::<u64>(12.idx()), BitPos::new(12));
		assert_eq!(LittleEndian::at::<u64>(13.idx()), BitPos::new(13));
		assert_eq!(LittleEndian::at::<u64>(14.idx()), BitPos::new(14));
		assert_eq!(LittleEndian::at::<u64>(15.idx()), BitPos::new(15));
		assert_eq!(LittleEndian::at::<u64>(16.idx()), BitPos::new(16));
		assert_eq!(LittleEndian::at::<u64>(17.idx()), BitPos::new(17));
		assert_eq!(LittleEndian::at::<u64>(18.idx()), BitPos::new(18));
		assert_eq!(LittleEndian::at::<u64>(19.idx()), BitPos::new(19));
		assert_eq!(LittleEndian::at::<u64>(20.idx()), BitPos::new(20));
		assert_eq!(LittleEndian::at::<u64>(21.idx()), BitPos::new(21));
		assert_eq!(LittleEndian::at::<u64>(22.idx()), BitPos::new(22));
		assert_eq!(LittleEndian::at::<u64>(23.idx()), BitPos::new(23));
		assert_eq!(LittleEndian::at::<u64>(24.idx()), BitPos::new(24));
		assert_eq!(LittleEndian::at::<u64>(25.idx()), BitPos::new(25));
		assert_eq!(LittleEndian::at::<u64>(26.idx()), BitPos::new(26));
		assert_eq!(LittleEndian::at::<u64>(27.idx()), BitPos::new(27));
		assert_eq!(LittleEndian::at::<u64>(28.idx()), BitPos::new(28));
		assert_eq!(LittleEndian::at::<u64>(29.idx()), BitPos::new(29));
		assert_eq!(LittleEndian::at::<u64>(30.idx()), BitPos::new(30));
		assert_eq!(LittleEndian::at::<u64>(31.idx()), BitPos::new(31));
		assert_eq!(LittleEndian::at::<u64>(32.idx()), BitPos::new(32));
		assert_eq!(LittleEndian::at::<u64>(33.idx()), BitPos::new(33));
		assert_eq!(LittleEndian::at::<u64>(34.idx()), BitPos::new(34));
		assert_eq!(LittleEndian::at::<u64>(35.idx()), BitPos::new(35));
		assert_eq!(LittleEndian::at::<u64>(36.idx()), BitPos::new(36));
		assert_eq!(LittleEndian::at::<u64>(37.idx()), BitPos::new(37));
		assert_eq!(LittleEndian::at::<u64>(38.idx()), BitPos::new(38));
		assert_eq!(LittleEndian::at::<u64>(39.idx()), BitPos::new(39));
		assert_eq!(LittleEndian::at::<u64>(40.idx()), BitPos::new(40));
		assert_eq!(LittleEndian::at::<u64>(41.idx()), BitPos::new(41));
		assert_eq!(LittleEndian::at::<u64>(42.idx()), BitPos::new(42));
		assert_eq!(LittleEndian::at::<u64>(43.idx()), BitPos::new(43));
		assert_eq!(LittleEndian::at::<u64>(44.idx()), BitPos::new(44));
		assert_eq!(LittleEndian::at::<u64>(45.idx()), BitPos::new(45));
		assert_eq!(LittleEndian::at::<u64>(46.idx()), BitPos::new(46));
		assert_eq!(LittleEndian::at::<u64>(47.idx()), BitPos::new(47));
		assert_eq!(LittleEndian::at::<u64>(48.idx()), BitPos::new(48));
		assert_eq!(LittleEndian::at::<u64>(49.idx()), BitPos::new(49));
		assert_eq!(LittleEndian::at::<u64>(50.idx()), BitPos::new(50));
		assert_eq!(LittleEndian::at::<u64>(51.idx()), BitPos::new(51));
		assert_eq!(LittleEndian::at::<u64>(52.idx()), BitPos::new(52));
		assert_eq!(LittleEndian::at::<u64>(53.idx()), BitPos::new(53));
		assert_eq!(LittleEndian::at::<u64>(54.idx()), BitPos::new(54));
		assert_eq!(LittleEndian::at::<u64>(55.idx()), BitPos::new(55));
		assert_eq!(LittleEndian::at::<u64>(56.idx()), BitPos::new(56));
		assert_eq!(LittleEndian::at::<u64>(57.idx()), BitPos::new(57));
		assert_eq!(LittleEndian::at::<u64>(58.idx()), BitPos::new(58));
		assert_eq!(LittleEndian::at::<u64>(59.idx()), BitPos::new(59));
		assert_eq!(LittleEndian::at::<u64>(60.idx()), BitPos::new(60));
		assert_eq!(LittleEndian::at::<u64>(61.idx()), BitPos::new(61));
		assert_eq!(LittleEndian::at::<u64>(62.idx()), BitPos::new(62));
		assert_eq!(LittleEndian::at::<u64>(63.idx()), BitPos::new(63));
	}
}
