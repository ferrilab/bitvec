/*! Element bit indexing.

This module provides strong indexing types to manage the concept of addressing
bits inside spans of memory elements. The crate needs to have a concept of bit
positions that exist in memory (`BitIdx`), abstract “dead” bits that mark the
first bit past the end of a memory region and are not required to exist in
hardware (`BitTail`), specific bit positions that may be accessed by machine
instructions (`BitPos`), and element values that mask one or more bits of
interest (`BitMask`).
!*/

use crate::store::BitStore;

use core::{
	marker::PhantomData,
	ops::Deref,
};

#[cfg(feature = "serde")]
use core::convert::TryFrom;

/** Indicates a semantic index of a bit within a memory element.

This type is consumed by [`BitOrder`] implementors, which use it to produce a
concrete bit position inside an element.

`BitIdx` is a semantic counter which has a defined, constant, and predictable
ordering. Values of `BitIdx` refer strictly to an abstract ordering, and not to
any actual bit positions within a memory element, so `BitIdx::<T>(0)` is always
the first bit counted within an element, but is not required to be the most or
least significant bits, or any other particular bits. Which specific bit is
referred by a `BitIdx` value is governed by implementors of `BitOrder`.

# Type Parameters

- `T`: The memory element type controlled by this index.

[`BitOrder`]: ../order/trait.BitOrder.html
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitIdx<T>
where T: BitStore {
	/// Semantic index within an element. Constrained to `0 .. T::BITS`.
	idx: u8,
	/// Marker for the indexed type.
	_ty: PhantomData<T>,
}

impl<T> BitIdx<T>
where T: BitStore {
	/// Wraps a counter value as a known-good index of the `T` element type.
	///
	/// # Parameters
	///
	/// - `idx`: A semantic index within a `T` memory element.
	///
	/// # Returns
	///
	/// If `idx` is within the range `0 .. T::BITS`, then this returns the index
	/// value wrapped in the index type; if `idx` exceeds this range, then this
	/// returns `None`.
	pub fn new(idx: u8) -> Option<Self> {
		if idx >= T::BITS {
			return None;
		}
		Some(unsafe { Self::new_unchecked(idx) })
	}

	/// Wraps a counter value as a known-good index of the `T` element type.
	///
	/// # Parameters
	///
	/// - `idx`: A semantic index within a `T` memory element. It must be in the
	///   range `0 .. T::BITS`.
	#[doc(hidden)]
	#[inline]
	pub unsafe fn new_unchecked(idx: u8) -> Self {
		debug_assert!(
			idx < T::BITS,
			"Bit index {} cannot exceed type width {}",
			idx,
			T::BITS,
		);
		Self { idx, _ty: PhantomData }
	}

	/// Finds the destination bit a certain distance away from a starting bit.
	///
	/// This produces the number of elements to move from the starting point,
	/// and then the bit index of the destination bit in the destination
	/// element.
	///
	/// # Parameters
	///
	/// - `self`: A bit index in some memory element, used as the starting
	///   position for the offset calculation.
	/// - `by`: The number of bits by which to move. Negative values move
	///   downwards in memory: towards index zero, then counting from index
	///   `T::MASK` to index zero in the next element lower in memory, repeating
	///   until arrival. Positive values move upwards in memory: towards index
	///   `T::MASK`, then counting from index zero to index `T::MASK` in the
	///   next element higher in memory, repeating until arrival.
	///
	/// # Returns
	///
	/// - `.0`: The number of elements by which to offset the caller’s element
	///   cursor. This value can be passed directly into [`ptr::offset`].
	/// - `.1`: The bit index of the destination bit in the element selected by
	///   applying the `.0` pointer offset.
	///
	/// # Safety
	///
	/// `by` must not be far enough to cause the returned element offset value
	/// to, when applied to the original memory address via [`ptr::offset`],
	/// produce a reference out of bounds of the original allocation. This
	/// method has no way of checking this requirement.
	///
	/// [`ptr::offset`]: https://doc.rust-lang.org/stable/std/primitive.pointer.html#method.offset
	pub(crate) fn offset(self, by: isize) -> (isize, Self) {
		let val = *self;

		//  Signed-add `*self` and the jump distance. Overflowing is the
		//  unlikely branch. The result is a bit index, and an overflow marker.
		//  `far` is permitted to be negative; this means that it is lower in
		//  memory than the origin bit. The number line has its origin at the
		//  front edge of the origin element, so `-1` is the *last* bit of the
		//  prior memory element.
		let (far, ovf) = by.overflowing_add(val as isize);
		//  If the `isize` addition does not overflow, then the sum can be used
		//  directly.
		if !ovf {
			//  If `far` is in the origin element, then the jump moves zero
			//  elements and produces `far` as an absolute index directly.
			if (0 .. T::BITS as isize).contains(&far) {
				(0, (far as u8).idx())
			}
			//  Otherwise, downshift the bit distance to compute the number of
			//  elements moved in either direction, and mask to compute the
			//  absolute bit index in the destination element.
			else {
				(far >> T::INDX, (far as u8 & T::MASK).idx())
			}
		}
		else {
			//  Overflowing `isize` addition happens to produce ordinary `usize`
			//  addition. In point of fact, `isize` addition and `usize`
			//  addition are the same machine instruction to perform the sum; it
			//  is merely the signed interpretation of the sum that differs. The
			//  sum can be recast back to `usize` without issue.
			let far = far as usize;
			//  This is really only needed in order to prevent sign-extension of
			//  the downshift; once shifted, the value can be safely re-signed.
			((far >> T::INDX) as isize, (far as u8 & T::MASK).idx())
		}
	}

	/// Computes the size of a span from `self` for `len` bits.
	///
	/// Spans always extend upwards in memory.
	///
	/// # Parameters
	///
	/// - `self`: The starting bit position of the span.
	/// - `len`: The number of bits to include in the span.
	///
	/// # Returns
	///
	/// - `.0`: The number of elements of `T` included in the span. If `len` is
	///   `0`, this will be `0`; otherwise, it will be at least one.
	/// - `.1`: The index of the first dead bit *after* the span. If `self` and
	///   `len` are both `0`, this will be `0`; otherwise, it will be in the
	///   domain `1 ..= T::BITS`.
	///
	/// # Notes
	///
	/// This defers to [`BitTail::span`], because `BitTail` is a strict superset
	/// of `BitIdx` (it is `{ BitIdx | T::BITS }`), and spans frequently begin
	/// from the tail of a slice in this crate. The `offset` function is *not*
	/// implemented on `BitTail`, and remains on `BitIdx` because offsets can
	/// only be computed from bit addresses that exist. It does not make sense
	/// to compute the offset from a `T::BITS` tail.
	///
	/// [`BitTail::span`]: struct.BitTail.html#method.span
	#[inline]
	pub(crate) fn span(self, len: usize) -> (usize, BitTail<T>) {
		unsafe { BitTail::new_unchecked(*self) }.span(len)
	}
}

impl<T> Deref for BitIdx<T>
where T: BitStore {
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.idx
	}
}

#[cfg(feature = "serde")]
impl<T> TryFrom<u8> for BitIdx<T>
where T: BitStore {
	type Error = &'static str;

	fn try_from(idx: u8) -> Result<Self, Self::Error> {
		if idx < T::BITS {
			Ok(Self { idx, _ty: PhantomData })
		}
		else {
			Err("Attempted to construct a `BitIdx` with an index out of range")
		}
	}
}

/** Indicates a semantic index of a dead bit *beyond* a memory element.

This type is equivalent to `BitIdx<T>`, except that it includes `T::BITS` in its
domain. Instances of this type will only ever contain `0` when the span they
describe is *empty*. Non-empty spans always cycle through the domain
`1 ..= T::BITS`.

This type cannot be used for indexing, and does not translate to `BitPos<T>`.
This type has no behavior other than viewing its internal `u8` for arithmetic.

# Type Parameters

- `T`: The memory element type controlled by this tail.
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct BitTail<T>
where T: BitStore {
	/// Semantic index *after* an element. Constrained to `0 ..= T::BITS`.
	end: u8,
	/// Marker for the tailed type.
	_ty: PhantomData<T>,
}

impl<T> BitTail<T>
where T: BitStore {
	/// Mark that `end` is a tail index for a type.
	///
	/// # Parameters
	///
	/// - `end` must be in the range `0 ..= T::BITS`.
	pub(crate) unsafe fn new_unchecked(end: u8) -> Self {
		debug_assert!(
			end <= T::BITS,
			"Bit tail {} cannot surpass type width {}",
			end,
			T::BITS,
		);
		Self { end, _ty: PhantomData }
	}

	pub(crate) fn span(self, len: usize) -> (usize, Self) {
		let val = *self;
		debug_assert!(
			val <= T::BITS,
			"Tail out of range: {} overflows type width {}",
			val,
			T::BITS,
		);

		if len == 0 {
			return (0, self);
		}

		let head = val & T::MASK;

		let bits_in_head = (T::BITS - head) as usize;

		if len <= bits_in_head {
			return (1, (head + len as u8).tail());
		}

		let bits_after_head = len - bits_in_head;

		let elts = bits_after_head >> T::INDX;
		let tail = bits_after_head as u8 & T::MASK;

		let is_zero = (tail == 0) as u8;
		let edges = 2 - is_zero as usize;
		(elts + edges, ((is_zero << T::INDX) | tail).tail())

		/* The above expression is the branchless equivalent of this structure:

		if tail == 0 {
			(elts + 1, T::BITS.tail())
		}
		else {
			(elts + 2, tail.tail())
		}
		*/
	}
}

impl<T> Deref for BitTail<T>
where T: BitStore {
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.end
	}
}

/** Indicates a real electrical index within an element.

This type is produced by [`BitOrder`] implementors, and marks a specific
electrical bit within a memory element, rather than `BitIdx`’s semantic bit.

# Type Parameters

- `T`: A `BitStore` element which provides bounds-checking information. The
  [`new`] constructor uses [`T::BITS`] to ensure that constructed `BitPos`
  instances are always valid to use within `T` elements.

[`BitOrder`]: ../order/trait.BitOrder.html
[`T::BITS`]: ../store/trait.BitStore.html#associatedconstant.BITS
[`new`]: #method.new
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitPos<T>
where T: BitStore {
	/// Electrical position within an element. Constrained to `0 .. T::BITS`.
	pos: u8,
	/// Marker for the positioned type.
	_ty: PhantomData<T>,
}

impl<T> BitPos<T>
where T: BitStore {
	/// Produce a new bit position marker at a valid position value.
	///
	/// `BitOrder` implementations should prefer this method, but *may* use
	/// [`::new_unchecked`] if they can guarantee that the range invariant is
	/// upheld.
	///
	/// # Parameters
	///
	/// - `pos`: The bit position value to encode. It must be in the range
	///   `0 .. T::BITS`.
	///
	/// # Panics
	///
	/// This function panics if `pos` is greater than or equal to `T::BITS`.
	///
	/// [`::new_unchecked`]: #method.new_unchecked
	#[inline]
	pub fn new(pos: u8) -> Self {
		assert!(
			pos < T::BITS,
			"Bit position {} cannot exceed type width {}",
			pos,
			T::BITS,
		);
		Self { pos, _ty: PhantomData }
	}

	/// Produce a new bit position marker at any position value.
	///
	/// # Safety
	///
	/// The caller *must* ensure that `pos` is less than `T::BITS`. `BitOrder`
	/// implementations should prefer [`::new`], which panics on range failure.
	///
	/// # Parameters
	///
	/// - `pos`: The bit position value to encode. This must be in the range
	///   `0 .. T::BITS`.
	///
	/// # Returns
	///
	/// `pos` wrapped in the `BitPos` marker type.
	///
	/// # Panics
	///
	/// This function panics if `pos` is greater than or equal to `T::BITS`, but
	/// only in debug builds. It does not inspect `pos` in release builds.
	///
	/// [`::new`]: #method.new
	#[cfg_attr(debug_assertions, inline)]
	#[cfg_attr(not(debug_assertions), inline(always))]
	pub unsafe fn new_unchecked(pos: u8) -> Self {
		debug_assert!(
			pos < T::BITS,
			"Bit position {} cannot exceed type width {}",
			pos,
			T::BITS,
		);
		Self { pos, _ty: PhantomData }
	}
}

impl<T> Deref for BitPos<T>
where T: BitStore {
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.pos
	}
}

/** Wrapper type indicating a one-hot encoding of a bit mask for an element.

This type is produced by [`BitOrder`] implementations to speed up access to the
underlying memory. It ensures that masks have exactly one set bit, and can
safely be used as a mask for read/write access to memory.

# Type Parameters

- `T`: The storage type being masked.

[`BitOrder`]: ../order/trait.BitOrder.html
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitMask<T>
where T: BitStore {
	/// Mask value.
	mask: T,
}

impl<T> BitMask<T>
where T: BitStore {
	/// Produce a new bit-mask wrapper around a one-hot mask value.
	///
	/// `BitOrder` implementations should prefer this method, but *may* use
	/// [`::new_unchecked`] if they can guarantee that the one-hot invariant is
	/// upheld.
	///
	/// # Parameters
	///
	/// - `mask`: The mask value to encode. This **must** have exactly one bit
	///   set high, and all others set low.
	///
	/// # Returns
	///
	/// `mask` wrapped in the `BitMask` marker type.
	///
	/// # Panics
	///
	/// This function unconditionally panics if `mask` has zero or multiple bits
	/// set high.
	///
	/// [`::new_unchecked`]: #method.new_unchecked
	#[inline]
	pub fn new(mask: T) -> Self {
		assert!(
			mask.count_ones() == 1,
			"Masks are required to have exactly one set bit: {:0>1$b}",
			mask,
			T::BITS as usize,
		);
		Self { mask }
	}

	/// Produce a new bit-mask wrapper around any value.
	///
	/// # Safety
	///
	/// The caller *must* ensure that `mask` has exactly one bit set. `BitOrder`
	/// implementations should prefer [`::new`], which always panics on failure.
	///
	/// # Parameters
	///
	/// - `mask`: The mask value to encode. This must have exactly one bit set.
	///   Failure to uphold this requirement will introduce uncontrolled state
	///   contamination.
	///
	/// # Returns
	///
	/// `mask` wrapped in the `BitMask` marker type.
	///
	/// # Panics
	///
	/// This function panics if `mask` has zero or multiple bits set, only in
	/// debug builds. It does not inspect `mask` in release builds.
	///
	/// [`::new`]: #method.new
	#[cfg_attr(debug_assertions, inline)]
	#[cfg_attr(not(debug_assertions), inline(always))]
	pub unsafe fn new_unchecked(mask: T) -> Self {
		debug_assert!(
			mask.count_ones() == 1,
			"Masks are required to have exactly one set bit: {:0>1$b}",
			mask,
			T::BITS as usize,
		);
		Self { mask }
	}
}

impl<T> Deref for BitMask<T>
where T: BitStore {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.mask
	}
}

/** Internal convenience trait for wrapping numbers with appropriate markers.

This trait must only be used on values that are known to be valid for their
context. It provides an internal-only shorthand for wrapping integer literals
and known-good values in marker types.

It is only implemented on `u8`.
**/
pub(crate) trait Indexable {
	/// Wraps a value as a `BitIdx<T>`.
	fn idx<T>(self) -> BitIdx<T>
	where T: BitStore;

	/// Wraps a value as a `BitTail<T>`.
	fn tail<T>(self) -> BitTail<T>
	where T: BitStore;

	/// Wraps a value as a `BitPos<T>`.
	fn pos<T>(self) -> BitPos<T>
	where T: BitStore;
}

impl Indexable for u8 {
	fn idx<T>(self) -> BitIdx<T>
	where T: BitStore {
		unsafe { BitIdx::<T>::new_unchecked(self) }
	}

	fn tail<T>(self) -> BitTail<T>
	where T: BitStore {
		unsafe { BitTail::<T>::new_unchecked(self) }
	}

	fn pos<T>(self) -> BitPos<T>
	where T: BitStore {
		unsafe { BitPos::<T>::new_unchecked(self) }
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn jump_far_up() {
		//  isize::max_value() is 0x7f...ff, so the result bit will be one less
		//  than the start bit.
		for n in 1 .. 8 {
			let (elt, bit) = n.idx::<u8>().offset(isize::max_value());
			assert_eq!(elt, (isize::max_value() >> u8::INDX) + 1);
			assert_eq!(*bit, n - 1);
		}
		let (elt, bit) = 0u8.idx::<u8>().offset(isize::max_value());
		assert_eq!(elt, isize::max_value() >> u8::INDX);
		assert_eq!(*bit, 7);
	}

	#[test]
	fn jump_far_down() {
		//  isize::min_value() is 0x80...00, so the result bit will be equal to
		//  the start bit
		for n in 0 .. 8 {
			let (elt, bit) = n.idx::<u8>().offset(isize::min_value());
			assert_eq!(elt, isize::min_value() >> u8::INDX);
			assert_eq!(*bit, n);
		}
	}
}
