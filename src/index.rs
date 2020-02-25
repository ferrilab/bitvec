/*! Indexing within memory elements.

This module provides types which guarantee certain properties about selecting
bits within a memory element. These types enable their use sites to explicitly
declare the indexing behavior they require, and move safety checks from runtime
to compile time.

# Bit Indexing

The [`BitIdx`] type represents the semantic index of a bit within a memory
element. It does not perform bit positioning, and cannot be used to create a
shift instruction or mask value. It is transformed into a value which can do
these things – [`BitPos`] – through the [`BitOrder::at`] function.

# Region End Marker

`bitvec` uses “half-open” ranges, described by a starting point and a count of
members that are live. This means that the “end” of a range is not the last
member that is *in*cluded in the range, but rather the first member that is
*ex*cluded from it.

This requires the [`BitTail` end marker to include in its range the width of the
element type (`8` for `u8`, etc), in order to mark that a region includes the
very last bit in the element (index `7` for `u8`, etc`).

The starting number for a dead region cannot be used to perform bit selection,
but is used to provide range computation, so it is kept distinct from the
indexing types.

# Bit Positioning

The [`BitPos`] type corresponds directly to a bit position in a memory element.
Its value can be used to create shift instructions which select part of memory.
It is only ever created by the `BitOrder::at` function.

# Bit Selection

The [`BitSel`] type is a one-hot mask encoding for a memory element. Unlike the
previous types, which are range-limited integers, this type is a wrapper over a
memory element and guarantees that it can be used as a mask value in `&` and `|`
operations to modify exactly one bit. It is equivalent to `1 << BitPos.value()`.

# Bit Masking

Lastly, the [`BitMask`] type is a bitmask that permits any number of bits to be
set or cleared. It is provided as a type rather than a bare value in order to
clearly communicate that there is no restriction on what this mask may affect.

[`BitIdx`]: struct.BitIdx.html
[`BitMask`]: struct.BitMask.html
[`BitOrder::at`]: ../order/trait.BitOrder.html#method.at
[`BitPos`]: struct.BitPos.html
[`BitSel`]: struct.BitSel.html
[`BitTail`]: struct.BitTail.html
!*/

use crate::mem::BitMemory;

use core::{
	fmt::{
		self,
		Binary,
		Formatter,
	},
	iter::{
		Product,
		Sum,
	},
	marker::PhantomData,
	ops::{
		BitAnd,
		BitOr,
		Deref,
		Not,
	},
};

#[cfg(feature = "serde")]
use core::convert::TryFrom;

/** Indicates a semantic index of a bit within a memory element.

This is a counter in the domain `0 .. M::BITS`, and marks a semantic position
in the ordering sequence described by a [`BitOrder`] implementation. It is used
for both position computation through `BitOrder` and range computation in
[`BitPtr`].

# Type Parameters

- `M`: The memory element type controlled by this index.

[`BitOrder`]: ../order/trait.BitOrder.html
[`BitPtr`]: ../pointer/struct.BitPtr.html
**/
//  If Rust had user-provided ranged integers, this would be communicable to the
//  compiler:
//  #[rustc_layout_scalar_valid_range_end(M::BITS)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitIdx<M>
where M: BitMemory
{
	/// Semantic index within an element. Constrained to `0 .. M::BITS`.
	idx: u8,
	/// Marker for the indexed type.
	_ty: PhantomData<M>,
}

impl<M> BitIdx<M>
where M: BitMemory
{
	/// The zero index.
	pub const ZERO: Self = Self {
		idx: 0,
		_ty: PhantomData,
	};

	/// Wraps a counter value as a known-good index of the `M` element type.
	///
	/// # Parameters
	///
	/// - `idx`: A semantic index within a `M` memory element.
	///
	/// # Returns
	///
	/// If `idx` is within the range `0 .. M::BITS`, then this returns the index
	/// value wrapped in the index type; if `idx` exceeds this range, then this
	/// returns `None`.
	pub fn new(idx: u8) -> Option<Self> {
		if idx >= M::BITS {
			return None;
		}
		Some(unsafe { Self::new_unchecked(idx) })
	}

	/// Wraps a counter value as a known-good index of the `M` element type.
	///
	/// # Parameters
	///
	/// - `idx`: A semantic index within a `M` memory element. It must be in the
	///   range `0 .. M::BITS`.
	///
	/// # Safety
	///
	/// If `idx` is outside the range, then the produced value will cause errors
	/// and memory unsafety when used.
	#[inline]
	pub unsafe fn new_unchecked(idx: u8) -> Self {
		debug_assert!(
			idx < M::BITS,
			"Bit index {} cannot exceed type width {}",
			idx,
			M::BITS,
		);
		Self {
			idx,
			_ty: PhantomData,
		}
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
	///   `M::MASK` to index zero in the next element lower in memory, repeating
	///   until arrival. Positive values move upwards in memory: towards index
	///   `M::MASK`, then counting from index zero to index `M::MASK` in the
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

		/* Signed-add `*self` and the jump distance. Overflowing is the unlikely
		branch. The result is a bit index, and an overflow marker. `far` is
		permitted to be negative; this means that it is lower in memory than the
		origin bit. The number line has its origin at the front edge of the
		origin element, so `-1` is the *last* bit of the prior memory element.
		*/
		let (far, ovf) = by.overflowing_add(val as isize);
		//  If the `isize` addition does not overflow, then the sum can be used
		//  directly.
		if !ovf {
			//  If `far` is in the origin element, then the jump moves zero
			//  elements and produces `far` as an absolute index directly.
			if (0 .. M::BITS as isize).contains(&far) {
				(0, (far as u8).idx())
			}
			/* Otherwise, downshift the bit distance to compute the number of
			elements moved in either direction, and mask to compute the absolute
			bit index in the destination element.
			*/
			else {
				(far >> M::INDX, (far as u8 & M::MASK).idx())
			}
		}
		else {
			/* Overflowing `isize` addition happens to produce ordinary `usize`
			addition. In point of fact, `isize` addition and `usize` addition
			are the same machine instruction to perform the sum; it is merely
			the signed interpretation of the sum that differs. The sum can be
			recast back to `usize` without issue.
			*/
			let far = far as usize;
			//  This is really only needed in order to prevent sign-extension of
			//  the downshift; once shifted, the value can be safely re-signed.
			((far >> M::INDX) as isize, (far as u8 & M::MASK).idx())
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
	/// - `.0`: The number of elements of `M` included in the span. If `len` is
	///   `0`, this will be `0`; otherwise, it will be at least one.
	/// - `.1`: The index of the first dead bit *after* the span. If `self` and
	///   `len` are both `0`, this will be `0`; otherwise, it will be in the
	///   domain `1 ..= M::BITS`.
	///
	/// # Notes
	///
	/// This defers to [`BitTail::span`], because `BitTail` is a strict superset
	/// of `BitIdx` (it is `{ BitIdx | M::BITS }`), and spans frequently begin
	/// from the tail of a slice in this crate. The `offset` function is *not*
	/// implemented on `BitTail`, and remains on `BitIdx` because offsets can
	/// only be computed from bit addresses that exist. It does not make sense
	/// to compute the offset from a `M::BITS` tail.
	///
	/// [`BitTail::span`]: struct.BitTail.html#method.span
	#[inline]
	pub(crate) fn span(self, len: usize) -> (usize, BitTail<M>) {
		unsafe { BitTail::new_unchecked(*self) }.span(len)
	}
}

impl<M> Binary for BitIdx<M>
where M: BitMemory
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(fmt, "0b{:0>1$b}", self.idx, M::INDX as usize)
	}
}

impl<M> Deref for BitIdx<M>
where M: BitMemory
{
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.idx
	}
}

#[cfg(feature = "serde")]
impl<M> TryFrom<u8> for BitIdx<M>
where M: BitMemory
{
	type Error = &'static str;

	fn try_from(idx: u8) -> Result<Self, Self::Error> {
		Self::new(idx).ok_or(
			"Attempted to construct a `BitIdx` with an index out of range",
		)
	}
}

/** Indicates a semantic index of a dead bit *beyond* a memory element.

This type is equivalent to `BitIdx<M>`, except that it includes `M::BITS` in its
domain. Instances of this type will only ever contain `0` when the span they
describe is *empty*. Non-empty spans always cycle through the domain
`1 ..= M::BITS`.

This type cannot be used for indexing, and does not translate to `BitPos<M>`.
This type has no behavior other than viewing its internal `u8` for arithmetic.

# Type Parameters

- `M`: The memory element type controlled by this tail.
**/
//  #[rustc_layout_scalar_valid_range_end(M::BITS + 1)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitTail<M>
where M: BitMemory
{
	/// Semantic index *after* an element. Constrained to `0 ..= M::BITS`.
	end: u8,
	/// Marker for the tailed type.
	_ty: PhantomData<M>,
}

impl<M> BitTail<M>
where M: BitMemory
{
	/// The termination index.
	pub const END: Self = Self {
		end: M::BITS,
		_ty: PhantomData,
	};

	/// Mark that `end` is a tail index for a type.
	///
	/// # Parameters
	///
	/// - `end` must be in the range `0 ..= M::BITS`.
	pub(crate) unsafe fn new_unchecked(end: u8) -> Self {
		debug_assert!(
			end <= M::BITS,
			"Bit tail {} cannot surpass type width {}",
			end,
			M::BITS,
		);
		Self {
			end,
			_ty: PhantomData,
		}
	}

	pub(crate) fn span(self, len: usize) -> (usize, Self) {
		let val = *self;
		debug_assert!(
			val <= M::BITS,
			"Tail out of range: {} overflows type width {}",
			val,
			M::BITS,
		);

		if len == 0 {
			return (0, self);
		}

		let head = val & M::MASK;

		let bits_in_head = (M::BITS - head) as usize;

		if len <= bits_in_head {
			return (1, (head + len as u8).tail());
		}

		let bits_after_head = len - bits_in_head;

		let elts = bits_after_head >> M::INDX;
		let tail = bits_after_head as u8 & M::MASK;

		let is_zero = (tail == 0) as u8;
		let edges = 2 - is_zero as usize;
		(elts + edges, ((is_zero << M::INDX) | tail).tail())

		/* The above expression is the branchless equivalent of this structure:

		if tail == 0 {
			(elts + 1, M::BITS.tail())
		}
		else {
			(elts + 2, tail.tail())
		}
		*/
	}
}

impl<M> Deref for BitTail<M>
where M: BitMemory
{
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.end
	}
}

/** Indicates a real electrical index within an element.

This type is produced by [`BitOrder`] implementors, and marks a specific
electrical bit within a memory element, rather than [`BitIdx`]’s semantic bit.

# Type Parameters

- `M`: A `BitMemory` element which provides bounds-checking information. The
  [`new`] constructor uses [`M::BITS`] to ensure that constructed `BitPos`
  instances are always valid to use within `M` elements.

[`BitIdx`]: struct.BitIdx.html
[`BitOrder`]: ../order/trait.BitOrder.html
[`M::BITS`]: ../mem/trait.BitMemory.html#associatedconstant.BITS
[`new`]: #method.new
**/
//  #[rustc_layout_scalar_valid_range_end(M::BITS)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitPos<M>
where M: BitMemory
{
	/// Electrical position within an element. Constrained to `0 .. M::BITS`.
	pos: u8,
	/// Marker for the positioned type.
	_ty: PhantomData<M>,
}

impl<M> BitPos<M>
where M: BitMemory
{
	/// Produce a new bit position marker at a valid position value.
	///
	/// `BitOrder` implementations should prefer this method, but *may* use
	/// [`::new_unchecked`] if they can guarantee that the range invariant is
	/// upheld.
	///
	/// # Parameters
	///
	/// - `pos`: The bit position value to encode. It must be in the range `0 ..
	///   M::BITS`.
	///
	/// # Panics
	///
	/// This function panics if `pos` is greater than or equal to `M::BITS`.
	///
	/// [`::new_unchecked`]: #method.new_unchecked
	#[inline]
	pub fn new(pos: u8) -> Self {
		assert!(
			pos < M::BITS,
			"Bit position {} cannot exceed type width {}",
			pos,
			M::BITS,
		);
		Self {
			pos,
			_ty: PhantomData,
		}
	}

	/// Produce a new bit position marker at any position value.
	///
	/// # Safety
	///
	/// The caller *must* ensure that `pos` is less than `M::BITS`. `BitOrder`
	/// implementations should prefer [`::new`], which panics on range failure.
	///
	/// # Parameters
	///
	/// - `pos`: The bit position value to encode. This must be in the range `0
	///   .. M::BITS`.
	///
	/// # Returns
	///
	/// `pos` wrapped in the `BitPos` marker type.
	///
	/// # Panics
	///
	/// This function panics if `pos` is greater than or equal to `M::BITS`, but
	/// only in debug builds. It does not inspect `pos` in release builds.
	///
	/// [`::new`]: #method.new
	#[inline]
	pub unsafe fn new_unchecked(pos: u8) -> Self {
		debug_assert!(
			pos < M::BITS,
			"Bit position {} cannot exceed type width {}",
			pos,
			M::BITS,
		);
		Self {
			pos,
			_ty: PhantomData,
		}
	}

	/// Produces a one-hot selector mask from a position value.
	///
	/// This is equivalent to `1 << *self`.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// A one-hot selector mask with the bit at `*self` set.
	#[inline]
	pub fn select(self) -> BitSel<M> {
		unsafe { BitSel::new_unchecked(M::ONE << *self) }
	}
}

impl<M> Deref for BitPos<M>
where M: BitMemory
{
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

- `M`: The storage type being masked.

[`BitOrder`]: ../order/trait.BitOrder.html
**/
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitSel<M>
where M: BitMemory
{
	/// Mask value.
	sel: M,
}

impl<M> BitSel<M>
where M: BitMemory
{
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
	pub fn new(sel: M) -> Self {
		assert!(
			sel.count_ones() == 1,
			"Masks are required to have exactly one set bit: {:0>1$b}",
			sel,
			M::BITS as usize,
		);
		Self { sel }
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
	#[inline]
	pub unsafe fn new_unchecked(sel: M) -> Self {
		debug_assert!(
			sel.count_ones() == 1,
			"Masks are required to have exactly one set bit: {:0>1$b}",
			sel,
			M::BITS as usize,
		);
		Self { sel }
	}
}

impl<M> Deref for BitSel<M>
where M: BitMemory
{
	type Target = M;

	fn deref(&self) -> &Self::Target {
		&self.sel
	}
}

/** A multi-bit selector mask.

Unlike [`BitSel`], which enforces a strict one-hot mask encoding, this mask type
permits any number of bits to be set or unset. This is used to combine batch
operations in an element.

It is only constructed by accumulating [`BitPos`] or [`BitSel`] values. As
`BitSel` is only constructed from `BitPos`, and `BitPos` is only constructed
from [`BitIdx`] and [`BitOrder`], this enforces a chain of responsibility to
prove that a given multimask is safe.
**/
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitMask<M>
where M: BitMemory
{
	/// A mask of any number of bits to modify.
	mask: M,
}

impl<M> BitMask<M>
where M: BitMemory
{
	/// A full mask.
	pub const ALL: Self = Self { mask: M::ALL };
	/// An empty mask.
	pub const ZERO: Self = Self { mask: M::ZERO };

	/// Wraps a value as a bitmask.
	///
	/// # Safety
	///
	/// The caller must ensure that the mask value is correct in the caller’s
	/// provenance.
	///
	/// # Parameters
	///
	/// - `mask`: Any integer, to be reïnterpreted as a bitmask.
	///
	/// # Returns
	///
	/// The `mask` value as a bitmask.
	pub fn new(mask: M) -> Self {
		Self { mask }
	}
}

impl<M> Product<BitPos<M>> for BitMask<M>
where M: BitMemory
{
	fn product<I>(iter: I) -> Self
	where I: Iterator<Item = BitPos<M>> {
		iter.map(BitPos::select).product()
	}
}

impl<M> Product<BitSel<M>> for BitMask<M>
where M: BitMemory
{
	fn product<I>(iter: I) -> Self
	where I: Iterator<Item = BitSel<M>> {
		iter.fold(Self::ALL, BitAnd::bitand)
	}
}

/// Enable accumulation of a multi-bit mask from a sequence of position values.
impl<M> Sum<BitPos<M>> for BitMask<M>
where M: BitMemory
{
	fn sum<I>(iter: I) -> Self
	where I: Iterator<Item = BitPos<M>> {
		iter.map(BitPos::select).sum()
	}
}

/// Enable accumulation of a multi-bit mask from a sequence of selector masks.
impl<M> Sum<BitSel<M>> for BitMask<M>
where M: BitMemory
{
	fn sum<I>(iter: I) -> Self
	where I: Iterator<Item = BitSel<M>> {
		iter.fold(Self::ZERO, BitOr::bitor)
	}
}

impl<M> BitAnd<M> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitand(self, rhs: M) -> Self {
		Self {
			mask: self.mask & rhs,
		}
	}
}

impl<M> BitAnd<BitPos<M>> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitand(self, rhs: BitPos<M>) -> Self {
		self & rhs.select()
	}
}

impl<M> BitAnd<BitSel<M>> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitand(self, rhs: BitSel<M>) -> Self {
		Self {
			mask: self.mask & rhs.sel,
		}
	}
}

impl<M> BitOr<M> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitor(self, rhs: M) -> Self {
		Self {
			mask: self.mask | rhs,
		}
	}
}

/// Insert a position value into a multimask.
impl<M> BitOr<BitPos<M>> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitor(self, rhs: BitPos<M>) -> Self {
		self | rhs.select()
	}
}

/// Insert a single selector into a multimask.
impl<M> BitOr<BitSel<M>> for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn bitor(self, rhs: BitSel<M>) -> Self {
		Self {
			mask: self.mask | rhs.sel,
		}
	}
}

impl<M> Deref for BitMask<M>
where M: BitMemory
{
	type Target = M;

	fn deref(&self) -> &Self::Target {
		&self.mask
	}
}

impl<M> Not for BitMask<M>
where M: BitMemory
{
	type Output = Self;

	fn not(self) -> Self {
		Self { mask: !self.mask }
	}
}

/** Internal convenience trait for wrapping numbers with appropriate markers.

This trait must only be used on values that are known to be valid for their
context. It provides an internal-only shorthand for wrapping integer literals
and known-good values in marker types.

It is only implemented on `u8`.
**/
pub(crate) trait Indexable {
	/// Wraps a value as a `BitIdx<M>`.
	fn idx<M>(self) -> BitIdx<M>
	where M: BitMemory;

	/// Wraps a value as a `BitTail<M>`.
	fn tail<M>(self) -> BitTail<M>
	where M: BitMemory;

	/// Wraps a value as a `BitPos<M>`.
	fn pos<M>(self) -> BitPos<M>
	where M: BitMemory;
}

impl Indexable for u8 {
	fn idx<M>(self) -> BitIdx<M>
	where M: BitMemory {
		unsafe { BitIdx::<M>::new_unchecked(self) }
	}

	fn tail<M>(self) -> BitTail<M>
	where M: BitMemory {
		unsafe { BitTail::<M>::new_unchecked(self) }
	}

	fn pos<M>(self) -> BitPos<M>
	where M: BitMemory {
		unsafe { BitPos::<M>::new_unchecked(self) }
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
