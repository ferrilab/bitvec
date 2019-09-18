/*! Bit management

The `BitStore` trait defines constants and associated functions suitable for
managing the bit patterns of a fundamental, and is the constraint for the
storage type of the data structures of the rest of the crate.

The other types in this module provide stronger rules about how indices map to
concrete bits in fundamental elements. They are implementation details, and are
not exported in the prelude.
!*/

use crate::cursor::Cursor;

use core::{
	cmp::Eq,
	fmt::{
		Binary,
		Debug,
		Display,
		LowerHex,
		UpperHex,
	},
	marker::{
		PhantomData,
		Send,
		Sync,
	},
	mem::size_of,
	ops::{
		BitAnd,
		BitAndAssign,
		BitOrAssign,
		Deref,
		DerefMut,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
};

#[cfg(feature = "atomic")]
use core::sync::atomic;

#[cfg(not(feature = "atomic"))]
use core::cell::Cell;

#[cfg(feature = "serde")]
use core::convert::TryFrom;

/** Generalizes over the fundamental types for use in `bitvec` data structures.

This trait must only be implemented on unsigned integer primitives with full
alignment. It cannot be implemented on `u128` on any architecture, or on `u64`
on 32-bit systems.

The `Sealed` supertrait ensures that this can only be implemented locally, and
will never be implemented by downstream crates on new types.
**/
pub trait BitStore:
	//  Forbid external implementation
	Sealed
	+ Binary
	//  Element-wise binary manipulation
	+ BitAnd<Self, Output=Self>
	+ BitAndAssign<Self>
	+ BitOrAssign<Self>
	//  Permit indexing into a generic array
	+ Copy
	+ Debug
	+ Default
	+ Display
	//  Permit testing a value against 1 in `get()`.
	+ Eq
	//  Rust treats numeric literals in code as vaguely typed and does not make
	//  them concrete until long after trait expansion, so this enables building
	//  a concrete Self value from a numeric literal.
	+ From<u8>
	//  Permit extending into a `u64`.
	+ Into<u64>
	+ LowerHex
	+ Not<Output=Self>
	+ Send
	+ Shl<u8, Output=Self>
	+ ShlAssign<u8>
	+ Shr<u8, Output=Self>
	+ ShrAssign<u8>
	//  Allow direct access to a concrete implementor type.
	+ Sized
	+ Sync
	+ UpperHex
{
	/// The width, in bits, of this type.
	const BITS: u8 = size_of::<Self>() as u8 * 8;

	/// The number of bits required to index a bit inside the type. This is
	/// always log<sub>2</sub> of the type’s bit width.
	const INDX: u8 = Self::BITS.trailing_zeros() as u8;

	/// The bitmask to turn an arbitrary number into a bit index. Bit indices
	/// are always stored in the lowest bits of an index value.
	const MASK: u8 = Self::BITS - 1;

	/// Name of the implementing type. This is only necessary until the compiler
	/// stabilizes `type_name()`.
	const TYPENAME: &'static str;

	/// Shared-mutability wrapper type used to safely mutate aliased data.
	type Nucleus: BitAccess<Self>;

	/// Reference conversion from `&Self` to `&Self::Nucleus`.
	#[doc(hidden)]
	fn nuclear(&mut self) -> &Self::Nucleus {
		//  Until the language provides a convenient atom producer like
		//  `Cell::from_mut`, this is the only generic way to make atom
		//  reference production work. I refuse to specialize this function in
		//  each implementor on sheer principle.
		unsafe { &*(self as *mut Self as *const Self::Nucleus) }
	}

	/// Sets a specific bit in an element to a given value.
	///
	/// # Safety
	///
	/// This method may only be called from within `&mut BitSlice` contexts.
	///
	/// # Parameters
	///
	/// - `&self`: An immutable reference to self, which will use interior
	///   mutation from either an atomic wrapper or a `Cell` wrapper to safely
	///   mutate shared data.
	/// - `place`: A bit index in the element, from `0` to `Self::MASK`. The bit
	///   under this index will be set according to `value`.
	/// - `value`: A Boolean value, which sets the bit on `true` and clears it
	///   on `false`.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation to translate the index into a position.
	#[inline(always)]
	fn set<C>(&mut self, place: BitIdx<Self>, value: bool)
	where C: Cursor {
		self.nuclear().set::<C>(place, value);
	}

	/// Inverts a specific bit in an element.
	///
	/// # Safety
	///
	/// This method may only be called from within `&mut BitSlice` contexts.
	///
	/// # Parameters
	///
	/// - `&self`: An immutable reference to self, which will use interior
	///   mutation from either an atomic wrapper or a `Cell` wrapper to safely
	///   mutate shared data.
	/// - `place`: A bit index in the element, from `0` to `Self::MASK`. The bit
	///   under this index will be inverted.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation to translate the index into a position.
	#[inline(always)]
	fn invert_bit<C>(&mut self, place: BitIdx<Self>)
	where C: Cursor {
		self.nuclear().invert_bit::<C>(place);
	}

	/// Gets a specific bit in an element.
	///
	/// # Parameters
	///
	/// - `place`: A bit index in the element, from `0` to `Self::MASK`. The bit
	///   under this index will be retrieved as a `bool`.
	///
	/// # Returns
	///
	/// The value of the bit under `place`, as a `bool`.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation to translate the index into a position.
	fn get<C>(&self, place: BitIdx<Self>) -> bool
	where C: Cursor {
		*self & *C::mask(place) != Self::from(0)
	}

	/// Counts how many bits in `self` are set to `1`.
	///
	/// This zero-extends `self` to `u64`, and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of bits in `self` set to `1`. This is a `usize` instead of a
	/// `u32` in order to ease arithmetic throughout the crate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::BitStore;
	/// assert_eq!(BitStore::count_ones(&0u8), 0);
	/// assert_eq!(BitStore::count_ones(&128u8), 1);
	/// assert_eq!(BitStore::count_ones(&192u8), 2);
	/// assert_eq!(BitStore::count_ones(&224u8), 3);
	/// assert_eq!(BitStore::count_ones(&240u8), 4);
	/// assert_eq!(BitStore::count_ones(&248u8), 5);
	/// assert_eq!(BitStore::count_ones(&252u8), 6);
	/// assert_eq!(BitStore::count_ones(&254u8), 7);
	/// assert_eq!(BitStore::count_ones(&255u8), 8);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_ones(&self) -> usize {
		u64::count_ones((*self).into()) as usize
	}

	/// Counts how many bits in `self` are set to `0`.
	///
	/// This inverts `self`, so all `0` bits are `1` and all `1` bits are `0`,
	/// then zero-extends `self` to `u64` and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of bits in `self` set to `0`. This is a `usize` instead of a
	/// `u32` in order to ease arithmetic throughout the crate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::BitStore;
	/// assert_eq!(BitStore::count_zeros(&0u8), 8);
	/// assert_eq!(BitStore::count_zeros(&1u8), 7);
	/// assert_eq!(BitStore::count_zeros(&3u8), 6);
	/// assert_eq!(BitStore::count_zeros(&7u8), 5);
	/// assert_eq!(BitStore::count_zeros(&15u8), 4);
	/// assert_eq!(BitStore::count_zeros(&31u8), 3);
	/// assert_eq!(BitStore::count_zeros(&63u8), 2);
	/// assert_eq!(BitStore::count_zeros(&127u8), 1);
	/// assert_eq!(BitStore::count_zeros(&255u8), 0);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_zeros(&self) -> usize {
		//  invert (0 becomes 1, 1 becomes 0), zero-extend, count ones
		u64::count_ones((!*self).into()) as usize
	}

	/// Extends a single bit to fill the entire element.
	///
	/// # Parameters
	///
	/// - `bit`: The bit to extend.
	///
	/// # Returns
	///
	/// An element with all bits set to the input.
	#[inline]
	fn bits(bit: bool) -> Self {
		if bit {
			!Self::from(0)
		}
		else {
			Self::from(0)
		}
	}
}

/** Newtype indicating a semantic index into an element.

This type is consumed by [`Cursor`] implementors, which use it to produce a
concrete bit position inside an element.

`BitIdx` is a semantic counter which has a defined, constant, and predictable
ordering. Values of `BitIdx` refer strictly to abstract ordering, and not to the
actual position in an element, so `BitIdx(0)` is the first bit in an element,
but is not required to be the electrical `LSb`, `MSb`, or any other.

# Type Parameters

- `T`: The storage type the index controls.

[`Cursor`]: ../cursor/trait.Cursor.html
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitIdx<T>
where T: BitStore {
	/// The semantic bit index within a `T` element.
	idx: u8,
	_ty: PhantomData<T>,
}

impl<T> BitIdx<T>
where T: BitStore {
	#[inline(always)]
	pub(crate) unsafe fn new_unchecked(idx: u8) -> Self {
		debug_assert!(
			idx < T::BITS,
			"Bit index {} cannot exceed type width {}",
			idx,
			T::BITS,
		);
		Self { idx, _ty: PhantomData }
	}

	/// Increments a cursor to the next value, wrapping if needed.
	///
	/// # Parameters
	///
	/// - `self`: The original cursor.
	///
	/// # Returns
	///
	/// - `.0`: An incremented cursor.
	/// - `.1`: Marks whether the increment crossed an element boundary.
	pub(crate) fn incr(self) -> (Self, bool) {
		let next = (*self).wrapping_add(1) & T::MASK;
		(next.idx(), next == 0)
	}

	/// Finds the destination bit a certain distance away from a starting bit.
	///
	/// This produces the number of elements to move, and then the bit index of
	/// the destination bit in the destination element.
	///
	/// # Parameters
	///
	/// - `self`: The bit index in an element of the starting position. This
	///   must be in the domain `0 .. T::BITS`.
	/// - `by`: The number of bits by which to move. Negative values move
	///   downwards in memory: towards `LSb`, then starting again at `MSb` of
	///   the prior element in memory (decreasing address). Positive values move
	///   upwards in memory: towards `MSb`, then starting again at `LSb` of the
	///   subsequent element in memory (increasing address).
	///
	/// # Returns
	///
	/// - `isize`: The number of elements by which to change the caller’s
	///   element cursor. This value can be passed directly into [`ptr::offset`]
	/// - `BitIdx`: The bit index of the destination bit in the newly selected
	///   element. This will always be in the domain `0 .. T::BITS`. This
	///   value can be passed directly into [`Cursor`] functions to compute the
	///   correct place in the element.
	///
	/// # Panics
	///
	/// This function panics if `from` is not less than `T::BITS`, in order
	/// to avoid index out of range errors.
	///
	/// # Safety
	///
	/// `by` must not be large enough to cause the returned `isize` value to,
	/// when applied to [`ptr::offset`], produce a reference out of bounds of
	/// the original allocation. This method has no means of checking this
	/// requirement.
	///
	/// [`Cursor`]: ../cursor/trait.Cursor.html
	/// [`ptr::offset`]: https://doc.rust-lang.org/stable/std/primitive.pointer.html#method.offset
	pub(crate) fn offset(self, by: isize) -> (isize, Self) {
		let val = *self;
		debug_assert!(
			val < T::BITS,
			"Index out of range: {} overflows {}",
			val,
			T::BITS,
		);

		//  Signed-add `self` and the jump distance. Overflowing is the
		//  unlikely branch. The result is a bit index, and an overflow marker.
		//  `far` is permitted to be negative; this means that it is elements
		//  below the origin in memory. The number line has its origin at the
		//  front edge of the origin element, so `-1` is the *last* bit of the
		//  element before, not the first.
		let (far, ovf) = by.overflowing_add(val as isize);
		//  If the `isize` addition does not overflow, then the sum can be used
		//  directly.
		if !ovf {
			//  If `far` is in the origin element, then the jump moves zero
			//  elements and produces `far` as an absolute index directly.
			if far >= 0 && far < T::BITS as isize {
				(0, (far as u8).idx())
			}
			//  Otherwise, we upshift to compute the number of elements moved in
			//  either direction, and mask to compute the absolute bit index in
			//  the destination element.
			else {
				(far >> T::INDX, (far as u8 & T::MASK).idx())
			}
		}
		else {
			//  Overflowing `isize` addition happens to produce ordinary `usize`
			//  addition. In point of fact, `isize` addition and `usize`
			//  addition are the same machine instruction to perform the sum; it
			//  is merely the signed interpretation of the sum that differs. The
			//  sum can be recast back to usize without issue.
			let far = far as usize;
			//  This is really only needed in order to prevent sign-extension of
			//  the downshift; once shifted, the value can be safely re-signed.
			((far >> T::INDX) as isize, (far as u8 & T::MASK).idx())
		}
	}

	/// Computes the size of a span from `self` for `len` bits.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `len`: The number of bits to include in the span.
	///
	/// # Returns
	///
	/// - `.0`: The number of elements `T` included in the span. This will be in
	///   the domain `1 .. usize::max_value()`.
	/// - `.1`: The index of the first bit *after* the span. This will be `0` in
	///   the case that `self` and `len` are both `0`, and otherwise, it will be
	///   in the domain `1 ..= T::BITS`.
	///
	/// # Notes
	///
	/// This defers to [`TailIdx::span`], because `TailIdx` is a strict superset
	/// of `BitIdx` (it is `{ BitIdx | T::BITS }`), and spans frequently begin
	/// from the tail of a slice in this crate. The `offset` function is *not*
	/// implemented on `TailIdx`, and remains on `BitIdx` because offsets can
	/// only be computed from bit addresses that exist. It does not make sense
	/// to compute the offset from a `T::BITS` tail
	///
	/// [`TailIdx::span`]: struct.TailIdx.html#method.span
	#[inline(always)]
	pub(crate) fn span(self, len: usize) -> (usize, TailIdx<T>) {
		self.to_tail().span(len)
	}

	/// Converts a bit index into a tail index.
	///
	/// This is always safe, as the set of tail indices is strictly greater than
	/// the set of bit indices.
	#[inline(always)]
	pub(crate) fn to_tail(self) -> TailIdx<T> {
		unsafe { TailIdx::new_unchecked(*self) }
	}
}

#[cfg(feature = "serde")]
impl<T> TryFrom<u8> for BitIdx<T>
where T: BitStore {
	type Error = &'static str;

	fn try_from(idx: u8) -> Result<Self, Self::Error> {
		if idx < T::BITS {
			Ok(unsafe { Self::new_unchecked(idx) })
		}
		else {
			Err("Attempted to construct a `BitIdx` with an index out of range")
		}
	}
}

impl<T> Deref for BitIdx<T>
where T: BitStore {
	type Target = u8;

	fn deref(&self) -> &Self::Target {
		&self.idx
	}
}

impl<T> DerefMut for BitIdx<T>
where T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.idx
	}
}

/** Crate-internal mechanism for turning known-good bare indices into `BitIdx`.

This is not exposed, because it is a thin wrapper over `BitIdx::new_unchecked`.
It is used only within the crate to wrap known-good index values as a shorthand.
**/
#[doc(hidden)]
pub trait IntoBitIdx {
	fn idx<T>(self) -> BitIdx<T>
	where T: BitStore;

	fn tail_idx<T>(self) -> TailIdx<T>
	where T: BitStore;
}

impl IntoBitIdx for u8 {
	fn idx<T>(self) -> BitIdx<T>
	where T: BitStore {
		debug_assert!(
			self < T::BITS,
			"Bit index {} must be less than the width {}",
			self,
			T::BITS,
		);
		unsafe { BitIdx::<T>::new_unchecked(self) }
	}

	fn tail_idx<T>(self) -> TailIdx<T>
	where T: BitStore {
		debug_assert!(
			self <= T::BITS,
			"Bit index {} must be less than or equal to the width {}",
			self,
			T::BITS,
		);
		unsafe { TailIdx::<T>::new_unchecked(self) }
	}
}

/** Marks that an index is to a dead bit, and cannot be used for indexing.

This type is equivalent to `BitIdx<T>`, except it includes `T::BITS` in its
domain. Instances of this type will only ever contain `0` when the span they
describe is *empty*. Non-empty spans always cycle through the domain
`1 ..= T::BITS`.

Users cannot do anything with this type except view its index as a `u8`.

# Type Parameters

- `T`: A `BitStore` implementation which provides bounds-checking information.
  The `new` function uses `T::BITS` to ensure that constructed `TailIdx`
  instances are always valid to use to describe the first dead bit of `T`
  elements.
**/
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct TailIdx<T>
where T: BitStore {
	/// The dead-bit semantic index within a `T` element.
	tail: u8,
	_ty: PhantomData<T>,
}

impl<T> TailIdx<T>
where T: BitStore {
	/// Constructs a new tail marker.
	///
	/// This is only exporting under `testing` builds, in order to allow tests
	/// to conveniently set up a tail index. It is never used within the crate
	/// proper, and is not part of the public API of the crate at all.
	///
	/// # Parameters
	///
	/// - `tail`: The dead-bit index. This must be in the range `0 ..= T::BITS`.
	///
	/// # Returns
	///
	/// `tail` wrapped in the `TailIdx` encoding type.
	#[cfg(any(test, feature = "testing"))]
	#[inline]
	pub fn new(tail: u8) -> Self {
		tail.tail_idx()
	}

	/// Wraps `tail` in the `TailIdx` encoding type, without any bounds checks.
	///
	/// This is an internal-only function used to skip bounds checks when the
	/// caller has already guaranteed that `tail` is valid.
	///
	/// # Safety
	///
	/// `tail` must be in the range `0 ..= T::BITS`. The caller must perform
	/// this check before making the call. It is *currently* possible to pass
	/// invalid values into the function; if the compiler ever stabilizes
	/// sub-type value range restrictions, these types will implement them and
	/// make it illegal to even *construct* invalid instances, ever before using
	/// them in element access.
	///
	/// # Parameters
	///
	/// - `tail`: The dead-bit index.
	///
	/// # Returns
	///
	/// `tail` wrapped in the `TailIdx` encoding type.
	#[inline(always)]
	pub(crate) unsafe fn new_unchecked(tail: u8) -> Self {
		Self { tail, _ty: PhantomData }
	}

	/// Computes the size of a span starting at `self` running for `len` bits.
	///
	/// Spans are always absolute measurements that proceed from a starting
	/// point and move upwards in memory. They are equivalent to Rust’s
	/// top-exclusive ranges: the starting bit is always included in the span,
	/// but the ending bit is not. The exclusion of the ending bit is why this
	/// produces a `TailIdx` rather than a `BitIdx`.
	///
	/// # Parameters
	///
	/// - `self`: The beginning of the span.
	/// - `len`: The number of bits to include in the span.
	///
	/// # Returns
	///
	/// - `.0`: The number of elements `T` included in the span. When `len` is
	///   `0`, this is also `0`; otherwise, it is in the domain
	///   `1 ..= usize::max_value() >> T::INDX`.
	/// - `.1`: The tail index (first dead bit) of the span. This will be `0`
	///   only when both `self` and `len` are `0`; otherwise, it will be in the
	///   range `1 ..= T::BITS`.
	///
	/// # Behaviors
	///
	/// 1. When `len` is `0`, this returns zero elements and `self` as the tail.
	/// 1. If `self` is `T::BITS`, then it is clamped to `0` for all future
	///   calculations. Non-zero spans that begin at `T::BITS` do not include
	///   their origin element.
	/// 1. When `self + len` is less than `T::BITS`, this returns one element
	///   and the sum as the tail.
	/// 1. When the sum is greater or equal to than `T::BITS` – causing the span
	///   to spill into another element – this produces the number of elements,
	///   including the head, that have live bits, and the appropriate tail
	///   index.
	pub(crate) fn span(self, len: usize) -> (usize, Self) {
		let val = *self;
		//  Trap illegal tail indices in debug mode. In release, they become
		//  impossible to construct, and thus the check is safe to elide.
		debug_assert!(
			val <= T::BITS,
			"Tail out of range: {} overflows {}",
			val,
			T::BITS,
		);

		//  A span of zero bits covers zero elements, and returns `self` as the
		//  tail.
		if len == 0 {
			return (0, self);
		}

		//  Clamp the tail cursor to be a valid head cursor. This wraps
		//  `T::BITS` to zero, which is correct behavior because a span that
		//  begins at maximal tail does not touch the origin element.
		let head = val & T::MASK;

		//  Compute the number of bits remaining in the head element.
		let bits_in_head = (T::BITS - head) as usize;
		//  For `b` bits after the head cursor (the first bit of the span) in
		//  the origin element, when `len <= b`, the span covers one element.
		//  When `len == n`, the tail is `T::BITS`.
		if len <= bits_in_head {
			return (1, (head + len as u8).tail_idx());
		}

		//  If `len > bits_in_head`, then the span spills. Compute the number of
		//  spilled bits – `len - bits_in_head`, which will always be one or
		//  more…
		let bits_after_head = len - bits_in_head;
		//  Then use integer divmod to compute how many full elements after the
		//  origin the span covers…
		let elts = bits_after_head >> T::INDX;
		//  and how many bits are live in the partial tail.
		let tail = bits_after_head as u8 & T::MASK;

		//  Set a flag if the tail is empty.
		let is_zero = (tail == 0) as u8;
		//  `elts` must be incremented to include the origin, and must be
		//  incremented again if the tail element has live bits. This can be
		//  rewritten as `2 - empty_tail`.
		let edges = 2 - is_zero as usize;
		//  If the tail is empty, return the maximum tail index rather than the
		//  minimum. Add the number of edge elements to the number of center
		//  elements. The span is now complete.
		(elts + edges, ((is_zero << T::INDX) | tail).tail_idx())

		/* The above expression is the branchless equivalent of this structure:

		if tail == 0 {
			(elts + 1, T::BITS.tail_idx())
		}
		else {
			(elts + 2, tail.tail_idx())
		}
		*/
	}
}

impl<T> Deref for TailIdx<T>
where T: BitStore {
	type Target = u8;
	fn deref(&self) -> &Self::Target {
		&self.tail
	}
}

/** Newtype indicating a concrete index into an element.

This type is produced by [`Cursor`] implementors, and denotes a concrete bit in
an element rather than a semantic bit.

`Cursor` implementors translate `BitIdx` values, which are semantic places, into
`BitPos` values, which are concrete electrical positions.

# Type Parameters

- `T`: A `BitStore` implementation which provides bounds-checking information.
  The `new` function uses `T::BITS` to ensure that constructed `BitPos`
  instances are always valid to use within `T` elements.

[`Cursor`]: ../cursor/trait.Cursor.html
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitPos<T>
where T: BitStore {
	/// The encoded position value.
	pos: u8,
	_ty: PhantomData<T>,
}

impl<T> BitPos<T>
where T: BitStore {
	/// Produces a new bit position marker at a valid position value.
	///
	/// `Cursor` implementations should prefer this method, but *may* use
	/// [`::new_unchecked`] if they can guarantee that the range invariant is
	/// upheld.
	///
	/// # Parameters
	///
	/// - `pos`: The bit position value to encode.
	///
	/// # Returns
	///
	/// `pos` wrapped in the `BitPos` marker type.
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

	/// Produces a new bit position marker at any position value.
	///
	/// # Safety
	///
	/// The caller *must* ensure that `pos` is less than `T::BITS`. `Cursor`
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
	/// This function panics if `pos` is invalid only in debug builds, and does
	/// not inspect `pos` in release builds.
	///
	/// [`::new`]: #method.new
	#[inline(always)]
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

impl<T> DerefMut for BitPos<T>
where T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.pos
	}
}


/** Newtype indicating a one-hot encoding bit-mask over an element.

This type is produced by [`Cursor`] implementations and then consumed by the
setter and getter functions of [`BitStore::Nucleus`]. It ensures that the
wrapped `T` value has only one bit set, and may be safely used as a mask for the
setter and getter operations.

# Type Parameters

- `T`: The storage type being masked.

[`BitStore::Nucleus`]: trait.BitStore.html#associatedtype.Nucleus
[`Cursor`]: ../cursor/trait.Cursor.html
**/
pub struct BitMask<T>
where T: BitStore {
	/// A one-hot masking value used in single-bit access.
	mask: T,
}

impl<T> BitMask<T>
where T: BitStore {
	/// Produces a new bit mask wrapper around a mask value.
	///
	/// `Cursor` implementations should prefer this method, but *may* use
	/// [`::new_unchecked`] if they can guarantee that the one-hot invariant is
	/// upheld.
	///
	/// # Parameters
	///
	/// - `val`: The mask value to wrap. This **must** have exactly one bit set
	///   to high, and all others set to low.
	///
	/// # Returns
	///
	/// `val` wrapped in the `BitMask` marker type.
	///
	/// # Panics
	///
	/// This function always panics if `val` has 0, or multiple, bits set high.
	///
	/// [`::new_unchecked`]: #method.new_unchecked
	#[inline(always)]
	pub fn new(val: T) -> Self {
		assert!(
			val.count_ones() == 1,
			"A mask must be a one-hot encoding of a position index!",
		);
		Self { mask: val }
	}

	/// Produces a new bit mask wrapper around any value.
	///
	/// # Safety
	///
	/// The caller *must* ensure that `val` has exactly one bit set. `Cursor`
	/// implementations should prefer [`::new`], which always panics on failure.
	///
	/// # Parameters
	///
	/// - `val`: The mask value to wrap. This must have exactly one bit set.
	///
	/// # Returns
	///
	/// `val` wrapped in the `BitMask` marker type.
	///
	/// # Panics
	///
	/// This function panics if `val` is invalid only in debug builds, and does
	/// not inspect `val` in release builds.
	///
	/// [`::new`]: #method.new
	#[inline(always)]
	pub unsafe fn new_unchecked(val: T) -> Self {
		debug_assert!(
			val.count_ones() == 1,
			"A mask must be a one-hot encoding of a position index!",
		);
		Self { mask: val }
	}
}

impl<T> Deref for BitMask<T>
where T: BitStore {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.mask
	}
}

impl BitStore for u8 {
	const TYPENAME: &'static str = "u8";

	#[cfg(feature = "atomic")]
	type Nucleus = atomic::AtomicU8;

	#[cfg(not(feature = "atomic"))]
	type Nucleus = Cell<Self>;
}

impl BitStore for u16 {
	const TYPENAME: &'static str = "u16";

	#[cfg(feature = "atomic")]
	type Nucleus = atomic::AtomicU16;

	#[cfg(not(feature = "atomic"))]
	type Nucleus = Cell<Self>;
}

impl BitStore for u32 {
	const TYPENAME: &'static str = "u32";

	#[cfg(feature = "atomic")]
	type Nucleus = atomic::AtomicU32;

	#[cfg(not(feature = "atomic"))]
	type Nucleus = Cell<Self>;
}

/// Type alias to the CPU word element, `u32`.
#[cfg(target_pointer_width = "32")]
pub type Word = u32;

#[cfg(target_pointer_width = "64")]
impl BitStore for u64 {
	const TYPENAME: &'static str = "u64";

	#[cfg(feature = "atomic")]
	type Nucleus = atomic::AtomicU64;

	#[cfg(not(feature = "atomic"))]
	type Nucleus = Cell<Self>;
}

/// Type alias to the CPU word element, `u64`.
#[cfg(target_pointer_width = "64")]
pub type Word = u64;

/** Marker trait to seal `BitStore` against downstream implementation.

This trait is public in the module, so that other modules in the crate can use
it, but so long as it is not exported by the crate root and this module is
private, this trait effectively forbids downstream implementation of the
`BitStore` trait.
**/
#[doc(hidden)]
pub trait Sealed {}

impl Sealed for u8 {}
impl Sealed for u16 {}
impl Sealed for u32 {}

#[cfg(target_pointer_width = "64")]
impl Sealed for u64 {}

/** Common interface for atomic and cellular shared-mutability wrappers.
**/
pub trait BitAccess<T>
where T: BitStore {
	fn clear_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor;

	fn set_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor;

	fn invert_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor;

	fn get<C>(&self, bit: BitIdx<T>) -> bool
	where C: Cursor;

	#[inline(always)]
	fn set<C>(&self, bit: BitIdx<T>, value: bool)
	where C: Cursor {
		if value {
			self.set_bit::<C>(bit);
		}
		else {
			self.clear_bit::<C>(bit);
		}
	}

	#[inline(always)]
	fn base(&self) -> &T {
		unsafe { &*(self as *const Self as *const T) }
	}
}

/* FIXME(myrrlyn): When the `radium` crate publishes generic traits, erase the
implementations currently in use and enable the generic implementation below:

use core::sync::atomic::Ordering::Relaxed;
impl<T, R> BitAccess<T> for R
where T: BitStore, R: RadiumBits<T> {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor {
		self.fetch_and(!*C::mask(bit), Relaxed);
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor {
		self.fetch_or(*C::mask(bit), Relaxed);
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<T>)
	where C: Cursor {
		self.fetch_xor(*C::mask(bit), Relaxed);
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<T>) -> bool
	where C: Cursor{
		self.load(Relaxed) & *C::mask(bit) != 0
	}
}
*/

#[cfg(feature = "atomic")] fn _atom() {

impl BitAccess<u8> for atomic::AtomicU8 {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.fetch_and(!*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.fetch_or(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.fetch_xor(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u8>) -> bool
	where C: Cursor{
		self.load(atomic::Ordering::Relaxed) & *C::mask(bit) != 0
	}
}

impl BitAccess<u16> for atomic::AtomicU16 {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.fetch_and(!*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.fetch_or(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.fetch_xor(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u16>) -> bool
	where C: Cursor{
		self.load(atomic::Ordering::Relaxed) & *C::mask(bit) != 0
	}
}

impl BitAccess<u32> for atomic::AtomicU32 {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.fetch_and(!*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.fetch_or(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.fetch_xor(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u32>) -> bool
	where C: Cursor{
		self.load(atomic::Ordering::Relaxed) & *C::mask(bit) != 0
	}
}

#[cfg(target_pointer_width = "64")]
impl BitAccess<u64> for atomic::AtomicU64 {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.fetch_and(!*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.fetch_or(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.fetch_xor(*C::mask(bit), atomic::Ordering::Relaxed);
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u64>) -> bool
	where C: Cursor{
		self.load(atomic::Ordering::Relaxed) & *C::mask(bit) != 0
	}
}

}

#[cfg(not(feature = "atomic"))] fn _cell() {

impl BitAccess<u8> for Cell<u8> {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u8>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u8>) -> bool
	where C: Cursor{
		self.get() & *C::mask(bit) != 0
	}
}

impl BitAccess<u16> for Cell<u16> {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u16>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u16>) -> bool
	where C: Cursor{
		self.get() & *C::mask(bit) != 0
	}
}

impl BitAccess<u32> for Cell<u32> {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u32>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u32>) -> bool
	where C: Cursor{
		self.get() & *C::mask(bit) != 0
	}
}

#[cfg(target_pointer_width = "64")]
impl BitAccess<u64> for Cell<u64> {
	#[inline(always)]
	fn clear_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert_bit<C>(&self, bit: BitIdx<u64>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get<C>(&self, bit: BitIdx<u64>) -> bool
	where C: Cursor{
		self.get() & *C::mask(bit) != 0
	}
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
		let (elt, bit) = 0.idx::<u8>().offset(isize::max_value());
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

	#[test]
	fn bits() {
		assert_eq!(u8::bits(false), 0);
		assert_eq!(u8::bits(true), u8::max_value());

		assert_eq!(u16::bits(false), 0);
		assert_eq!(u16::bits(true), u16::max_value());

		assert_eq!(u32::bits(false), 0);
		assert_eq!(u32::bits(true), u32::max_value());

		#[cfg(target_pointer_width = "64")]
		assert_eq!(u64::bits(false), 0);
		#[cfg(target_pointer_width = "64")]
		assert_eq!(u64::bits(true), u64::max_value());
	}

	#[test]
	fn span() {
		//  Starting from the head and filling an element produces the maximal
		//  tail index
		assert_eq!(0.tail_idx::<u8>().span(8), (1, 8.tail_idx()));

		//  a zero tail is *only* produced for (0, 0) inputs
		assert_eq!(0.tail_idx::<u8>().span(0), (0, 0.tail_idx()));
		//  span(0) is the identity function
		assert_eq!(8.tail_idx::<u8>().span(0), (0, 8.tail_idx()));

		//  Starting from the tail of one element, and spilling to the next,
		//  produces a span over *one* element, because the maximal tail is not
		//  a member of the origin element.
		assert_eq!(8.tail_idx::<u8>().span(1), (1, 1.tail_idx()));
		assert_eq!(8.tail_idx::<u8>().span(8), (1, 8.tail_idx()));
		assert_eq!(8.tail_idx::<u8>().span(9), (2, 1.tail_idx()));
	}
}
