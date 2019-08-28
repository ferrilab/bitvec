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
	convert::From,
	fmt::{
		self,
		Binary,
		Debug,
		Display,
		Formatter,
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
use crate::atomic::Atomic;

#[cfg(feature = "atomic")]
use core::sync::atomic;

#[cfg(not(feature = "atomic"))]
use crate::cellular::Cellular;

#[cfg(not(feature = "atomic"))]
use core::cell::Cell;

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

	/// Atomic version of the storage type, to have properly fenced access.
	#[cfg(feature = "atomic")]
	#[doc(hidden)]
	type Nucleus: Atomic<Fundamental = Self>;

	/// Cellular version of the storage type, to have properly bound access.
	#[cfg(not(feature = "atomic"))]
	#[doc(hidden)]
	type Nucleus: Cellular<Fundamental = Self>;

	/// Reference conversion from `&Self` to `&Self::Nucleus`.
	#[doc(hidden)]
	fn nuclear(&self) -> &Self::Nucleus {
		unsafe { &*(self as *const Self as *const Self::Nucleus) }
	}

	/// Performs a load on the underlying element.
	///
	/// Under the `atomic` feature, this is a synchronized load that is
	/// guaranteed to occur only after pending read/modify/write cycles have
	/// finished. Without the `atomic` feature, this is a normal dereference.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The element referred to by the `self` reference, loaded according to the
	/// presence or absence of the `atomic` feature.
	#[inline(always)]
	fn load(&self) -> Self {
		self.nuclear().get()
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
	///
	/// # Examples
	///
	/// This example sets and clears bits in a byte.
	///
	/// ```rust
	/// use bitvec::prelude::{
	///   BitIdx,
	///   BitStore,
	///   BigEndian,
	///   LittleEndian,
	/// };
	///
	/// let mut elt: u16 = 0;
	///
	/// elt.set::<BigEndian>(BitIdx::new(1), true);
	/// assert_eq!(elt, 0b0100_0000__0000_0000);
	/// elt.set::<LittleEndian>(BitIdx::new(1), true);
	/// assert_eq!(elt, 0b0100_0000__0000_0010);
	///
	/// elt.set::<BigEndian>(BitIdx::new(1), false);
	/// assert_eq!(elt, 0b0000_0000__0000_0010);
	/// elt.set::<LittleEndian>(BitIdx::new(1), false);
	/// assert_eq!(elt, 0);
	/// ```
	#[inline(always)]
	fn set<C>(&self, place: BitIdx<Self>, value: bool)
	where C: Cursor {
		self.set_at(place.pos::<C>(), value);
	}

	/// Sets a specific bit in an element to a given value.
	///
	/// # Safety
	///
	/// This method may only be called within an `&mut BitSlice` context.
	///
	/// # Parameters
	///
	/// - `&self`: An immutable reference to self, which will use interior
	///   mutation from either an atomic wrapper or a `Cell` wrapper to safely
	///   mutate shared data.
	/// - `place`: A bit *position* in the element, where `0` is the LSbit and
	///   `Self::MASK` is the MSbit.
	/// - `value`: A Boolean value, which sets the bit high on `true` and clears
	///   it low on `false`.
	///
	/// # Panics
	///
	/// This function only panics in debug mode. In release mode, it is
	/// impossible to construct a `BitPos` that exceeds `Self`’s width.
	///
	/// # Examples
	///
	/// This example sets and clears bits in a byte.
	///
	/// ```rust
	/// use bitvec::prelude::{BitPos, BitStore};
	/// let mut elt: u8 = 0;
	/// elt.set_at(BitPos::new(0), true);
	/// assert_eq!(elt, 0b0000_0001);
	/// elt.set_at(BitPos::new(7), true);
	/// assert_eq!(elt, 0b1000_0001);
	/// ```
	fn set_at(&self, place: BitPos<Self>, value: bool) {
		//  Outside of testing builds, it is only possible to construct `BitPos`
		//  by going through conformant `Cursor` implementations.
		debug_assert!(
			*place < Self::BITS,
			"Bit index {} must be less than the width {}",
			*place,
			Self::BITS,
		);
		if value {
			self.nuclear().set(place);
		}
		else {
			self.nuclear().clear(place);
		}
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
	fn invert<C>(&self, place: BitIdx<Self>)
	where C: Cursor {
		self.invert_at(place.pos::<C>());
	}

	/// Inverts a specific bit in an element.
	///
	/// # Safety
	///
	/// This method may only be called within an `&mut BitSlice` context.
	///
	/// # Parameters
	///
	/// - `&self`: An immutable reference to self, which will use interior
	///   mutation from either an atomic wrapper or a `Cell` wrapper to safely
	///   mutate shared data.
	/// - `place`: A bit *position* in the element, where `0` is the LSbit and
	///   `Self::MASK` is the MSbit.
	///
	/// # Panics
	///
	/// This function only panics in debug mode. In release mode, it is
	/// impossible to construct a `BitPos` that exceeds `Self`’s width.
	fn invert_at(&self, place: BitPos<Self>) {
		debug_assert!(
			*place < Self::BITS,
			"Bit index {} must be less than the width {}",
			*place,
			Self::BITS,
		);
		self.nuclear().invert(place);
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
	///
	/// # Examples
	///
	/// This example gets two bits from a byte.
	///
	/// ```rust
	/// use bitvec::prelude::{BitIdx, BitStore, BigEndian};
	/// let elt: u8 = 0b0010_0000;
	/// assert!(!elt.get::<BigEndian>(BitIdx::new(1)));
	/// assert!(elt.get::<BigEndian>(BitIdx::new(2)));
	/// assert!(!elt.get::<BigEndian>(BitIdx::new(3)));
	/// ```
	fn get<C>(&self, place: BitIdx<Self>) -> bool
	where C: Cursor {
		self.get_at(place.pos::<C>())
	}

	/// Gets a specific bit in an element.
	///
	/// # Parameters
	///
	/// - `place`: A bit *position* in the element, from `0` at LSbit to
	///   `Self::MASK` at MSbit. The bit under this position will be retrieved
	///   as a `bool`.
	///
	/// # Returns
	///
	/// The value of the bit under `place`, as a `bool`.
	///
	/// # Panics
	///
	/// This function only panics in debug mode. In release mode, it is
	/// impossible to construct a `BitPos` that exceeds `Self`’s width.
	///
	/// # Examples
	///
	/// This example gets two bits from a byte.
	///
	/// ```rust
	/// use bitvec::prelude::{BitPos, BitStore};
	/// let elt: u8 = 0b0010_0000;
	/// assert!(!elt.get_at(BitPos::new(4)));
	/// assert!(elt.get_at(BitPos::new(5)));
	/// assert!(!elt.get_at(BitPos::new(6)));
	/// ```
	fn get_at(&self, place: BitPos<Self>) -> bool {
		debug_assert!(
			*place < Self::BITS,
			"Bit index {} must be less than the width {}",
			*place,
			Self::BITS,
		);
		self.load() & Self::mask_at(place) != Self::from(0u8)
	}

	/// Produces the bit mask which selects only the bit at the requested
	/// position.
	///
	/// This mask must be inverted in order to clear the bit.
	///
	/// # Parameters
	///
	/// - `place`: The bit position for which to create a bitmask.
	///
	/// # Returns
	///
	/// The one-hot encoding of the bit position index.
	///
	/// # Panics
	///
	/// This function only panics in debug mode. In release mode, it is
	/// impossible to construct a `BitPos` that exceeds `Self`’s width.
	///
	/// # Examples
	///
	/// This example produces the one-hot encodings for indices.
	///
	/// ```rust
	/// use bitvec::prelude::{BitPos, BitStore};
	///
	/// assert_eq!(u8::mask_at(BitPos::new(0)), 0b0000_0001);
	/// assert_eq!(u8::mask_at(BitPos::new(1)), 0b0000_0010);
	/// assert_eq!(u8::mask_at(BitPos::new(2)), 0b0000_0100);
	/// assert_eq!(u8::mask_at(BitPos::new(3)), 0b0000_1000);
	/// assert_eq!(u8::mask_at(BitPos::new(4)), 0b0001_0000);
	/// assert_eq!(u8::mask_at(BitPos::new(5)), 0b0010_0000);
	/// assert_eq!(u8::mask_at(BitPos::new(6)), 0b0100_0000);
	/// assert_eq!(u8::mask_at(BitPos::new(7)), 0b1000_0000);
	///
	/// assert_eq!(u16::mask_at(BitPos::new(8)),  0b0000_0001__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(9)),  0b0000_0010__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(10)), 0b0000_0100__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(11)), 0b0000_1000__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(12)), 0b0001_0000__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(13)), 0b0010_0000__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(14)), 0b0100_0000__0000_0000);
	/// assert_eq!(u16::mask_at(BitPos::new(15)), 0b1000_0000__0000_0000);
	///
	/// assert_eq!(u32::mask_at(BitPos::new(16)), 1 << 16);
	/// assert_eq!(u32::mask_at(BitPos::new(24)), 1 << 24);
	/// assert_eq!(u32::mask_at(BitPos::new(31)), 1 << 31);
	///
	/// # #[cfg(target_pointer_width = "64")] {
	/// assert_eq!(u64::mask_at(BitPos::new(32)), 1 << 32);
	/// assert_eq!(u64::mask_at(BitPos::new(48)), 1 << 48);
	/// assert_eq!(u64::mask_at(BitPos::new(63)), 1 << 63);
	/// # }
	/// ```
	#[inline(always)]
	fn mask_at(place: BitPos<Self>) -> Self {
		debug_assert!(
			*place < Self::BITS,
			"Bit index {} must be less than the width {}",
			*place,
			Self::BITS,
		);
		//  Pad 1 to the correct width, then shift up to the correct bit place.
		Self::from(1u8) << *place
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
		u64::count_ones(self.load().into()) as usize
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
		u64::count_ones((!self.load()).into()) as usize
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
#[doc(hidden)]
pub struct BitIdx<T>
where T: BitStore {
	idx: u8,
	_ty: PhantomData<T>,
}

impl<T> BitIdx<T>
where T: BitStore {
	#[inline]
	pub fn new(idx: u8) -> Self {
		assert!(
			idx < T::BITS,
			"Bit index {} cannot exceed type width {}",
			idx,
			T::BITS,
		);
		unsafe { Self::new_unchecked(idx) }
	}

	#[inline(always)]
	pub unsafe fn new_unchecked(idx: u8) -> Self {
		Self { idx, _ty: PhantomData }
	}

	#[inline(always)]
	pub(crate) fn pos<C>(self) -> BitPos<T>
	where C: Cursor {
		C::at::<T>(self)
	}

	/// Increments a cursor to the next value, wrapping if needed.
	///
	/// # Parameters
	///
	/// - `self`: The original cursor.
	///
	/// # Returns
	///
	/// - `Self`: An incremented cursor.
	/// - `bool`: Marks whether the increment crossed an element boundary.
	///
	/// # Type Parameters
	///
	/// - `T: BitStore`: The storage type for which the increment will be
	///   calculated.
	///
	/// # Panics
	///
	/// This method panics if `self` is not less than `T::BITS`, in order to
	/// avoid index out of range errors.
	///
	/// # Examples
	///
	/// This example increments inside an element.
	///
	/// ```rust
	/// # #[cfg(feature = "testing")] {
	/// use bitvec::testing::BitIdx;
	/// # use bitvec::store::IntoBitIdx;
	/// assert_eq!(BitIdx::from(6).incr::<u8>(), (7.idx(), false));
	/// # }
	/// ```
	///
	/// This example increments at the high edge, and wraps to the next element.
	///
	/// ```rust
	/// # #[cfg(feature = "testing")] {
	/// use bitvec::testing::BitIdx;
	/// # use bitvec::store::IntoBitIdx;
	/// assert_eq!(BitIdx::from(7).incr::<u8>(), (0.idx(), true));
	/// # }
	/// ```
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
	/// # Examples
	///
	/// This example calculates offsets within the same element.
	///
	/// ```rust
	/// # #[cfg(feature = "testing")] {
	/// use bitvec::testing::BitIdx;
	/// assert_eq!(BitIdx::<u32>::new(1).offset(4isize), (0, BitIdx::new(5)));
	/// assert_eq!(BitIdx::<u32>::new(6).offset(-3isize), (0, BitIdx::new(3)));
	/// # }
	/// ```
	///
	/// This example calculates offsets that cross into other elements. It uses
	/// `u32`, so the bit index domain is `0 ..= 31`.
	///
	/// `7 - 18`, modulo 32, wraps down from 0 to 31 and continues decreasing.
	/// `23 + 68`, modulo 32, wraps up from 31 to 0 and continues increasing.
	///
	/// ```rust
	/// # #[cfg(feature = "testing")] {
	/// use bitvec::testing::BitIdx;
	/// assert_eq!(BitIdx::<u32>::new(7).offset(-18isize), (-1, BitIdx::new(21)));
	/// assert_eq!(BitIdx::<u32>::new(23).offset(68isize), (2, BitIdx::new(27)));
	/// # }
	/// ```
	///
	/// [`Cursor`]: ../cursor/trait.Cursor.html
	/// [`ptr::offset`]: https://doc.rust-lang.org/stable/std/primitive.pointer.html#method.offset
	pub fn offset(self, by: isize) -> (isize, Self) {
		let val = *self;
		debug_assert!(
			val < T::BITS,
			"Index out of range: {} overflows {}",
			val,
			T::BITS,
		);
		//  If the `isize` addition does not overflow, then the sum can be used
		//  directly.
		if let (far, false) = by.overflowing_add(val as isize) {
			//  If `far` is in the domain `0 .. T::BITS`, then the offset did
			//  not depart the element.
			if far >= 0 && far < T::BITS as isize {
				(0, unsafe { Self::new_unchecked(far as u8) })
			}
			//  If `far` is negative, then the offset leaves the initial element
			//  going down. If `far` is not less than `T::BITS`, then the
			//  offset leaves the initial element going up.
			else {
				(far >> T::INDX, (far as u8 & T::MASK).idx())
			}
		}
		//  If the `isize` addition overflows, then the `by` offset is positive.
		//  Add as `usize` and use that. This is guaranteed not to overflow,
		//  because `isize -> usize` doubles the domain, but `self` is limited
		//  to `0 .. T::BITS`.
		else {
			let far = val as usize + by as usize;
			//  This addition will always result in a `usize` whose lowest
			//  `T::INDX` bits are the bit index in the destination element,
			//  and the rest of the high bits (shifted down) are the number of
			//  elements by which to advance.
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
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "testing")] {
	/// use bitvec::testing::{BitIdx, BitStore, TailIdx};
	///
	/// let head: BitIdx<u8> = BitIdx::new(0);
	/// assert_eq!(head.span(8), (1, TailIdx::<u8>::new(8)));
	/// # }
	/// ```
	pub fn span(self, len: usize) -> (usize, TailIdx<T>) {
		let val = *self & T::MASK;
		debug_assert!(
			*self <= T::BITS,
			"Index {} is invalid for type {}",
			val,
			T::TYPENAME,
		);

		//  A span of zero bits covers zero elements, and does not move the
		//  index.
		if len == 0 {
			return (0, self.to_tail());
		}

		//  Number of bits in the head *element*. Domain 32 .. 0.
		let bits_in_head = (T::BITS - val) as usize;
		//  If there are `n` bits live between the head cursor (which marks the
		//  address of the first live bit) and the back edge of the element,
		//  then when `len <= n`, the span covers one element. When `len == n`,
		//  the tail will be `T::BITS`, which is valid for a tail.
		if len <= bits_in_head {
			return (1, (val + len as u8).tail_idx());
		}
		//  If there are more bits in the span than `n`, then subtract `n` from
		//  `len` and use the difference to count elements and bits.

		//  1 ..
		let bits_after_head = len - bits_in_head;
		//  Count the number of wholly filled elements
		let elts = bits_after_head >> T::INDX;
		//  Count the number of bits in the *next* element. If this is zero,
		//  become `T::BITS`; if it is nonzero, add one more to `elts`.
		//  `elts` must have one added to it by default to account for the
		//  head element.
		let bits = bits_after_head as u8 & T::MASK;

		/*
		 * The expression below this comment is equivalent to the branched
		 * structure below, but branchless.
		 *
		 * if bits == 0 {
		 * 	(elts + 1, T::BITS.into())
		 * }
		 * else {
		 * 	(elts + 2, bits.into())
		 * }
		 */

		let is_zero = (bits == 0) as u8;
		(elts + 2 - is_zero as usize, ((is_zero << T::INDX) | bits).tail_idx())
	}

	/// Converts a bit index into a tail index.
	///
	/// This is always safe, as the set of tail indices is strictly greater than
	/// the set of bit indices.
	pub(crate) fn to_tail(self) -> TailIdx<T> {
		unsafe { TailIdx::new_unchecked(*self) }
	}
}

/// Unwraps a `BitIdx` to a `u8`.
impl<T> Into<u8> for BitIdx<T>
where T: BitStore {
	fn into(self) -> u8 {
		self.idx
	}
}

impl<T> Display for BitIdx<T>
where T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(&self.idx, f)
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
**/
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct TailIdx<T>
where T: BitStore {
	tail: u8,
	_ty: PhantomData<T>,
}

impl<T> TailIdx<T>
where T: BitStore {
	pub fn new(tail: u8) -> Self {
		tail.tail_idx()
	}

	pub(crate) unsafe fn new_unchecked(tail: u8) -> Self {
		Self { tail, _ty: PhantomData }
	}

	pub fn span(self, len: usize) -> (usize, Self) {
		let tail = *self;
		let (elts, bits) = (tail & T::MASK).idx().span(len);
		(elts + (tail == T::BITS) as usize, bits)
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

[`Cursor`]: ../cursor/trait.Cursor.html
**/
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[doc(hidden)]
pub struct BitPos<T>
where T: BitStore {
	pos: u8,
	_ty: PhantomData<T>,
}

impl<T> BitPos<T>
where T: BitStore {
	#[inline]
	pub fn new(pos: u8) -> Self {
		assert!(
			pos < T::BITS,
			"Bit position {} cannot exceed type width {}",
			pos,
			T::BITS,
		);
		unsafe { Self::new_unchecked(pos) }
	}

	#[inline(always)]
	pub unsafe fn new_unchecked(pos: u8) -> Self {
		Self { pos, _ty: PhantomData }
	}
}

/// Unwraps a `BitPos` to a `u8`.
impl<T> Into<u8> for BitPos<T>
where T: BitStore {
	fn into(self) -> u8 {
		self.pos
	}
}

impl<T> Display for BitPos<T>
where T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(&self.pos, f)
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

#[cfg(target_pointer_width = "64")]
impl BitStore for u64 {
	const TYPENAME: &'static str = "u64";

	#[cfg(feature = "atomic")]
	type Nucleus = atomic::AtomicU64;

	#[cfg(not(feature = "atomic"))]
	type Nucleus = Cell<Self>;
}

/// Marker trait to seal `BitStore` against downstream implementation.
///
/// This trait is public in the module, so that other modules in the crate can
/// use it, but so long as it is not exported by the crate root and this module
/// is private, this trait effectively forbids downstream implementation of the
/// `BitStore` trait.
#[doc(hidden)]
pub trait Sealed {}

impl Sealed for u8 {}
impl Sealed for u16 {}
impl Sealed for u32 {}

#[cfg(target_pointer_width = "64")]
impl Sealed for u64 {}

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
		let (elt, bit) = BitIdx::<u8>::new(0).offset(isize::max_value());
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
}
