/*! Bit management

The `BitStore` trait defines constants and associated functions suitable for
managing the bit patterns of a fundamental, and is the constraint for the
storage type of the data structures of the rest of the crate.

The other types in this module provide stronger rules about how indices map to
concrete bits in fundamental elements. They are implementation details, and are
not exported in the prelude.
!*/

use crate::{
	access::BitAccess,
	indices::BitIdx,
	order::BitOrder,
};

use core::{
	cmp::Eq,
	convert::{
		From,
		TryInto,
	},
	fmt::{
		Binary,
		Debug,
		Display,
		LowerHex,
		UpperHex,
	},
	marker::{
		Send,
		Sync,
	},
	mem::size_of,
	ops::{
		BitAnd,
		BitAndAssign,
		BitOr,
		BitOrAssign,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
	slice,
};

use radium::marker::BitOps;

#[cfg(feature = "atomic")]
use core::sync::atomic;

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
	+ BitAnd<Self, Output = Self>
	+ BitAndAssign<Self>
	+ BitOr<Self, Output = Self>
	+ BitOrAssign<Self>
	//  Permit indexing into a generic array
	+ Copy
	+ Debug
	+ Display
	//  Permit testing a value against 0 in `get()`.
	+ Eq
	//  Rust treats numeric literals in code as vaguely typed and does not make
	//  them concrete until long after trait expansion, so this enables building
	//  a concrete Self value from a numeric literal.
	+ From<u8>
	//  Permit extending into a `u64`.
	+ Into<u64>
	+ LowerHex
	+ Not<Output = Self>
	+ Send
	+ Shl<u8, Output = Self>
	+ ShlAssign<u8>
	+ Shr<u8, Output = Self>
	+ ShrAssign<u8>
	//  Allow direct access to a concrete implementor type.
	+ Sized
	+ Sync
	+ UpperHex
	+ BitOps
{
	/// The width, in bits, of this type.
	const BITS: u8 = size_of::<Self>() as u8 * 8;

	/// The number of bits required to index a bit inside the type. This is
	/// always log<sub>2</sub> of the type’s bit width.
	const INDX: u8 = Self::BITS.trailing_zeros() as u8;

	/// The bitmask to turn an arbitrary number into a bit index. Bit indices
	/// are always stored in the lowest bits of an index value.
	const MASK: u8 = Self::BITS - 1;

	/// The value with all bits unset.
	const FALSE: Self;

	/// The value with all bits set.
	const TRUE: Self;

	/// Name of the implementing type. This is only necessary until the compiler
	/// stabilizes `type_name()`.
	const TYPENAME: &'static str;

	/// Shared/mutable access wrapper.
	///
	/// Within `&BitSlice` and `&mut BitSlice` contexts, the `Access` type
	/// governs all access to underlying memory that may be contended by
	/// multiple slices. When a codepath knows that it has full, uncontended
	/// ownership of a memory element of `Self`, and no other codepath may
	/// observe or modify it, then that codepath may skip the `Access` type and
	/// use plain accessors.
	type Access: BitAccess<Self>;

	/// Gets a specific bit in an element.
	///
	/// # Safety
	///
	/// This method cannot be called from within an `&BitSlice` context; it may
	/// only be called by construction of an `&Self` reference from a `Self`
	/// element directly.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `place`: A bit index in the element. The bit under this index, as
	///   governed by the `O` `BitOrder`, will be retrieved as a `bool`.
	///
	/// # Returns
	///
	/// The value of the bit under `place`.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation to translate the index into a position.
	fn get<O>(&self, place: BitIdx<Self>) -> bool
	where O: BitOrder {
		*self & *O::mask(place) != Self::FALSE
	}

	/// Sets a specific bit in an element to a given value.
	///
	/// # Safety
	///
	/// This method cannot be called from within an `&mut BitSlice` context; it
	/// may only be called by construction of an `&mut Self` reference from a
	/// `Self` element directly.
	///
	/// # Parameters
	///
	/// - `place`: A bit index in the element. The bit under this index, as
	///   governed by the `O` `BitOrder`, will be set according to `value`.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation to translate the index into a position.
	fn set<O>(&mut self, place: BitIdx<Self>, value: bool)
	where O: BitOrder {
		let mask = *O::mask(place);
		if value {
			*self |= mask;
		}
		else {
			*self &= !mask;
		}
	}

	/// Counts how many bits in `self` are set to `1`.
	///
	/// This zero-extends `self` to `u64`, and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `self`
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
	/// assert_eq!(BitStore::count_ones(0u8), 0);
	/// assert_eq!(BitStore::count_ones(128u8), 1);
	/// assert_eq!(BitStore::count_ones(192u8), 2);
	/// assert_eq!(BitStore::count_ones(224u8), 3);
	/// assert_eq!(BitStore::count_ones(240u8), 4);
	/// assert_eq!(BitStore::count_ones(248u8), 5);
	/// assert_eq!(BitStore::count_ones(252u8), 6);
	/// assert_eq!(BitStore::count_ones(254u8), 7);
	/// assert_eq!(BitStore::count_ones(255u8), 8);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_ones(self) -> usize {
		Into::<u64>::into(self).count_ones() as usize
	}

	/// Counts how many bits in `self` are set to `0`.
	///
	/// This inverts `self`, so all `0` bits are `1` and all `1` bits are `0`,
	/// then zero-extends `self` to `u64` and uses the [`u64::count_ones`]
	/// inherent method.
	///
	/// # Parameters
	///
	/// - `self`
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
	/// assert_eq!(BitStore::count_zeros(0u8), 8);
	/// assert_eq!(BitStore::count_zeros(1u8), 7);
	/// assert_eq!(BitStore::count_zeros(3u8), 6);
	/// assert_eq!(BitStore::count_zeros(7u8), 5);
	/// assert_eq!(BitStore::count_zeros(15u8), 4);
	/// assert_eq!(BitStore::count_zeros(31u8), 3);
	/// assert_eq!(BitStore::count_zeros(63u8), 2);
	/// assert_eq!(BitStore::count_zeros(127u8), 1);
	/// assert_eq!(BitStore::count_zeros(255u8), 0);
	/// ```
	///
	/// [`u64::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.u64.html#method.count_ones
	#[inline(always)]
	fn count_zeros(self) -> usize {
		//  invert (0 becomes 1, 1 becomes 0), zero-extend, count ones
		Into::<u64>::into(!self).count_ones() as usize
	}

	/// Interprets a value as a sequence of bytes.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice covering `*self` as a sequence of individual bytes.
	fn as_bytes(&self) -> &[u8];

	/// Interprets a sequence of bytes as `Self`.
	///
	/// # Parameters
	///
	/// - `bytes`: The bytes to interpret as `Self`. This must be exactly
	///   `mem::size_of::<Self>` bytes long.
	///
	/// # Returns
	///
	/// An instance of `Self` constructed by reinterpreting `bytes`.
	///
	/// # Panics
	///
	/// This panics if `bytes.len()` is not `mem::size_of::<Self>()`.
	fn from_bytes(bytes: &[u8]) -> Self;
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
	let width: usize = size_of::<T>() * 8;
	bits / width + (bits % width != 0) as usize
}

impl BitStore for u8 {
	const TYPENAME: &'static str = "u8";

	const FALSE: Self = 0;
	const TRUE: Self = !0;

	#[cfg(feature = "atomic")]
	type Access = atomic::AtomicU8;

	#[cfg(not(feature = "atomic"))]
	type Access = Cell<Self>;

	#[inline]
	fn as_bytes(&self) -> &[u8] {
		unsafe { slice::from_raw_parts(self as *const Self as *const u8, 1) }
	}

	#[inline]
	fn from_bytes(bytes: &[u8]) -> Self {
		bytes
			.try_into()
			.map(Self::from_ne_bytes)
			.expect("<u8 as BitStore>::from_bytes requires a slice of length 1")
	}
}

impl BitStore for u16 {
	const TYPENAME: &'static str = "u16";

	const FALSE: Self = 0;
	const TRUE: Self = !0;

	#[cfg(feature = "atomic")]
	type Access = atomic::AtomicU16;

	#[cfg(not(feature = "atomic"))]
	type Access = Cell<Self>;

	#[inline]
	fn as_bytes(&self) -> &[u8] {
		unsafe { slice::from_raw_parts(self as *const Self as *const u8, 2) }
	}

	#[inline]
	fn from_bytes(bytes: &[u8]) -> Self {
		bytes
			.try_into()
			.map(Self::from_ne_bytes)
			.expect("<u16 as BitStore>::from_bytes requires a slice of length 2")
	}
}

impl BitStore for u32 {
	const TYPENAME: &'static str = "u32";

	const FALSE: Self = 0;
	const TRUE: Self = !0;

	#[cfg(feature = "atomic")]
	type Access = atomic::AtomicU32;

	#[cfg(not(feature = "atomic"))]
	type Access = Cell<Self>;

	#[inline]
	fn as_bytes(&self) -> &[u8] {
		unsafe { slice::from_raw_parts(self as *const Self as *const u8, 4) }
	}

	#[inline]
	fn from_bytes(bytes: &[u8]) -> Self {
		bytes
			.try_into()
			.map(Self::from_ne_bytes)
			.expect("<u32 as BitStore>::from_bytes requires a slice of length 4")
	}
}

#[cfg(target_pointer_width = "64")]
impl BitStore for u64 {
	const TYPENAME: &'static str = "u64";

	const FALSE: Self = 0;
	const TRUE: Self = !0;

	#[cfg(feature = "atomic")]
	type Access = atomic::AtomicU64;

	#[cfg(not(feature = "atomic"))]
	type Access = Cell<Self>;

	#[inline]
	fn as_bytes(&self) -> &[u8] {
		unsafe { slice::from_raw_parts(self as *const Self as *const u8, 8) }
	}

	#[inline]
	fn from_bytes(bytes: &[u8]) -> Self {
		bytes
			.try_into()
			.map(Self::from_ne_bytes)
			.expect("<u64 as BitStore>::from_bytes requires a slice of length 8")
	}
}

/** A default word size for bit sequences.

The target has 32-bit CPU words, so `u32` is a good default unit size.
**/
#[cfg(target_pointer_width = "32")]
pub type Word = u32;

/** A default word size for bit sequences.

The target has 64-bit CPU words, so `u64` is a good default unit size.
**/
#[cfg(target_pointer_width = "64")]
pub type Word = u64;

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_fail!("This architecture is currently not supported. File an issue at https://github.com/myrrlyn/bitvec");

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
