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
	convert::TryInto,
	fmt::{
		Binary,
		Debug,
		Display,
		LowerHex,
		UpperHex,
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
	//  Permit extending into a `usize`.
	+ TryInto<usize>
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
	/// This zero-extends `self` to `usize`, and uses the [`usize::count_ones`]
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
	/// [`usize::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.usize.html#method.count_ones
	#[inline(always)]
	fn count_ones(self) -> usize {
		let extended = self.try_into()
			.unwrap_or_else(|_| unreachable!("This conversion is infallible"));
		//  Ensure that this calls the inherent method in `impl usize`, not the
		//  trait method in `impl BitStore for usize`.
		usize::count_ones(extended) as usize
	}

	/// Counts how many bits in `self` are set to `0`.
	///
	/// This inverts `self`, so all `0` bits are `1` and all `1` bits are `0`,
	/// then zero-extends `self` to `usize` and uses the [`usize::count_ones`]
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
	/// [`usize::count_ones`]: https://doc.rust-lang.org/stable/std/primitive.usize.html#method.count_ones
	#[inline(always)]
	fn count_zeros(self) -> usize {
		//  invert (0 becomes 1, 1 becomes 0), zero-extend, count ones
		<Self as BitStore>::count_ones(!self)
	}
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

/// Batch implementation of `BitStore` for the appropriate fundamental integers.
macro_rules! bitstore {
	($($t:ty => $bits:literal , $atom:ty ;)*) => { $(
		impl BitStore for $t {
			const TYPENAME: &'static str = stringify!($t);

			const FALSE: Self = 0;
			const TRUE: Self = !0;

			#[cfg(feature = "atomic")]
			type Access = $atom;

			#[cfg(not(feature = "atomic"))]
			type Access = Cell<Self>;

			#[inline(always)]
			fn count_ones(self) -> usize {
				Self::count_ones(self) as usize
			}
		}
	)* };
}

bitstore! {
	u8 => 1, atomic::AtomicU8;
	u16 => 2, atomic::AtomicU16;
	u32 => 4, atomic::AtomicU32;
}

#[cfg(target_pointer_width = "32")]
bitstore! {
	usize => 4, atomic::AtomicUsize;
}

#[cfg(target_pointer_width = "64")]
bitstore! {
	u64 => 8, atomic::AtomicU64;
	usize => 8, atomic::AtomicUsize;
}

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

macro_rules! seal {
	($($t:ty),*) => { $(
		impl Sealed for $t {}
	)* };
}

seal!(u8, u16, u32, usize);

#[cfg(target_pointer_width = "64")]
seal!(u64);
