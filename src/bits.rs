/*! Bit Management

The `Bits` trait defines constants and free functions suitable for managing bit
storage of a primitive, and is the constraint for the storage type of a
`BitVec`.
!*/

use core::{
	cmp::Eq,
	convert::From,
	fmt::{
		Binary,
		Debug,
		Display,
		LowerHex,
		UpperHex,
	},
	mem::size_of,
	ops::{
		Not,
		BitAnd,
		BitAndAssign,
		BitOrAssign,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
};

/// A trait for types that can be used as direct storage of bits.
///
/// This trait must only be implemented on unsigned integer primitives.
///
/// The dependency on `Sealed`, a crate-private trait, ensures that this trait
/// can only ever be implemented locally, and no downstream crates are able to
/// implement it on new types.
pub trait Bits:
	//  Forbid external implementation
	Sealed
	+ Binary
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
	+ LowerHex
	+ Not<Output=Self>
	+ Shl<u8, Output=Self>
	+ ShlAssign<u8>
	+ Shr<u8, Output=Self>
	+ ShrAssign<u8>
	//  Allow direct access to a concrete implementor type.
	+ Sized
	+ UpperHex
{
	/// The width in bits of this type.
	const WIDTH: u8 = size_of::<Self>() as u8 * 8;

	/// The number of bits required to *index* the type. This is always
	/// log<sub>2</sub> of the type width.
	///
	/// Incidentally, this can be computed as `size_of().trailing_zeros()` once
	/// that becomes a valid constexpr.
	const BITS: u8; // = size_of::<Self>().trailing_zeros() as u8;

	/// The bitmask to turn an arbitrary usize into the bit index. Bit indices
	/// are always stored in the lowest bits of an index value.
	const MASK: u8 = Self::WIDTH - 1;

	/// The maximum number of this type that can be held in a `BitVec`.
	const MAX_ELT: usize = core::usize::MAX >> Self::BITS;

	/// Set a specific bit in an element to a given value.
	fn set(&mut self, place: u8, value: bool) {
		assert!(place <= Self::MASK, "Index out of range");
		//  Blank the selected bit
		*self &= !(Self::from(1u8) << place);
		//  Set the selected bit
		*self |= Self::from(value as u8) << place;
	}

	/// Get a specific bit in an element.
	fn get(&self, place: u8) -> bool {
		assert!(place <= Self::MASK, "Index out of range");
		//  Shift down so the targeted bit is LSb, then blank all other bits.
		(*self >> place) & Self::from(1) == Self::from(1)
	}

	/// Counts how many bits are set.
	#[inline(always)]
	fn ones(&self) -> usize;

	/// Counts how many bits are unset.
	#[inline(always)]
	fn zeros(&self) -> usize;

	/// Splits a `usize` cursor into an (element, bit) tuple.
	///
	/// The bit component is semantic count, not bit index.
	fn split(cursor: usize) -> (usize, u8) {
		(cursor >> Self::BITS, (cursor & Self::MASK as usize) as u8)
	}

	/// Joins a `usize` element cursor and `u8` bit cursor into a single
	/// `usize` cursor.
	fn join(elt: usize, bit: u8) -> usize {
		assert!(elt <= core::usize::MAX >> Self::BITS, "Element count out of range!");
		assert!(bit <= Self::MASK, "Bit count out of range!");
		(elt << Self::BITS) | bit as usize
	}

	/// Rust doesn’t (as far as I know) have a way to render a typename at
	/// runtime, so this constant holds the typename of the primitive for
	/// printing by Debug.
	#[doc(hidden)]
	const TY: &'static str;
}

impl Bits for u8 {
	const BITS: u8 = 3;

	#[inline(always)]
	fn ones(&self) -> usize {
		self.count_ones() as usize
	}

	#[inline(always)]
	fn zeros(&self) -> usize {
		self.count_zeros() as usize
	}

	const TY: &'static str = "u8";
}

impl Bits for u16 {
	const BITS: u8 = 4;

	#[inline(always)]
	fn ones(&self) -> usize {
		self.count_ones() as usize
	}

	#[inline(always)]
	fn zeros(&self) -> usize {
		self.count_zeros() as usize
	}

	const TY: &'static str = "u16";
}

impl Bits for u32 {
	const BITS: u8 = 5;

	#[inline(always)]
	fn ones(&self) -> usize {
		self.count_ones() as usize
	}

	#[inline(always)]
	fn zeros(&self) -> usize {
		self.count_zeros() as usize
	}

	const TY: &'static str = "u32";
}

//  Boy I sure hope nobody tries to use this on middle-endian systems or where
//  the layout of a u64 is not guaranteed to be continuous between 32-bit halves
impl Bits for u64 {
	const BITS: u8 = 6;

	#[inline(always)]
	fn ones(&self) -> usize {
		self.count_ones() as usize
	}

	#[inline(always)]
	fn zeros(&self) -> usize {
		self.count_zeros() as usize
	}

	const TY: &'static str = "u64";
}

//  Do NOT implement on u128. They are aligned to 8 bytes, not to 16.

/// Marker trait to seal `Bits` against downstream implementation
///
/// This trait is public in the module, so that other modules in the crate can
/// use it, but so long as it is not exported by the crate root and this module
/// is private, this trait effectively forbids downstream implementation of
/// `Bits`.
#[doc(hidden)]
pub trait Sealed {}

impl Sealed for u8 {}
impl Sealed for u16 {}
impl Sealed for u32 {}
impl Sealed for u64 {}
