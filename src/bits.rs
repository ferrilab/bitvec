/*! Permit use of Rust native types as bit collections.

This module exposes a trait, `Bits`, which functions similarly to the `AsRef`
and `AsMut` traits in the standard library. This trait allows an implementor to
express the means by which it can be interpreted as a collection of bits.
!*/

use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

/** Allows a type to be used as a sequence of immutable bits.

# Requirements

This trait can only be implemented by contiguous structures: individual
fundamentals, and sequences (arrays or slices) of them.
**/
pub trait Bits {
	/// The underlying fundamental type of the implementor.
	type Store: BitStore;

	/// Constructs a `BitSlice` reference over data.
	///
	/// # Type Parameters
	///
	/// - `O: BitOrder`: The `BitOrder` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `BitOrder`
	/// type and using `Self::Store` as the data type.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 8u8;
	/// let bits = src.bits::<Msb0>();
	/// assert!(bits[4]);
	/// ```
	fn bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder;

	/// Synonym for [`bits`](#method.bits).
	#[deprecated(since = "0.16.0", note = "Use `Bits::bits` instead")]
	fn as_bitslice<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		Bits::bits(self)
	}

	/// Constructs a mutable `BitSlice` reference over data.
	///
	/// # Type Parameters
	///
	/// - `O: BitOrder`: The `BitOrder` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `BitOrder`
	/// type and using `Self::Store` as the data type.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 8u8;
	/// let bits = src.bits_mut::<Lsb0>();
	/// assert!(bits[3]);
	/// *bits.at(3) = false;
	/// assert!(!bits[3]);
	/// ```
	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder;

	/// Synonym for [`bits_mut`](#method.bits_mut).
	#[deprecated(since = "0.16.0", note = "Use `Bits::bits_mut` instead")]
	fn as_mut_bitslice<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder {
		Bits::bits_mut(self)
	}
}

impl<T> Bits for T
where T: BitStore {
	type Store = T;
	fn bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element(self)
	}

	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element_mut(self)
	}
}

impl<T> Bits for [T]
where T: BitStore {
	type Store = T;
	fn bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice(self)
	}

	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice_mut(self)
	}
}

macro_rules! impl_bits_for {
	($( $n:expr ),* ) => { $(
		impl<T> Bits for [T; $n]
		where T: BitStore {
			type Store = T;
			fn bits<O>(&self) -> &BitSlice<O, T>
			where O: BitOrder {
				BitSlice::from_slice(self)
			}
			fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
			where O: BitOrder {
				BitSlice::from_slice_mut(self)
			}
		}
	)* };
}

impl_bits_for![
	0, 1, 2, 3, 4, 5, 6, 7,
	8, 9, 10, 11, 12, 13, 14, 15,
	16, 17, 18, 19, 20, 21, 22, 23,
	24, 25, 26, 27, 28, 29, 30, 31,
	32
];
