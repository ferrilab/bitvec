/*! Permit use of Rust native types as bit collections.

This module exposes two traits, `Bits` and `BitsMut`, which function similarly
to the `AsRef` and `AsMut` traits in the standard library. These traits allow an
implementor to express the means by which it can be interpreted as a collection
of bits.

Trait coherence rules forbid the following blanket implementation,

```rust,ignore
impl<C: Cursor, T: Bits> AsRef<BitSlice<C, T::Store>> for T {
  fn as_ref(&self) -> &BitSlice<C, T::Store> {
    Bits::as_bitslice(self)
  }
}
impl<C: Cursor, T: BitsMut> AsMut<BitSlice<C, T::Store>> for T {
  fn as_ref(&mut self) -> &mut BitSlice<C, T::Store> {
    BitsMut::as_mut_bitslice(self)
  }
}
```

but it is correct in theory, and so all types which implement `Bits` should
implement `AsRef<BitSlice>` and all types which implement `BitsMut` should
implement `AsMut<BitSlice>`.
!*/

use crate::{
	cursor::Cursor,
	slice::BitSlice,
	store::BitStore,
};

use core::convert::{
	AsMut,
	AsRef,
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
	/// - `C: Cursor`: The `Cursor` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `Cursor` type
	/// and using `Self::Store` as the data type.
	fn as_bitslice<C>(&self) -> &BitSlice<C, Self::Store>
	where C: Cursor;
}

/** Allows a type to be used as a sequence of mutable bits.

# Requirements

This trait can only be implemented by contiguous structures: individual
fundamentals, and sequences (arrays or slices) of them.
**/
pub trait BitsMut: Bits {
	/// Constructs a mutable `BitSlice` reference over data.
	///
	/// # Type Parameters
	///
	/// - `C: Cursor`: The `Cursor` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `Cursor` type
	/// and using `Self::Store` as the data type.
	fn as_mut_bitslice<C>(&mut self) -> &mut BitSlice<C, Self::Store>
	where C: Cursor;
}

macro_rules! impl_bits_for {
	( $( $t:ty ),* ) => { $(
impl<C> AsMut<BitSlice<C, $t>> for $t
where C: Cursor {
	fn as_mut(&mut self) -> &mut BitSlice<C, $t> {
		BitsMut::as_mut_bitslice(self)
	}
}

impl<C> AsRef<BitSlice<C, $t>> for $t
where C: Cursor {
	fn as_ref(&self) -> &BitSlice<C, $t> {
		Bits::as_bitslice(self)
	}
}

impl Bits for $t {
	type Store = $t;

	fn as_bitslice<C>(&self) -> &BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_element(self)
	}
}

impl BitsMut for $t {
	fn as_mut_bitslice<C>(&mut self) -> &mut BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_element_mut(self)
	}
}

impl<C> AsMut<BitSlice<C, $t>> for [$t]
where C: Cursor {
	fn as_mut(&mut self) -> &mut BitSlice<C, $t> {
		BitsMut::as_mut_bitslice(self)
	}
}

impl<C> AsRef<BitSlice<C, $t>> for [$t]
where C: Cursor {
	fn as_ref(&self) -> &BitSlice<C, $t> {
		Bits::as_bitslice(self)
	}
}

impl Bits for [$t] {
	type Store = $t;

	fn as_bitslice<C>(&self) -> &BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_slice(self)
	}
}

impl BitsMut for [$t] {
	fn as_mut_bitslice<C>(&mut self) -> &mut BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_slice_mut(self)
	}
}

impl<C> AsMut<BitSlice<C, $t>> for [$t; 0]
where C: Cursor {
	fn as_mut(&mut self) -> &mut BitSlice<C, $t> {
		BitsMut::as_mut_bitslice(self)
	}
}

impl<C> AsRef<BitSlice<C, $t>> for [$t; 0]
where C: Cursor {
	fn as_ref(&self) -> &BitSlice<C, $t> {
		Bits::as_bitslice(self)
	}
}

impl Bits for [$t; 0] {
	type Store = $t;

	fn as_bitslice<C>(&self) -> &BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::empty()
	}
}

impl BitsMut for [$t; 0] {
	fn as_mut_bitslice<C>(&mut self) -> &mut BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::empty_mut()
	}
}

impl_bits_for! { array $t ;
	    1  2  3  4  5  6  7  8  9
	10 11 12 13 14 15 16 17 18 19
	20 21 22 23 24 25 26 27 28 29
	30 31 32 // going above 32 is a DoS attack on the compiler
}
	)* };

	( array $t:ty ; $( $n:expr )* ) => { $(
impl<C> AsMut<BitSlice<C, $t>> for [$t; $n]
where C: Cursor {
	fn as_mut(&mut self) -> &mut BitSlice<C, $t> {
		BitsMut::as_mut_bitslice(self)
	}
}

impl<C> AsRef<BitSlice<C, $t>> for [$t; $n]
where C: Cursor {
	fn as_ref(&self) -> &BitSlice<C, $t> {
		Bits::as_bitslice(self)
	}
}

impl Bits for [$t; $n] {
	type Store = $t;

	fn as_bitslice<C>(&self) -> &BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_slice(&self[..])
	}
}

impl BitsMut for [$t; $n] {
	fn as_mut_bitslice<C>(&mut self) -> &mut BitSlice<C, Self::Store>
	where C: Cursor {
		BitSlice::from_slice_mut(&mut self[..])
	}
}
	)* };
}

impl_bits_for! { u8, u16, u32 }

#[cfg(target_pointer_width = "64")]
impl_bits_for! { u64 }
