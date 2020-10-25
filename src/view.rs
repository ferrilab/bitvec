/*! [`BitSlice`] view adapters for memory regions.

The [`&BitSlice`][`BitSlice`] type is a referential view over existing memory.
The inherent constructor functions are awkward to call, as they require function
syntax rather than method syntax, and must provide a token for the memory type
argument even though this is informed by the already-existing reference being
used.

This module provides an extension trait, [`BitView`], which provides methods on
many memory types (all [`BitRegister`] integers, and slices and arrays of them)
to construct [`BitSlice`] over those values.

In addition, the traits [`AsBits`] and [`AsBitsMut`] are analogues of [`AsRef`]
and [`AsMut`], respectively. These traits have a blanket implementation for all
`A: As{Ref,Mut}<[T: BitRegister]>`, so that any type that implements a view to a
suitable memory region automatically implements a view to that region’s bits.

These traits are distinct because [`BitView`] combines the im/mutable view
functions into one trait, and can provide specialized implementations with a
slight performance increase over the generic, but `AsBits{,Mut}` can fit in the
generic type system of any library without undue effort.

[`AsBits`]: self::AsBits
[`AsBitsMut`]: self::AsBitsMut
[`AsMut`]: core::convert::AsMut
[`AsRef`]: core::convert::AsRef
[`BitRegister`]: crate::mem::BitRegister
[`BitSlice`]: crate::slice::BitSlice
[`BitView`]: self::BitView
!*/

use crate::{
	index::BitIdx,
	mem::{
		BitMemory,
		BitRegister,
	},
	order::BitOrder,
	ptr::BitPtr,
	slice::BitSlice,
	store::BitStore,
};

/** Creates a [`BitSlice`] view over some type that supports it.

This trait is implemented on all [`BitRegister`] types, and the arrays and slices
of them that are supported by the standard library.

This means that until type-level integers are stabilized, only arrays in
`[T: BitRegister; 0 ..= 64]` will implement the trait; wider arrays will need to
reborrow as slices `[T]` in order to use the slice implementation.

If you have a type that contains a [`BitRegister`] type that can be viewed with
this trait, then you can implement this trait by forwarding to the interior
view.

[`BitSlice`]: crate::slice::BitSlice
[`BitRegister`]: crate::mem::BitRegister
**/
pub trait BitView {
	/// The region’s storage type.
	type Store: BitStore;

	/// Views a memory region as a [`BitSlice`].
	///
	/// # Type Parameters
	///
	/// - `O`: The bit ordering used for the region.
	///
	/// # Parameters
	///
	/// - `&self`: The region to view as individual bits.
	///
	/// # Returns
	///
	/// A `&BitSlice` view over the region at `*self`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder;

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated(
		since = "0.18.0",
		note = "The method is renamed to `.view_bits`"
	)]
	fn bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		self.view_bits::<O>()
	}

	/// Views a memory region as a mutable [`BitSlice`].
	///
	/// # Type Parameters
	///
	/// - `O`: The bit ordering used for the region.
	///
	/// # Parameters
	///
	/// - `&mut self`: The region to view as individual mutable bits.
	///
	/// # Returns
	///
	/// A `&mut BitSlice` view over the region at `*self`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder;

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated(
		since = "0.18.0",
		note = "The method is renamed to `.view_bits_mut`"
	)]
	fn bits_mut<O>(&mut self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		self.view_bits_mut::<O>()
	}

	/// Produces the number of bits that the implementing type can hold.
	#[doc(hidden)]
	fn const_bits() -> usize
	where Self: Sized {
		Self::const_elts() << <<Self::Store as BitStore>::Mem as BitMemory>::INDX
	}

	/// Produces the number of memory elements that the implementing type holds.
	#[doc(hidden)]
	fn const_elts() -> usize
	where Self: Sized;
}

impl<T> BitView for T
where T: BitStore
{
	type Store = T;

	fn view_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element(self)
	}

	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element_mut(self)
	}

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	fn const_elts() -> usize {
		1
	}
}

impl<T> BitView for [T]
where T: BitStore
{
	type Store = T;

	fn view_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice(self).expect("slice was too long to view as bits")
	}

	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice_mut(self)
			.expect("slice was too long to view as bits")
	}

	/// Slices cannot implement this function.
	#[cold]
	#[doc(hidden)]
	#[inline(never)]
	fn const_elts() -> usize {
		unreachable!("This cannot be called on unsized slices")
	}
}

impl<T> BitView for [T; 0]
where T: BitStore
{
	type Store = T;

	fn view_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::empty()
	}

	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::empty_mut()
	}

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	fn const_elts() -> usize {
		0
	}
}

//  Replace with a const-generic once that becomes available.
macro_rules! view_bits {
	($($n:expr),+ $(,)?) => { $(
		impl<T> BitView for [T; $n]
		where T: BitStore {
			type Store = T;

			fn view_bits<O>(&self) -> &BitSlice<O, T>
			where O: BitOrder {
				unsafe {
					BitPtr::new_unchecked(
						self.as_ptr(),
						BitIdx::ZERO,
						$n * T::Mem::BITS as usize,
					)
				}
				.to_bitslice_ref()
			}

			fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
			where O: BitOrder {
				unsafe {
					BitPtr::new_unchecked(
						self.as_mut_ptr(),
						BitIdx::ZERO,
						$n * T::Mem::BITS as usize,
					)
				}
				.to_bitslice_mut()
			}

			#[doc(hidden)]
			fn const_elts() -> usize {
				$n
			}
		}
	)+ };
}

view_bits!(
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
	41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
	60, 61, 62, 63, 64
);

/** Views a region as an immutable [`BitSlice`] only.

This trait is an analogue to the [`AsRef`] trait, in that it enables any type to
provide an immutable-only view of a bit slice.

It does not require an `AsRef<[T: BitStore]>` implementation, and a blanket
implementation for all such types is provided. This allows you to choose whether
to implement only one of `AsBits<T>` or `AsRef<[T]>`, and gain a [`BitSlice`]
view with either choice.

# Type Parameters

- `T`: The underlying storage region.

# Notes

You are not *forbidden* from creating multiple views with different element
types to the same region, but doing so is likely to cause inconsistent and
surprising behavior.

Refrain from implementing this trait with more than one storage argument unless
you are sure that you can uphold the memory region requirements of all of them,
and are aware of the behavior conflicts that may arise.

[`AsRef`]: core::convert::AsRef
[`BitSlice`]: crate::slice::BitSlice
**/
pub trait AsBits<T>
where T: BitStore
{
	/// Views memory as a slice of immutable bits.
	///
	/// # Type Parameters
	///
	/// - `O`: The bit ordering used for the region.
	///
	/// # Parameters
	///
	/// - `&self`: The value that is providing a [`BitSlice`] view.
	///
	/// # Returns
	///
	/// An immutable view into some bits.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	fn as_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder;
}

/** Views a region as a mutable [`BitSlice`].

This trait is an analogue to the [`AsMut`] trait, in that it enables any type to
provide a mutable view of a bit slice.

It does not require an `AsMut<[T: BitStore]>` implementation, and a blanket
implementation for all such types is provided. This allows you to choose whether
to implement only one of `AsBitsMut<T>` or `AsMut<[T]>`, and gain a [`BitSlice`]
view with either choice.

# Type Parameters

- `T`: The underlying storage region.

# Notes

You are not *forbidden* from creating multiple views with different element
types to the same region, but doing so is likely to cause inconsistent and
surprising behavior.

Refrain from implementing this trait with more than one storage argument unless
you are sure that you can uphold the memory region requirements of all of them,
and are aware of the behavior conflicts that may arise.

[`AsMut`]: core::convert::AsMut
[`BitSlice`]: crate::slice::BitSlice
**/
pub trait AsBitsMut<T>
where T: BitStore
{
	/// Views memory as a slice of mutable bits.
	///
	/// # Type Parameters
	///
	/// - `O`: The bit ordering used for the region.
	///
	/// # Parameters
	///
	/// - `&mut self`: The value that is providing a [`BitSlice`] view.
	///
	/// # Returns
	///
	/// A mutable view into some bits.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	fn as_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder;
}

#[cfg(not(tarpaulin_include))]
impl<A, T> AsBits<T> for A
where
	A: AsRef<[T]>,
	T: BitStore + BitRegister,
{
	fn as_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		self.as_ref().view_bits::<O>()
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, T> AsBitsMut<T> for A
where
	A: AsMut<[T]>,
	T: BitStore + BitRegister,
{
	fn as_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		self.as_mut().view_bits_mut::<O>()
	}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	#[test]
	fn impls() {
		let mut data = [0u8; 3];
		let bits = data[..].view_bits_mut::<Msb0>();
		assert_eq!(bits.len(), 24);
		assert!(bits.not_any());
	}
}
