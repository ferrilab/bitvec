/*! View constructors for memory regions.

The `&BitSlice` type is a referential view over existing memory. The inherent
constructors are awkward to call, as they require function syntax rather than
method syntax, and must provide a token for the memory type even though this is
provided by the prior binding.

This module provides a view trait, `ViewBits`, which provides `BitSlice`
constructors available in method-call syntax with only ordering type parameters.

In addition, the traits `AsBits` and `AsBitsMut` are analogues of [`AsRef`] and
[`AsMut`], respectively. These traits have a blanket implementation for all
`A: As{Ref,Mut}<[T: BitStore]>`, so that any type that implements a view to a
suitable memory region automatically implements a view to that region’s bits.

These traits are distinct because `ViewBits` combines the im/mutable view
functions into one trait, and can provide specialized implementations with a
slight performance increase over the generic, but `AsBits{,Mut}` can fit in the
generic type system of any library without undue effort.

[`AsMut`]: https://doc.rust-lang.org/core/convert/trait.AsMut.html
[`AsRef`]: https://doc.rust-lang.org/core/convert/trait.AsRef.html
!*/

#![cfg_attr(tarpaulin, skip)]

use crate::{
	index::BitIdx,
	mem::BitMemory,
	order::BitOrder,
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
};

/** Views a type that can store bits as a bit-slice.

This trait is implemented on all `T: BitStore` types, and the arrays and slices
of them that are supported by the standard library.

This means that until type-level integers are stabilized, only arrays in
`[T: BitStore; 0 ..= 32]` will implement the trait; wider arrays will need to
reborrow as slices `[T]` in order to use the slice implementation.

If you have a type that contains a bit-storage type that can be viewed with this
trait, then you can implement this trait by forwarding to the interior view.
**/
pub trait BitView {
	/// The underlying memory type of the storage region.
	type Store: BitStore;

	/// Views a memory region as a `BitSlice`.
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
	fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder;

	/// Views a memory region as a mutable `BitSlice`.
	///
	/// # Type Parameters
	///
	/// - `O`: The bit ordering used for the region.
	///
	/// # Parameters
	///
	/// - `&self`: The region to view as individual mutable bits.
	///
	/// # Returns
	///
	/// A `&mut BitSlice` view over the region at `*self`.
	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder;

	/// Produces the number of bits that the implementing type can hold.
	#[doc(hidden)]
	fn const_bits() -> usize
	where Self: Sized;
}

impl<T> BitView for T
where T: BitStore
{
	type Store = Self;

	#[inline(always)]
	fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::from_element(self)
	}

	#[inline(always)]
	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::from_element_mut(self)
	}

	#[inline(always)]
	#[doc(hidden)]
	fn const_bits() -> usize {
		T::Mem::BITS as usize
	}
}

impl<T> BitView for [T]
where T: BitStore
{
	type Store = T;

	#[inline(always)]
	fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::from_slice(self).expect("slice was too long to view as bits")
	}

	#[inline(always)]
	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::from_slice_mut(self)
			.expect("slice was too long to view as bits")
	}

	/// Slices cannot implement this function.
	#[cold]
	#[doc(hidden)]
	#[inline(never)]
	fn const_bits() -> usize {
		unreachable!("This cannot be called on unsized slices")
	}
}

impl<T> BitView for [T; 0]
where T: BitStore
{
	type Store = T;

	#[inline(always)]
	fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::empty()
	}

	#[inline(always)]
	fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder {
		BitSlice::empty_mut()
	}

	#[doc(hidden)]
	#[inline(always)]
	fn const_bits() -> usize {
		0
	}
}

//  Replace with a const-generic once that becomes available.
macro_rules! view_bits {
	($($n:expr),+ $(,)?) => { $(
		impl<T> BitView for [T; $n]
		where T: BitStore {
			type Store = T;

			#[inline]
			fn view_bits<O>(&self) -> &BitSlice<O, Self::Store>
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

			#[inline]
			fn view_bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
			where O: BitOrder {
				unsafe {
					BitPtr::new_unchecked(
						self.as_ptr(),
						BitIdx::ZERO,
						$n * T::Mem::BITS as usize,
					)
				}
				.to_bitslice_mut()
			}

			#[doc(hidden)]
			#[inline(always)]
			fn const_bits() -> usize {
				$n * T::Mem::BITS as usize
			}
		}
	)+ };
}

view_bits!(
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32
);

/** Views a region as an immutable bit-slice only.

This trait is an analogue to the [`AsRef`] trait, in that it enables any type to
provide an immutable-only view of a bit slice.

It does not require an `AsRef<[T: BitStore]>` implementation, and a blanket
implementation for all such types is provided. This allows you to choose whether
to implement only one of `AsBits<T>` or `AsRef<[T]>`, and gain a bit-slice view
with either choice.

# Type Parameters

- `T`: The underlying storage region.

# Notes

You are not *forbidden* from creating multiple views with different element
types to the same region, but doing so is likely to cause inconsistent and
unsurprising behavior.

Refrain from implementing this trait with more than one storage argument unless
you are sure that you can uphold the memory region requirements of all of them,
and are aware of the behavior conflicts that may arise.

[`AsRef`]: https://doc.rust-lang.org/core/convert/trait.AsRef.html
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
	/// - `&self`: The value that is providing a bit-slice view.
	///
	/// # Returns
	///
	/// An immutable view into some bits.
	fn as_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder;
}

/** Views a region as a mutable bit-slice.

This trait is an analogue to the [`AsMut`] trait, in that it enables any type to
provide a mutable view of a bit slice.

It does not require an `AsMut<[T: BitStore]>` implementation, and a blanket
implementation for all such types is provided. This allows you to choose whether
to implement only one of `AsBitsMut<T>` or `AsMut<[T]>`, and gain a bit-slice
view with either choice.

# Type Parameters

- `T`: The underlying storage region.

# Notes

You are not *forbidden* from creating multiple views with different element
types to the same region, but doing so is likely to cause inconsistent and
unsurprising behavior.

Refrain from implementing this trait with more than one storage argument unless
you are sure that you can uphold the memory region requirements of all of them,
and are aware of the behavior conflicts that may arise.

[`AsMut`]: https://doc.rust-lang.org/core/convert/trait.AsMut.html
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
	/// - `&mut self`: The value that is providing a bit-slice view.
	///
	/// # Returns
	///
	/// A mutable view into some bits.
	fn as_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder;
}

impl<A, T> AsBits<T> for A
where
	A: AsRef<[T]>,
	T: BitStore,
{
	#[inline]
	fn as_bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		self.as_ref().view_bits::<O>()
	}
}

impl<A, T> AsBitsMut<T> for A
where
	A: AsMut<[T]>,
	T: BitStore,
{
	#[inline]
	fn as_bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		self.as_mut().view_bits_mut::<O>()
	}
}
