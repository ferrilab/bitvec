//! By-value buffer iteration.

use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::FusedIterator,
};

use super::BitBox;
use crate::{
	order::BitOrder,
	ptr::{
		BitPtrRange,
		Mut,
	},
	slice::BitSlice,
	store::BitStore,
};
/// This is not present on `Box<[T]>`, but is needed to fit into the general
/// operator implementations.
#[cfg(not(tarpaulin_include))]
impl<O, T> IntoIterator for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = IntoIter<O, T>;
	type Item = bool;

	#[inline(always)]
	fn into_iter(self) -> Self::IntoIter {
		IntoIter::new(self)
	}
}

/** An iterator that moves out of a [`BitVec`].

This `struct` is created by the [`into_iter`] method on [`BitVec`] (provided by
the [`IntoIterator`] trait).

# Original

[`vec::IntoIter`](alloc::vec::IntoIter)

[`BitVec`]: crate::vec::BitVec
[`IntoIterator`]: core::iter::IntoIterator
[`into_iter`]: core::iter::IntoIterator::into_iter
**/
pub struct IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The buffer being iterated.
	_buf: BitBox<O, T>,
	/// A bit-pointer iterator over the buffer’s contents.
	iter: BitPtrRange<Mut, O, T>,
}

impl<O, T> IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Constructs an iterator over a [`BitBox`] or [`BitVec`].
	///
	/// [`BitBox`]: crate::vec::BitBox
	/// [`BitVec`]: crate::vec::BitVec
	fn new(mut this: BitBox<O, T>) -> Self {
		let iter = this.as_mut_bitptr_range();
		Self { _buf: this, iter }
	}

	/// Returns the remaining bits of this iterator as a [`BitSlice`].
	///
	/// # Original
	///
	/// [`vec::IntoIter::as_slice`](alloc::vec::IntoIter::as_slice)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 0, 1];
	/// let mut into_iter = bv.into_iter();
	///
	/// assert_eq!(into_iter.as_bitslice(), bits![0, 1, 0, 1]);
	/// let _ = into_iter.next().unwrap();
	/// assert_eq!(into_iter.as_bitslice(), bits![1, 0, 1]);
	/// ```
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn as_bitslice(&self) -> &BitSlice<O, T> {
		self.iter.clone().into_bitspan().to_bitslice_ref()
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpalin_include))]
	#[deprecated = "Use `as_bitslice` to view the underlying slice"]
	pub fn as_slice(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}

	/// Returns the remaining bits of this iterator as a mutable [`BitSlice`].
	///
	/// # Original
	///
	/// [`vec::IntoIter::as_mut_slice`](alloc::vec::IntoIter::as_mut_slice)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 0, 1];
	/// let mut into_iter = bv.into_iter();
	///
	/// assert_eq!(into_iter.as_bitslice(), bits![0, 1, 0, 1]);
	/// into_iter.as_mut_bitslice().set(2, true);
	/// assert!(!into_iter.next().unwrap());
	/// assert!(into_iter.next().unwrap());
	/// assert!(into_iter.next().unwrap());
	/// ```
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, T> {
		self.iter.clone().into_bitspan().to_bitslice_mut()
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `as_mut_bitslice` to view the underlying slice"]
	pub fn as_mut_slice(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Debug for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("IntoIter")
			.field(&self.as_bitslice())
			.finish()
	}
}

impl<O, T> Iterator for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next().map(crate::ptr::range::read_raw)
	}

	#[inline(always)]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	#[inline(always)]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth(n).map(crate::ptr::range::read_raw)
	}

	#[inline(always)]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T> DoubleEndedIterator for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back().map(crate::ptr::range::read_raw)
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth_back(n).map(crate::ptr::range::read_raw)
	}
}

impl<O, T> ExactSizeIterator for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn len(&self) -> usize {
		self.iter.len()
	}
}

impl<O, T> FusedIterator for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}
