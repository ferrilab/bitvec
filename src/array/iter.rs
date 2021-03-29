//! Array iteration.

use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::FusedIterator,
	ops::Range,
};

use tap::pipe::Pipe;

use super::BitArray;
use crate::{
	order::BitOrder,
	ptr::{
		BitPtr,
		Const,
	},
	slice::BitSlice,
	view::BitViewSized,
};

/** A by-value [bit-array] iterator.

# Original

[`array::IntoIter`](core::array::IntoIter)

[bit-array]: crate::array::BitArray
[`BitView`]: crate::view::BitView
**/
#[derive(Clone)]
pub struct IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	/// The array being iterated.
	array: BitArray<O, V>,

	/// The bits in `array` that have not yet been yielded.
	///
	/// Invariants:
	/// - `alive.start <= alive.end`
	/// - `alive.end <= V::BITS`
	alive: Range<usize>,
}

impl<O, V> IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	/// Creates a new iterator over the given `array`.
	///
	/// # Original
	///
	/// [`IntoIter::new`](core::array::IntoIter::new)
	#[inline]
	pub(super) fn new(array: BitArray<O, V>) -> Self {
		Self {
			array,
			alive: 0 .. V::BITS,
		}
	}

	/// Returns an immutable slice of all bits that have not been yielded yet.
	///
	/// # Original
	///
	/// [`IntoIter::as_slice`](core::array::IntoIter::as_slice)
	#[inline]
	pub fn as_bitslice(&self) -> &BitSlice<O, V::Store> {
		unsafe { self.array.as_bitslice().get_unchecked(self.alive.clone()) }
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `as_bitslice` to view the underlying slice"]
	pub fn as_slice(&self) -> &BitSlice<O, V::Store> {
		self.as_bitslice()
	}

	/// Returns a mutable slice of all bits that have not been yielded yet.
	///
	/// # Original
	///
	/// [`IntoIter::as_mut_slice`](core::array::IntoIter::as_mut_slice)
	#[inline]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, V::Store> {
		unsafe {
			self.array
				.as_mut_bitslice()
				.get_unchecked_mut(self.alive.clone())
		}
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `as_mut_bitslice` to view the underlying slice"]
	pub fn as_mut_slice(&mut self) -> &mut BitSlice<O, V::Store> {
		self.as_mut_bitslice()
	}

	/// Extracts a bit from the array.
	#[inline]
	fn get(&self, index: usize) -> bool {
		unsafe {
			self.array
				.as_raw_slice()
				.pipe(BitPtr::<Const, O, V::Store>::from_slice)
				.add(index)
				.read()
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Debug for IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("IntoIter")
			.field(&self.as_bitslice())
			.finish()
	}
}

impl<O, V> Iterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.alive.next().map(|idx| self.get(idx))
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.alive.nth(n).map(|idx| self.get(idx))
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn count(self) -> usize {
		self.len()
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, V> DoubleEndedIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.alive.next_back().map(|idx| self.get(idx))
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.alive.nth_back(n).map(|idx| self.get(idx))
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> ExactSizeIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	#[inline(always)]
	fn len(&self) -> usize {
		self.alive.len()
	}
}

impl<O, V> FusedIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
}
