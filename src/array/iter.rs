//! Array iteration.

use crate::{
	array::BitArray,
	order::BitOrder,
	slice::BitSlice,
	view::BitView,
};

use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::FusedIterator,
	ops::Range,
};

/** A by-value [array] iterator.

# Original

[`array::IntoIter`](core::array::IntoIter)

# API Differences

The standard-library iterator is still unstable, as it depends on
const-generics. The [`BitView`] trait provides a rough simulacrum of
const-generic arrays until this feature stabilizes for use outside the standard
libraries.

[array]: crate::array::BitArray
[`BitView`]: crate::view::BitView
**/
#[derive(Clone)]
pub struct IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	/// The array being iterated.
	array: BitArray<O, V>,

	/// The bits in `array` that have not yet been yielded.
	///
	/// Invariants:
	/// - `alive.start <= alive.end`
	/// - `alive.end <= V::const_bits()`
	alive: Range<usize>,
}

impl<O, V> IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	/// Creates a new iterator over the given `array`.
	///
	/// # Original
	///
	/// [`IntoIter::new`](core::array::IntoIter::new)
	pub(crate) fn new(array: BitArray<O, V>) -> Self {
		Self {
			array,
			alive: 0 .. V::const_bits(),
		}
	}

	/// Returns an immutable slice of all bits that have not been yielded yet.
	///
	/// # Original
	///
	/// [`IntoIter::as_slice`](core::array::IntoIter::as_slice)
	pub fn as_bitslice(&self) -> &BitSlice<O, V::Mem> {
		unsafe { self.array.as_bitslice().get_unchecked(self.alive.clone()) }
	}

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `.as_bitslice()` to view the underlying slice"]
	pub fn as_slice(&self) -> &BitSlice<O, V::Mem> {
		self.as_bitslice()
	}

	/// Returns a mutable slice of all bits that have not been yielded yet.
	///
	/// # Original
	///
	/// [`IntoIter::as_mut_slice`](core::array::IntoIter::as_mut_slice)
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, V::Mem> {
		unsafe {
			self.array
				.as_mut_bitslice()
				.get_unchecked_mut(self.alive.clone())
		}
	}

	#[doc(hidden)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `.as_mut_bitslice()` to view the underlying slice"]
	pub fn as_mut_slice(&mut self) -> &BitSlice<O, V::Mem> {
		self.as_mut_bitslice()
	}

	/// Extracts a bit from the array.
	fn get(&self, index: usize) -> bool {
		*unsafe { self.array.as_bitslice().get_unchecked(index) }
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Debug for IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("IntoIter")
			.field(&self.as_bitslice())
			.finish()
	}
}

impl<O, V> Iterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.alive.next().map(|idx| self.get(idx))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.alive.nth(n).map(|idx| self.get(idx))
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, V> DoubleEndedIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		self.alive.next_back().map(|idx| self.get(idx))
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.alive.nth_back(n).map(|idx| self.get(idx))
	}
}

impl<O, V> ExactSizeIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
	fn len(&self) -> usize {
		self.alive.len()
	}
}

impl<O, V> FusedIterator for IntoIter<O, V>
where
	O: BitOrder,
	V: BitView,
{
}
