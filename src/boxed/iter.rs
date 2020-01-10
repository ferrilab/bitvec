//! Iteration processes for `BitBox`.

use crate::{
	boxed::BitBox,
	order::BitOrder,
	pointer::BitPtr,
	slice::{
		BitMut,
		BitSlice,
	},
	store::BitStore,
};

use core::iter::FusedIterator;

impl<O, T> IntoIterator for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Item = bool;
	type IntoIter = IntoIter<O, T>;

	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			region: self.bitptr(),
			bitbox: self,
		}
	}
}

impl<'a, O, T> IntoIterator for &'a BitBox<O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = <&'a BitSlice<O, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.as_bitslice().into_iter()
	}
}

impl<'a, O, T> IntoIterator for &'a mut BitBox<O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = BitMut<'a, O, T>;
	type IntoIter = <&'a mut BitSlice<O, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_bitslice().into_iter()
	}
}

/// State keeper for consuming iteration over a `BitBox`.
#[repr(C)]
pub struct IntoIter<O, T>
where O: BitOrder, T: BitStore {
	/// Owning pointer to the full slab
	bitbox: BitBox<O, T>,
	/// Slice descriptor for the region undergoing iteration.
	region: BitPtr<T>,
}

impl<O, T> IntoIter<O, T>
where O: BitOrder, T: BitStore {
	fn iterator(&self) -> <&BitSlice<O, T> as IntoIterator>::IntoIter {
		self.region.into_bitslice().into_iter()
	}
}

impl<O, T> Iterator for IntoIter<O, T>
where O: BitOrder, T: BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next().copied();
		self.region = slice_iter.bitptr();
		out
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iterator().size_hint()
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.nth(n).copied();
		self.region = slice_iter.bitptr();
		out
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T> DoubleEndedIterator for IntoIter<O, T>
where O: BitOrder, T: BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next_back().copied();
		self.region = slice_iter.bitptr();
		out
	}
}

impl<O, T> ExactSizeIterator for IntoIter<O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for IntoIter<O, T>
where O: BitOrder, T: BitStore {}
