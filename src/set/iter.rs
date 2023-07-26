#![doc = include_str!("../../doc/set/iter.md")]

use core::iter::{
	FromIterator,
	FusedIterator,
};

use super::BitSet;
use crate::{
	order::BitOrder,
	slice::{
		BitSlice,
		IterOnes,
	},
	store::BitStore,
};

impl<T, O> Extend<usize> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = usize> {
		iter.into_iter().for_each(|val| {
			self.insert(val);
		});
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, T, O> Extend<&'a usize> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = &'a usize> {
		self.extend(iter.into_iter().copied());
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> FromIterator<usize> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = usize> {
		let mut set = Self::new();
		set.extend(iter.into_iter());
		set
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, T, O> FromIterator<&'a usize> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = &'a usize> {
		iter.into_iter().copied().collect::<Self>()
	}
}

/*
impl<T, O> IntoIterator for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	type IntoIter = ???;
	type Item = usize;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.inner.into_boxed_bitslice().???()
	}
}
*/

#[cfg(not(tarpaulin_include))]
impl<'a, T, O> IntoIterator for &'a BitSet<T, O>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	type IntoIter = IterOnes<'a, T, O>;
	type Item = usize;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.iter()
	}
}

#[doc = include_str!("../../doc/set/iter/Range.md")]
pub struct Range<'a, T, O>
where
	T: BitStore,
	O: BitOrder,
{
	/// Inner [`IterOnes`] iterator.
	inner: IterOnes<'a, T, O>,
}
impl<'a, T, O> Range<'a, T, O>
where
	T: BitStore,
	O: BitOrder,
{
	pub(super) fn new(slice: &'a BitSlice<T, O>, offset: usize) -> Self {
		Self {
			inner: IterOnes::new(slice, offset),
		}
	}
}
impl<'a, T, O> Iterator for Range<'a, T, O>
where
	T: BitStore,
	O: BitOrder,
{
	type Item = usize;

	easy_iter!();

	#[inline]
	fn next(&mut self) -> Option<usize> {
		self.inner.next()
	}
}
impl<'a, T, O> DoubleEndedIterator for Range<'a, T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn next_back(&mut self) -> Option<usize> {
		self.inner.next_back()
	}
}
impl<T, O> ExactSizeIterator for Range<'_, T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn len(&self) -> usize {
		self.inner.len()
	}
}
impl<T, O> FusedIterator for Range<'_, T, O>
where
	T: BitStore,
	O: BitOrder,
{
}
