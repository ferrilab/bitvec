/*! Adapters for fitting iterators of `bool` into `bitvec`.

This module provides an adapter struct that foreign `Iterator` implementations
must use in order to be eligible for bit-wise arithmetic with `bitvec` types.

Older versions of the crate implemented bit-wise arithmetic (the `&`, `|`, and
`^` operators, as well as their `&=`, `|=`, and `^=` variants) with a single
blanket implementation over all `Iterator<Item = bool>`. However, the common use
case for these operators was between `bitvec` data structures, not involving a
foreign `bool` source. The bit-by-bit crawl implementation was a performance
bottleneck, and so was replaced.

Rust’s type-algebra system is not powerful enough to permit both a generalized
blanket implementation over iterators as well as a specialized implementation
over known data structures. As such, the data structures replaced their blanket
implementations with specific implementations. Each data structure implements
the operators with itself, [`BitSlice`], and the [`BitIter`] wrapper provided
here. Implementations between bit-slices have the opportunity to specialize for
performance increases, and the `BitIter` implementation provides the old
bit-by-bit behavior, now safely routed through the single wrapper struct
`BitIter` rather than through a blanket trait implementation.

This module provides the [`BitIterExt`] trait, which is blanket-implemented on
all `IntoIterator<Item = bool>` types. It provides a method, [`for_bitvec`],
which wraps its receiver in `BitIter` so that it can be used in bit-wise
arithmetic. This trait is in the crate [prelude], and neither type in this
module needs to be directly named by users.

[prelude]: crate::prelude
[`BitIter`]: crate::iter::BitIter
[`BitIterExt`]: crate::iter::BitIterExt
[`BitSlice`]: crate::slice::BitSlice
[`for_bitvec`]: crate::iter::BitIterExt::for_bitvec
!*/

use core::iter::FusedIterator;

/** Allows any `bool`-producing iterator to be used in bitwise arithmetic.

This structure is a transparent wrapper over any `Iterator` or `IntoIterator`
type whose `Item` is `bool`. This type is necessary in order to allow `bitvec`
types to perform bitwise arithmetic with arbitrary bit-streams, while still
allowing specialization so that they can use fast paths where available.

Adapt any `bool`-producing iterator for use in `bitvec` arithmetic with the
[`for_bitvec`] adapter method, which is provided by a blanket implementation
through the [`BitIterExt`] trait.

See the [module documentation][crate::iter] for more information.

[`BitIterExt`]: crate::iter::BitIterExt
[`for_bitvec`]: crate::iter::BitIterExt::for_bitvec
**/
#[repr(transparent)]
pub struct BitIter<I>
where I: Iterator<Item = bool>
{
	/// The wrapped iterator.
	inner: I,
}

impl<I> BitIter<I>
where I: Iterator<Item = bool>
{
	/// Wraps a `bool`-producing iterator so that `bitvec` can use it.
	pub fn new<I2>(src: I2) -> Self
	where I2: IntoIterator<Item = bool, IntoIter = I> {
		Self {
			inner: src.into_iter(),
		}
	}
}

impl<I> Iterator for BitIter<I>
where I: Iterator<Item = bool>
{
	type Item = bool;

	#[inline(always)]
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}

	#[inline(always)]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.inner.nth(n)
	}

	#[inline(always)]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}

	#[inline(always)]
	fn count(self) -> usize {
		self.inner.count()
	}

	#[inline(always)]
	fn last(self) -> Option<Self::Item> {
		self.inner.last()
	}
}

impl<I> DoubleEndedIterator for BitIter<I>
where I: Iterator<Item = bool> + DoubleEndedIterator
{
	#[inline(always)]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.next_back()
	}

	#[inline(always)]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.inner.nth_back(n)
	}
}

impl<I> ExactSizeIterator for BitIter<I>
where I: Iterator<Item = bool> + ExactSizeIterator
{
	#[inline(always)]
	fn len(&self) -> usize {
		self.inner.len()
	}
}

impl<I> FusedIterator for BitIter<I> where I: Iterator<Item = bool> + FusedIterator
{
}

/** Extends all `bool`-producing iterators to have a `BitIter` adapter method.

See the [module documentation][crate::iter].
**/
pub trait BitIterExt: IntoIterator<Item = bool> + Sized {
	/// Wraps the iterator as a `BitIter` for use in `bitvec` operations.
	#[inline(always)]
	fn for_bitvec(self) -> BitIter<Self::IntoIter> {
		BitIter::new(self)
	}
}

impl<I> BitIterExt for I where I: IntoIterator<Item = bool>
{
}
