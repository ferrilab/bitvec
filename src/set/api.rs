//! Port of the `BTreeSet<usize>` inherent API.

use core::ops::{self,};

use super::{
	BitSet,
	Range,
};
use crate::{
	order::BitOrder,
	slice::IterOnes,
	store::BitStore,
	vec::BitVec,
};

/// Port of the `BTreeSet<T>` inherent API.
impl<T, O> BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	/// Constructs a new, empty, bit-set.
	///
	/// Does not allocate anything on its own.
	///
	/// ## Original
	///
	/// [`BTreeSet::new`](alloc::collections::BTreeSet::new)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let bs = BitSet::<u8, Msb0>::new();
	/// assert!(bs.is_empty());
	/// ```
	#[inline]
	pub fn new() -> Self {
		Self::EMPTY
	}

	/// Constructs a double-ended iterator over a sub-range of elements in the
	/// set.
	///
	/// ## Panics
	///
	/// Panics if range `start > end`.
	///
	/// ## Original
	///
	/// [`BTreeSet::range`](alloc::collections::BTreeSet::range)
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the API has been restricted to
	/// only accept standard ranges (like `1..10`) instead of all possible range
	/// types.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(3);
	/// set.insert(5);
	/// set.insert(8);
	/// for elem in set.range(4..9) {
	///     println!("{elem}");
	/// }
	/// assert_eq!(Some(5), set.range(4..9).next());
	/// ```
	#[inline]
	pub fn range(&self, range: ops::Range<usize>) -> Range<'_, T, O> {
		let start = range.start;
		let end = range.end;
		assert!(
			start <= end,
			"range start ({}) less than range end ({})",
			start,
			end
		);
		Range::new(
			if end < self.inner.len() {
				&self.inner[start .. end]
			}
			else {
				&self.inner[start ..]
			},
			start,
		)
	}

	/*
	/// Visits the elements representing the difference, i.e.,
	/// the elements that are in `self` but not in `other`,
	/// in ascending order.
	///
	/// ## Original
	///
	/// [`BTreeSet::difference`](alloc::collections::BTreeSet::difference)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	///
	/// let mut b: BitSet = BitSet::new();
	/// b.insert(2);
	/// b.insert(3);
	///
	/// let diff: Vec<_> = a.difference(&b).cloned().collect();
	/// assert_eq!(diff, [1]);
	/// ```
	#[inline]
	pub fn difference<'a>(&'a self, other: &'a BitSet<T, O>) -> Difference<'_, T, O> {
		todo!()
	}

	/// Visits the elements representing the symmetric difference,
	/// i.e., the elements that are in `self` or in other but not in both, in ascending order.
	///
	/// ## Original
	///
	/// [`BTreeSet::symmetric_difference`](alloc::collections::BTreeSet::symmetric_difference)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	///
	/// let mut b: BitSet = BitSet::new();
	/// b.insert(2);
	/// b.insert(3);
	///
	/// let diff: Vec<_> = a.symmetric_difference(&b).cloned().collect();
	/// assert_eq!(diff, [1, 3]);
	/// ```
	#[inline]
	pub fn symmetric_difference<'a>(&'a self, other: &'a BitSet<T, O>) -> SymmetricDifference<'_, T, O> {
		todo!()
	}

	/// Visits the elements representing the intersection,
	/// i.e., the elements that are in both `self` and `other`, in ascending order.
	///
	/// ## Original
	///
	/// [`BTreeSet::intersection`](alloc::collections::BTreeSet::intersection)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	///
	/// let mut b: BitSet = BitSet::new();
	/// b.insert(2);
	/// b.insert(3);
	///
	/// let diff: Vec<_> = a.intersection(&b).cloned().collect();
	/// assert_eq!(diff, [2]);
	/// ```
	#[inline]
	pub fn intersection<'a>(&'a self, other: &'a BitSet<T, O>) -> Intersection<'_, T, O> {
		todo!()
	}

	/// Visits the elements representing the union,
	/// i.e., all the elements in both `self` or `other`, without duplicates, in ascending order.
	///
	/// ## Original
	///
	/// [`BTreeSet::union`](alloc::collections::BTreeSet::union)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	///
	/// let mut b: BitSet = BitSet::new();
	/// b.insert(2);
	/// b.insert(3);
	///
	/// let diff: Vec<_> = a.union(&b).cloned().collect();
	/// assert_eq!(diff, [1, 2, 3]);
	/// ```
	#[inline]
	pub fn union<'a>(&'a self, other: &'a BitSet<T, O>) -> Union<'_, T, O> {
		todo!()
	}
	*/

	/// Clears the set, removing all elements.
	///
	/// ## Original
	///
	/// [`BTreeSet::clear`](alloc::collections::BTreeSet::clear)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(1);
	/// set.clear();
	/// assert!(set.is_empty());
	/// ```
	#[inline]
	pub fn clear(&mut self) {
		self.inner.clear()
	}

	/// Returns `true` if the set contains the given element.
	///
	/// ## Original
	///
	/// [`BTreeSet::contains`](alloc::collections::BTreeSet::contains)
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the argument has been adjusted
	/// to accept a `usize` value instead of a reference to be easier to use.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(1);
	/// set.insert(2);
	/// set.insert(3);
	/// assert!(set.contains(1));
	/// assert!(!set.contains(4));
	/// ```
	#[inline]
	pub fn contains(&self, value: usize) -> bool {
		if value >= self.inner.len() {
			false
		}
		else {
			self.inner[value]
		}
	}

	/*
	/// Returns `true` if `self` has no elements in common with `other`.
	/// This is equivalent to checking for an empty intersection.
	///
	/// ## Original
	///
	/// [`BTreeSet::is_disjoint`](alloc::collections::BTreeSet::is_disjoint)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	/// a.insert(3);
	///
	/// let mut b: BitSet = BitSet::new();
	/// assert!(a.is_disjoint(&b));
	/// b.insert(4);
	/// assert!(a.is_disjoint(&b));
	/// b.insert(1);
	/// assert!(!a.is_disjoint(&b));
	/// ```
	#[inline]
	pub fn is_disjoint(&self, other: &BitSet<T, O>) -> bool {
		self.intersection(other).next().is_none()
	}

	/// Returns `true` if the set is a subset of another, i.e.,
	/// `other` contains at least all the elements in `self`.
	///
	/// ## Original
	///
	/// [`BTreeSet::is_subset`](alloc::collections::BTreeSet::is_subset)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut sup: BitSet = BitSet::new();
	/// sup.insert(1);
	/// sup.insert(2);
	/// sup.insert(3);
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert!(set.is_subset(&sup));
	/// set.insert(2);
	/// assert!(set.is_subset(&sup));
	/// set.insert(4);
	/// assert!(!set.is_subset(&sup));
	/// ```
	#[inline]
	pub fn is_subset(&self, other: &BitSet<T, O>) -> bool {
		todo!()
	}

	/// Returns `true` if the set is a superset of another, i.e.,
	/// `self` contains at least all the elements in `other`.
	///
	/// ## Original
	///
	/// [`BTreeSet::is_superset`](alloc::collections::BTreeSet::is_superset)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut sub: BitSet = BitSet::new();
	/// sub.insert(1);
	/// sub.insert(2);
	/// sub.insert(3);
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert!(!set.is_superset(&sub));
	/// set.insert(0);
	/// set.insert(1);
	/// assert!(!set.is_superset(&sub));
	/// set.insert(2);
	/// assert!(set.is_superset(&sub));
	/// ```
	#[inline]
	pub fn is_superset(&self, other: &BitSet<T, O>) -> bool {
		todo!()
	}
	*/

	/// Returns the first element in the set, if any.
	/// This element is always the minimum of all elements in the set.
	///
	/// ## Original
	///
	/// [`BTreeSet::first`](alloc::collections::BTreeSet::first)
	///
	/// ## API Differences
	///
	/// Since bit-sets store their elements as bits instead of values, the
	/// element is returned by-value instead.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert_eq!(set.first(), None);
	/// set.insert(1);
	/// assert_eq!(set.first(), Some(1));
	/// set.insert(2);
	/// assert_eq!(set.first(), Some(1));
	/// ```
	#[inline]
	pub fn first(&self) -> Option<usize> {
		self.inner.first_one()
	}

	/// Returns the last element in the set, if any.
	/// This element is always the maximum of all elements in the set.
	///
	/// ## Original
	///
	/// [`BTreeSet::last`](alloc::collections::BTreeSet::last)
	///
	/// ## API Differences
	///
	/// Since bit-sets store their elements as bits instead of values, the
	/// element is returned by-value instead.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert_eq!(set.last(), None);
	/// set.insert(1);
	/// assert_eq!(set.last(), Some(1));
	/// set.insert(2);
	/// assert_eq!(set.last(), Some(2));
	/// ```
	#[inline]
	pub fn last(&self) -> Option<usize> {
		self.inner.last_one()
	}

	/// Removes the first element from the set and returns it, if any.
	/// The first element is always the minimum element in the set.
	///
	/// ## Original
	///
	/// [`BTreeSet::pop_first`](alloc::collections::BTreeSet::pop_first)
	///
	/// ## API Differences
	///
	/// Since bit-sets store their elements as bits instead of values, the
	/// element is returned by-value instead.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(1);
	/// while let Some(n) = set.pop_first() {
	///     assert_eq!(n, 1);
	/// }
	/// assert!(set.is_empty());
	/// ```
	#[inline]
	pub fn pop_first(&mut self) -> Option<usize> {
		let first = self.first()?;
		self.remove(first);
		Some(first)
	}

	/// Removes the last element from the set and returns it, if any.
	/// The last element is always the maximum element in the set.
	///
	/// ## Original
	///
	/// [`BTreeSet::pop_last`](alloc::collections::BTreeSet::pop_last)
	///
	/// ## API Differences
	///
	/// Since bit-sets store their elements as bits instead of values, the
	/// element is returned by-value instead.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(1);
	/// while let Some(n) = set.pop_last() {
	///     assert_eq!(n, 1);
	/// }
	/// assert!(set.is_empty());
	/// ```
	#[inline]
	pub fn pop_last(&mut self) -> Option<usize> {
		let last = self.last()?;
		self.remove(last);
		Some(last)
	}

	/// Adds a value to the set.
	///
	/// Returns whether the value was newly inserted. That is:
	///
	/// * If the set did not previously contain the value, `true` is returned.
	/// * If the set already contained the value, `false` is returned.
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the argument has been adjusted
	/// to accept a `usize` value instead of a reference to be easier to use.
	///
	/// ## Original
	///
	/// [`BTreeSet::insert`](alloc::collections::BTreeSet::insert)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	///
	/// assert!(set.insert(2));
	/// assert!(!set.insert(2));
	/// assert_eq!(set.len(), 1);
	/// ```
	#[inline]
	pub fn insert(&mut self, value: usize) -> bool {
		let old_len = self.inner.len();
		if value >= old_len {
			self.inner.resize(value + 1, false);
			self.inner.set(value, true);
			true
		}
		else {
			!self.inner.replace(value, true)
		}
	}

	/// If the set contains the value, removes it from the set.
	/// Returns whether such an element was present.
	///
	/// ## Original
	///
	/// [`BTreeSet::remove`](alloc::collections::BTreeSet::remove)
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the argument has been adjusted
	/// to accept a `usize` value instead of a reference to be easier to use.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	///
	/// set.insert(2);
	/// assert!(set.remove(2));
	/// assert!(!set.remove(2));
	/// ```
	#[inline]
	pub fn remove(&mut self, value: usize) -> bool {
		let old_len = self.inner.len();
		if value >= old_len {
			false
		}
		else {
			let ret = self.inner.replace(value, false);

			// NOTE: it's unclear how this affects performance and if we should
			// do this automatically, or require it manually only
			self.shrink_inner();

			ret
		}
	}

	/// Retains only the elements specified by the predicate.
	///
	/// In other words, remove all elements `e` for which `f(e)` returns
	/// `false`. The elements are visited in ascending order.
	///
	/// ## Original
	///
	/// [`BTreeSet::retain`](alloc::collections::BTreeSet::retain)
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the function argument has been
	/// adjusted to accept `usize` values instead of references to be easier to
	/// use.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(1);
	/// set.insert(2);
	/// set.insert(3);
	/// set.insert(4);
	/// set.insert(5);
	/// set.insert(6);
	/// // Keep only the even numbers.
	/// set.retain(|k| k % 2 == 0);
	/// assert!(set.iter().eq([2, 4, 6].into_iter()));
	/// ```
	#[inline]
	pub fn retain<F>(&mut self, mut f: F)
	where F: FnMut(usize) -> bool {
		self.inner
			.iter_mut()
			.enumerate()
			.for_each(|(idx, mut bit)| {
				if *bit && !f(idx) {
					bit.set(false);
				}
			});
	}

	/// Moves all elements from `other` into `self`, leaving `other` empty.
	///
	/// ## Original
	///
	/// [`BTreeSet::append`](alloc::collections::BTreeSet::append)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	/// a.insert(3);
	///
	/// let mut b: BitSet = BitSet::new();
	/// b.insert(3);
	/// b.insert(4);
	/// b.insert(5);
	///
	/// a.append(&mut b);
	///
	/// assert_eq!(a.len(), 5);
	/// assert_eq!(b.len(), 0);
	///
	/// assert!(a.contains(1));
	/// assert!(a.contains(2));
	/// assert!(a.contains(3));
	/// assert!(a.contains(4));
	/// assert!(a.contains(5));
	/// ```
	#[inline]
	pub fn append(&mut self, other: &mut BitSet<T, O>) {
		other.shrink_inner();
		let and_len = Ord::min(self.inner.len(), other.inner.len());
		self.inner[.. and_len] |= &other.inner[.. and_len];
		self.inner.extend_from_bitslice(&other.inner[and_len ..]);
		other.inner.clear();
	}

	/// Splits the collection into two at the value.
	/// Returns a new collection with all elements greater than or equal to the
	/// value.
	///
	/// ## Original
	///
	/// [`BTreeSet::split_off`](alloc::collections::BTreeSet::split_off)
	///
	/// ## API Differences
	///
	/// Since bit-sets can only contain `usize`, the argument has been adjusted
	/// to accept a `usize` value instead of a reference to be easier to use.
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut a: BitSet = BitSet::new();
	/// a.insert(1);
	/// a.insert(2);
	/// a.insert(3);
	/// a.insert(17);
	/// a.insert(41);
	///
	/// let mut b = a.split_off(3);
	///
	/// assert_eq!(a.len(), 2);
	/// assert_eq!(b.len(), 3);
	///
	/// assert!(a.contains(1));
	/// assert!(a.contains(2));
	/// assert!(b.contains(3));
	/// assert!(b.contains(17));
	/// assert!(b.contains(41));
	/// ```
	#[inline]
	pub fn split_off(&mut self, value: usize) -> BitSet<T, O> {
		let len = self.inner.len();
		if value > len {
			self.shrink_inner();
			return BitSet::new();
		}

		let mut other = <BitVec<T, O>>::with_capacity(len);
		unsafe {
			other.set_len(len);
			other[.. value].fill(false);
			other[value ..].copy_from_bitslice(&self.inner[value ..]);
		}
		self.inner.truncate(value);
		self.shrink_inner();
		BitSet { inner: other }
	}

	/// Gets an iterator that visits the elements in the bit-set in ascending
	/// order.
	///
	/// ## Original
	///
	/// [`BTreeSet::iter`](alloc::collections::BTreeSet::iter)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// set.insert(3);
	/// set.insert(1);
	/// set.insert(2);
	///
	/// let mut set_iter = set.iter();
	/// assert_eq!(set_iter.next(), Some(1));
	/// assert_eq!(set_iter.next(), Some(2));
	/// assert_eq!(set_iter.next(), Some(3));
	/// assert_eq!(set_iter.next(), None);
	/// ```
	#[inline]
	pub fn iter(&self) -> IterOnes<'_, T, O> {
		self.inner.iter_ones()
	}

	/// Returns the number of elements in the set.
	///
	/// ## Original
	///
	/// [`BTreeSet::len`](alloc::collections::BTreeSet::len)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert_eq!(set.len(), 0);
	/// set.insert(1);
	/// assert_eq!(set.len(), 1);
	/// ```
	#[inline]
	pub fn len(&self) -> usize {
		self.inner.count_ones()
	}

	/// Returns `true` if the set contains no elements.
	///
	/// ## Original
	///
	/// [`BTreeSet::is_empty`](alloc::collections::BTreeSet::is_empty)
	///
	/// ## Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::set::BitSet;
	///
	/// let mut set: BitSet = BitSet::new();
	/// assert!(set.is_empty());
	/// set.insert(1);
	/// assert!(!set.is_empty());
	/// ```
	#[inline]
	pub fn is_empty(&self) -> bool {
		self.inner.not_any()
	}
}
