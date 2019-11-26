//! Iteration processes for `BitVec`.

use super::*;

use crate::{
	order::BitOrder,
	store::BitStore,
};

use alloc::vec::Vec;

use core::{
	iter::{
		FromIterator,
		FusedIterator,
	},
	ptr::NonNull,
};

/** Extends a `BitVec` with the contents of another bitstream.

At present, this just calls `.push()` in a loop. When specialization becomes
available, it will be able to more intelligently perform bulk moves from the
source into `self` when the source is `BitSlice`-compatible.
**/
impl<O, T> Extend<bool> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Extends a `BitVec` from another bitstream.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `src`: A source bitstream.
	///
	/// # Type Parameters
	///
	/// - `I: IntoIterator<Item=bool>`: The source bitstream with which to
	///   extend `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![Msb0, u8; 0; 4];
	/// bv.extend(bitvec![1; 4]);
	/// assert_eq!(0x0F, bv.as_slice()[0]);
	/// ```
	fn extend<I: IntoIterator<Item=bool>>(&mut self, src: I) {
		let iter = src.into_iter();
		match iter.size_hint() {
			(_, Some(hi)) => self.reserve(hi),
			(lo, None) => self.reserve(lo),
		}
		iter.for_each(|b| self.push(b));
	}
}

/// Permits the construction of a `BitVec` by using `.collect()` on an iterator
/// of `bool`.
impl<O, T> FromIterator<bool> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Collects an iterator of `bool` into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// use std::iter::repeat;
	/// let bv: BitVec<Msb0, u8> = repeat(true)
	///   .take(4)
	///   .chain(repeat(false).take(4))
	///   .collect();
	/// assert_eq!(bv.as_slice()[0], 0xF0);
	/// ```
	fn from_iter<I: IntoIterator<Item=bool>>(src: I) -> Self {
		let iter = src.into_iter();
		let mut bv = match iter.size_hint() {
			| (_, Some(len))
			| (len, _)
			=> Self::with_capacity(len),
		};
		for bit in iter {
			bv.push(bit);
		}
		bv
	}
}

/** Produces an iterator over all the bits in the vector.

This iterator follows the ordering in the vector type, and implements
`ExactSizeIterator`, since `BitVec`s always know exactly how large they are, and
`DoubleEndedIterator`, since they have known ends.
**/
impl<O, T> IntoIterator for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Item = bool;
	type IntoIter = IntoIter<O, T>;

	/// Iterates over the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 1, 1, 1, 1, 0, 0, 0, 0];
	/// let mut count = 0;
	/// for bit in bv {
	///   if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			region: self.pointer,
			bitvec: self,
		}
	}
}

impl<'a, O, T> IntoIterator for &'a BitVec<O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = <&'a BitSlice<O, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		<&'a BitSlice<O, T> as IntoIterator>::into_iter(self)
	}
}

/** State keeper for draining iteration.

# Type Parameters

- `O: BitOrder`: The ordering type of the underlying vector.
- `T: 'a + BitStore`: The storage type of the underlying vector.

# Lifetimes

- `'a`: The lifetime of the underlying vector.
**/
pub struct Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Pointer to the `BitVec` being drained.
	pub(super) bitvec: NonNull<BitVec<O, T>>,
	/// Current remaining range to remove.
	pub(super) iter: crate::slice::iter::Iter<'a, O, T>,
	/// Index of the original vector tail to preserve.
	pub(super) tail_start: usize,
	/// Length of the tail.
	pub(super) tail_len: usize,
}

impl<'a, O, T> Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Fills the drain span with another iterator.
	///
	/// If the stream exhausts before the drain is filled, then the tail
	/// elements move downwards; otherwise, the tail stays put and the drain is
	/// filled.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `stream`: The source of bits to fill into the drain.
	///
	/// # Returns
	///
	/// - `true` if the drain was filled before the `stream` exhausted.
	/// - `false` if the `stream` exhausted early, and the tail was moved down.
	///
	/// # Type Parameters
	///
	/// - `I: Iterator<Item=bool>`: A provider of bits.
	unsafe fn fill<I: Iterator<Item=bool>>(&mut self, stream: &mut I) -> bool {
		let bv = self.bitvec.as_mut();
		let drain_from = bv.len();
		let drain_upto = self.tail_start;

		for n in drain_from .. drain_upto {
			if let Some(bit) = stream.next() {
				bv.push(bit);
			}
			else {
				for (to, from) in (n .. n + self.tail_len).zip(drain_upto ..) {
					bv.swap(from, to);
				}
				self.tail_start = n;
				return false;
			}
		}
		true
	}

	/// Moves the tail span farther back in the vector.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The amount by which to move the tail span.
	unsafe fn move_tail(&mut self, by: usize) {
		let bv = self.bitvec.as_mut();
		bv.reserve(by);
		let new_tail = self.tail_start + by;
		let old_len = bv.len();
		let new_len = self.tail_start + self.tail_len + by;

		bv.set_len(new_len);
		for n in (0 .. self.tail_len).rev() {
			bv.swap(self.tail_start + n, new_tail + n);
		}
		bv.set_len(old_len);

		self.tail_start = new_tail;
	}
}

impl<'a, O, T> DoubleEndedIterator for Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back().copied()
	}
}

impl<'a, O, T> ExactSizeIterator for Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {}

impl<'a, O, T> FusedIterator for Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {}

impl<'a, O, T> Iterator for Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next().copied()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth(n).copied()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.iter.next_back().copied()
	}
}

impl<'a, O, T> Drop for Drain<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	fn drop(&mut self) { unsafe {
		let bv: &mut BitVec<O, T> = self.bitvec.as_mut();
		//  Get the start of the drained span.
		let start = bv.len();
		//  Get the start of the remnant span.
		let tail = self.tail_start;
		let tail_len = self.tail_len;
		//  Get the full length of the vector,
		let full_len = tail + tail_len;
		//  And the length of the vector after the drain.
		let end_len = start + tail_len;
		//  Inflate the vector to include the remnant span,
		bv.set_len(full_len);
		//  Swap the remnant span down into the drained span,
		for (from, to) in (tail .. full_len).zip(start .. end_len) {
			bv.swap(from, to);
		}
		//  And deflate the vector to fit.
		bv.set_len(end_len);
	} }
}

/// A consuming iterator for `BitVec`.
#[repr(C)]
pub struct IntoIter<O, T>
where O: BitOrder, T: BitStore {
	/// Owning descriptor for the allocation. This is not modified by iteration.
	pub(super) bitvec: BitVec<O, T>,
	/// Descriptor for the live portion of the vector as iteration proceeds.
	pub(super) region: BitPtr<T>,
}

impl<O, T> IntoIter<O, T>
where O: BitOrder, T: BitStore {
	fn iterator(&self) -> <&BitSlice<O, T> as IntoIterator>::IntoIter {
		self.region.into_bitslice().into_iter()
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

impl<O, T> Iterator for IntoIter<O, T>
where O: BitOrder, T: BitStore {
	type Item = bool;

	/// Advances the iterator by one, returning the first bit in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading bit in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![1, 0];
	/// let mut iter = bv.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next().copied();
		self.region = slice_iter.bitptr();
		out
	}

	/// Hints at the number of bits remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum bits remaining.
	/// - `Option<usize>`: The maximum bits remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1];
	/// let mut iter = bv.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iterator().size_hint()
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// You are probably looking to use this on a borrowed iterator rather than
	/// an owning iterator. See [`BitSlice`].
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of bits in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bv = bitvec![Msb0, u8; 0, 1, 0, 1, 0];
	/// assert_eq!(bv.into_iter().count(), 5);
	/// ```
	///
	/// [`BitSlice`]: ../struct.BitSlice.html#method.iter
	fn count(self) -> usize {
		self.bitvec.len()
	}

	/// Advances the iterator by `n` bits, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of bits to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// bits.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 1];
	/// let mut iter = bv.into_iter();
	/// assert_eq!(iter.len(), 4);
	/// assert!(iter.nth(3).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.nth(n).copied();
		self.region = slice_iter.bitptr();
		out
	}

	/// Consumes the iterator, returning only the last bit.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 1];
	/// assert!(bv.into_iter().last().unwrap());
	/// ```
	///
	/// Empty iterators return `None`
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// assert!(bitvec![].into_iter().last().is_none());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** A splicing iterator for `BitVec`.

This removes a segment from the vector and inserts another bitstream into its
spot. Any bits from the original `BitVec` after the removed segment are kept,
after the inserted bitstream.

Only the removed segment is available for iteration.

# Type Parameters

- `I: Iterator<Item=bool>`: Any bitstream. This will be used to fill the
  removed span.
**/
pub struct Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {
	pub(super) drain: Drain<'a, O, T>,
	pub(super) splice: I,
}

impl<'a, O, T, I> DoubleEndedIterator for Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, O, T, I> ExactSizeIterator for Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {}

impl<'a, O, T, I> FusedIterator for Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {}

//  Forward iteration to the interior drain
impl<'a, O, T, I> Iterator for Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		//  If the drain produced a bit, then try to pull a bit from the
		//  replacement. If the replacement produced a bit, push it into the
		//  `BitVec` that the drain is managing. This works because the `Drain`
		//  type truncates the `BitVec` to the front of the region being
		//  drained, then tracks the remainder of the memory.
		self.drain.next().map(|bit| {
			if let Some(new_bit) = self.splice.next() {
				unsafe { self.drain.bitvec.as_mut() }.push(new_bit);
			}
			bit
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	fn count(self) -> usize {
		self.drain.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth(n)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, O, T, I> Drop for Splice<'a, O, T, I>
where O: BitOrder, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn drop(&mut self) { unsafe {
		if self.drain.tail_len == 0 {
			self.drain.bitvec.as_mut().extend(self.splice.by_ref());
			return;
		}

		//  Fill the drained span from the splice. If this exhausts the splice,
		//  exit. Note that `Drain::fill` runs from the current `BitVec.len`
		//  value, so the fact that `Splice::next` attempts to push onto the
		//  vector is not a problem here.
		if !self.drain.fill(&mut self.splice) {
			return;
		}

		let (lower, _) = self.splice.size_hint();

		//  If the splice still has data, move the tail to make room for it and
		//  fill.
		if lower > 0 {
			self.drain.move_tail(lower);
			if !self.drain.fill(&mut self.splice) {
				return;
			}
		}

		let mut remnant = self.splice.by_ref().collect::<Vec<_>>().into_iter();
		if remnant.len() > 0 {
			self.drain.move_tail(remnant.len());
			self.drain.fill(&mut remnant);
		}
		//  Drain::drop does the rest
	} }
}
