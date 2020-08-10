//! `BitVec` iterators

use crate::{
	devel as dvl,
	order::BitOrder,
	slice::{
		BitSlice,
		Iter,
	},
	store::BitStore,
	vec::BitVec,
};

use core::{
	iter::{
		FromIterator,
		FusedIterator,
	},
	ops::{
		Range,
		RangeBounds,
	},
	ptr::NonNull,
	slice,
};

use wyz::{
	pipe::Pipe,
	tap::TapOption,
};

impl<O, T> Extend<bool> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = bool> {
		let mut iter = iter.into_iter();
		match iter.size_hint() {
			(n, None) | (_, Some(n)) => {
				// This body exists to try to accelerate
				self.reserve(n);
				let len = self.len();
				let new_len = len + n;
				let new = unsafe {
					self.set_len(new_len);
					self.get_unchecked_mut(len .. new_len)
				};
				let mut pulled = 0;
				for (slot, bit) in new.iter_mut().zip(iter.by_ref()) {
					slot.set(bit);
					pulled += 1;
				}
				unsafe {
					self.set_len(len + pulled);
				}
			},
		}
		iter.for_each(|bit| self.push(bit));
	}
}

impl<'a, O, T> Extend<&'a bool> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = &'a bool> {
		self.extend(iter.into_iter().copied());
	}
}

impl<O, T> FromIterator<bool> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = bool> {
		let iter = iter.into_iter();
		let mut out = match iter.size_hint() {
			(n, None) | (_, Some(n)) => Self::with_capacity(n),
		};
		out.extend(iter);
		out
	}
}

impl<'a, O, T> FromIterator<&'a bool> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = &'a bool> {
		iter.into_iter().copied().pipe(Self::from_iter)
	}
}

impl<O, T> IntoIterator for BitVec<O, T>
where
	O: 'static + BitOrder,
	T: 'static + BitStore,
{
	type IntoIter = IntoIter<O, T>;
	type Item = bool;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			iter: self.as_bitslice().bitptr().to_bitslice_ref().iter(),
			_bv: self,
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> IntoIterator for &'a BitVec<O, T>
where
	O: 'a + BitOrder,
	T: 'a + BitStore,
{
	type IntoIter = <&'a BitSlice<O, T> as IntoIterator>::IntoIter;
	type Item = <&'a BitSlice<O, T> as IntoIterator>::Item;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.as_bitslice().into_iter()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> IntoIterator for &'a mut BitVec<O, T>
where
	O: 'a + BitOrder,
	T: 'a + BitStore,
{
	type IntoIter = <&'a mut BitSlice<O, T> as IntoIterator>::IntoIter;
	type Item = <&'a mut BitSlice<O, T> as IntoIterator>::Item;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_bitslice().into_iter()
	}
}

/** An iterator that moves out of a vector.

This `struct` is created by the `into_iter` method on [`BitVec`] (provided by
the [`IntoIterator`] trait).

# Original

[`vec::IntoIter`](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html)

# API Differences

This explicitly requires that `O` and `T` type parameters are `'static`, which
is not a bound present in the original. However, it is always *true*, so it will
not cause a compilation error.

[`BitVec`]: struct.BitVec.html
[`IntoIterator`]: https://doc.rust-lang.org/core/iter/trait.IntoIterator.html
**/
#[derive(Clone, Debug)]
pub struct IntoIter<O, T>
where
	O: 'static + BitOrder,
	T: 'static + BitStore,
{
	/// Take ownership of the vector for destruction.
	_bv: BitVec<O, T>,
	/// Use `BitSlice` iteration processes. This requires a `'static` lifetime,
	/// since it cannot borrow from itself.
	iter: Iter<'static, O, T>,
}

impl<O, T> IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Returns the remaining bits of this iterator as a bitslice.
	///
	/// # Original
	///
	/// [`vec::IntoIter::as_slice`](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html#method.as_slice)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 0, 1];
	/// let mut into_iter = bv.into_iter();
	/// assert_eq!(into_iter.as_bitslice(), bits![0, 1, 0, 1]);
	/// let _ = into_iter.next().unwrap();
	/// assert_eq!(into_iter.as_bitslice(), bits![1, 0, 1]);
	/// ```
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn as_bitslice(&self) -> &BitSlice<O, T> {
		self.iter.as_bitslice()
	}

	/// Returns the remaining elements of this iterator as a slice.
	///
	/// # Original
	///
	/// [`vec::IntoIter::as_slice`](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html#method.as_slice)
	///
	/// # Notes
	///
	/// You almost certainly want [`.as_bitslice()`].
	///
	/// [`.as_bitslice()`]: #method.as_bitslice
	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn as_slice(&self) -> &[T] {
		let bitptr = self.as_bitslice().bitptr();
		unsafe {
			slice::from_raw_parts(bitptr.pointer().to_const(), bitptr.elements())
		}
	}

	/// Returns the remaining bits of this iterator as a mutable slice.
	///
	/// # Original
	///
	/// [`vec::IntoIter::as_mut_slice`](https://doc.rust-lang.org/alloc/vec/struct.IntoIter.html#method.as_mut_slice)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 0, 1];
	/// let mut into_iter = bv.into_iter();
	/// assert_eq!(into_iter.as_bitslice(), bits![0, 1, 0, 1]);
	/// into_iter.as_mut_bitslice().set(2, true);
	/// assert!(!into_iter.next().unwrap());
	/// assert!(into_iter.next().unwrap());
	/// assert!(into_iter.next().unwrap());
	/// ```
	#[inline]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, T> {
		self.iter.as_bitslice().bitptr().to_bitslice_mut()
	}

	#[inline]
	#[doc(hidden)]
	#[deprecated(
		note = "Use `.as_mut_bitslice` on iterators to view the remaining data"
	)]
	#[cfg(not(tarpaulin_include))]
	pub fn as_mut_slice(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
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
		self.iter.next().copied()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth(n).copied()
	}

	#[inline]
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
		self.iter.next_back().copied()
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth_back(n).copied()
	}
}

impl<O, T> ExactSizeIterator for IntoIter<O, T>
where
	O: BitOrder,
	T: BitStore,
{
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

/** A draining iterator for `BitVec<O, T>`.

This `struct` is created by the [`drain`] method on [`BitVec`].

# Original

[`vec::Drain`](https://doc.rust-lang.org/alloc/vec/struct.Drain.html)

[`BitVec`]: struct.BitVec.html
[`drain`]: struct.BitVec.html#method.drain
**/
#[derive(Debug)]
pub struct Drain<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Exclusive reference to the vector this drains.
	source: NonNull<BitVec<O, T>>,
	/// The range of the source vector’s buffer being drained.
	drain: Iter<'a, O, T>,
	/// The range of the source vector’s preserved tail. This runs from the back
	/// edge of the drained region to the vector’s original length.
	tail: Range<usize>,
}

impl<'a, O, T> Drain<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	pub(super) fn new<R>(source: &'a mut BitVec<O, T>, range: R) -> Self
	where R: RangeBounds<usize> {
		let len = source.len();
		let drain = dvl::normalize_range(range, len);
		dvl::assert_range(drain.clone(), len);

		let tail = drain.end .. len;
		let drain = unsafe {
			//  Truncate the source vector to the beginning of the drain.
			source.set_len(drain.start);
			source
				.as_bitslice()
				.get_unchecked(drain)
				//  Remove the lifetime and borrow information
				.bitptr()
				.to_bitslice_ref().iter()
		};
		Self {
			source: source.into(),
			drain,
			tail,
		}
	}

	#[inline]
	fn tail_len(&self) -> usize {
		self.tail.end - self.tail.start
	}

	/// Attempts to overwrite the drained region with another iterator.
	///
	/// # Type Parameters
	///
	/// - `I`: Some source of `bool`s
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `stream`: A source of `bools` with which to overwrite the drained
	///   span.
	///
	/// # Returns
	///
	/// - `true` if the drained span was completely overwritten by `stream`.
	/// - `false` if the `stream` exhausted early.
	///
	/// # Effects
	///
	/// If the drained region is completely filled by the replacement `stream`,
	/// then the source vector is restored to its original length, and this
	/// `Drain` has no further work.
	///
	/// If the `stream` exhausts before completely filling the drained region,
	/// then the source vector is extended only to include the portion of the
	/// drain that was replaced. The tail section is not restored to the vector
	/// until the destructor runs.
	fn fill<I>(&mut self, stream: &mut I) -> bool
	where I: Iterator<Item = bool> {
		let tail_len = self.tail_len();
		let bv = unsafe { self.source.as_mut() };

		//  The entire span between `bv.len()` and `tail.start` is considered
		//  dead, and should be filled by `stream`.
		for idx in bv.len() .. self.tail.start {
			if let Some(bit) = stream.next() {
				unsafe {
					bv.set_unchecked(idx, bit);
				}
			}
			//  When the stream exhausts, extend the front region to the loop
			//  counter and exit. The destructor will finish relocation.
			else {
				unsafe {
					bv.set_len(idx + tail_len);
				}
				return false;
			}
		}
		//  If the drain region is completely filled, then the vector’s length
		//  reaches the end of the tail.
		unsafe {
			bv.set_len(self.tail.end);
		}
		//  Prevent the destructor from running by erasing the tail.
		self.tail = 0 .. 0;
		true
	}

	/// Resizes the middle drain segment to a new width.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `width`: The width, in bits, between the back edge of the head segment
	///   and the front edge of the tail segment.
	///
	/// # Effects
	///
	/// This is permitted to reällocate the buffer in order to grow capacity.
	/// After completion, the tail segment will be relocated to begin `width`
	/// bits after the head segment ends. The drain iteration cursor will *not*
	/// be modified.
	fn resize_drain(&mut self, width: usize) {
		let tail_len = self.tail_len();
		let bv = unsafe { self.source.as_mut() };
		let base_len = bv.len();
		let new_tail = base_len + width;
		let new_end = new_tail + tail_len;
		//  Ensure capacity for the drain and tail segments.
		bv.reserve(new_end - base_len);
		unsafe {
			bv.copy_within_unchecked(self.tail.clone(), new_tail);
		}
		self.tail = new_tail .. new_end;
	}
}

impl<O, T> Iterator for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.drain.next().copied()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth(n).copied()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T> DoubleEndedIterator for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back().copied()
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth_back(n).copied()
	}
}

impl<O, T> ExactSizeIterator for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn len(&self) -> usize {
		self.drain.len()
	}
}

impl<O, T> FusedIterator for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

impl<O, T> Drop for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn drop(&mut self) {
		match self.tail_len() {
			//  If there is no tail segment, there is no finalization work.
			0 => {},
			n => unsafe {
				let bv = self.source.as_mut();
				let start = bv.len();
				let new_len = start + n;
				//  Copy the tail span down to the start of the drained region.
				bv.copy_within_unchecked(self.tail.clone(), start);
				bv.set_len(new_len);
			},
		}
	}
}

/** A splicing iterator for `BitVec`.

This struct is created by the [`splice()`] method on [`BitVec`]. See its
documentation for more.

# Original

[`vec::Splice`](https://doc.rust-lang.org/alloc/vec/struct.Splice.html)

[`BitVec`]: struct.BitVec.html
[`splice()`]: struct.BitVec.html#method.splice
**/
#[derive(Debug)]
pub struct Splice<'a, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	/// Drain controller for the region of the vector being spliced.
	drain: Drain<'a, O, T>,
	/// Source of bits written into the drain.
	splice: I,
}

impl<'a, O, T, I> Splice<'a, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	pub(super) fn new<II>(drain: Drain<'a, O, T>, splice: II) -> Self
	where II: IntoIterator<IntoIter = I, Item = bool> {
		Self {
			drain,
			splice: splice.into_iter(),
		}
	}
}

impl<O, T, I> Iterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.drain.next().tap_some(|_| {
			/* Attempt to write a bit into the now-vacated slot at the front of
			the `Drain`. If the `splice` stream produced a bit, then it is
			written into the end of the `Drain`’s vector handle. This works
			because `Drain` always truncates its handle to the front edge of the
			drain region, so `bv.len()` is always the first bit of the `Drain`
			if the `Drain` is willing to yield.
			*/
			self.splice.next().tap_some(|new| {
				unsafe {
					let bv = self.drain.source.as_mut();
					let len = bv.len();
					//  It is always sound to write directly into the front of a
					//  `Drain`.
					/* TODO(myrrlyn): Extend `Iter` to have a `.next_slot`
					function which permits an `xchg` behavior, to avoid
					computing the pointer individually for read and write.
					*/
					bv.set_unchecked(len, *new);
					bv.set_len(len + 1);
				}
			})
		})
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	#[inline]
	fn count(self) -> usize {
		self.drain.len()
	}
}

//  Take from the back of the drain, without attempting to fill from the splice.
//  This makes dead regions that are cleaned up on drop.
impl<O, T, I> DoubleEndedIterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth_back(n)
	}
}

impl<O, T, I> ExactSizeIterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	#[inline]
	fn len(&self) -> usize {
		self.drain.len()
	}
}

impl<O, T, I> FusedIterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
}

impl<O, T, I> Drop for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	fn drop(&mut self) {
		//  If the drain has no tail segment, copy the splice into the vector.
		if self.drain.tail_len() == 0 {
			unsafe { self.drain.source.as_mut() }.extend(self.splice.by_ref());
			return;
		}
		/* Attempt to fill the dead region between the front and back segments
		the vector with the splice. If the splice exhausts (`return false`),
		then the `Drain` destructor will handle tail-section cleanup.
		*/
		if !self.drain.fill(&mut self.splice) {
			return;
		}

		let (lower, upper) = self.splice.size_hint();

		//  If the splice gives an exact upper bound on its remaining bits, move
		//  the drain’s tail and fill it. The signal can be safely discarded.
		if let Some(rem) = upper {
			//  Relocate the tail section to
			self.drain.resize_drain(rem);
			self.drain.fill(&mut self.splice);
			return;
		}

		/* If the slice did not give an upper bound, then it must be collected
		into a temporary which will either crash the program, or find an exact
		limit. This temporary can then be used to fill the drain.
		*/
		let mut tmp: BitVec = BitVec::with_capacity(lower);
		tmp.extend(self.splice.by_ref());
		match tmp.len() {
			0 => {},
			n => {
				self.drain.resize_drain(n);
				self.drain.fill(&mut tmp.into_iter());
			},
		}
	}
}
