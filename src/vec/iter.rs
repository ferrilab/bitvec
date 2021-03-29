//! Iterators over `Vec<T>`.

use alloc::vec::Vec;
use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::{
		FromIterator,
		FusedIterator,
	},
	mem::{
		self,
		ManuallyDrop,
	},
	ops::{
		Range,
		RangeBounds,
	},
};

use tap::{
	Pipe,
	Tap,
	TapOptional,
};

use super::BitVec;
use crate::{
	boxed::BitBox,
	devel as dvl,
	order::BitOrder,
	ptr::{
		BitPtrRange,
		BitRef,
		Mut,
		Mutability,
	},
	slice::BitSlice,
	store::BitStore,
	view::BitView,
};

/** Extends a `BitVec` from a `bool` producer.

# Notes

This is the second-slowest possible way to append bits to a bit-vector, second
only to `for bit in bits { bitvec.push(bit); }`. **Do not** use this if you have
any other choice.

If you are extending a bit-vector from the contents of a bit-slice, use
[`BitVec::extend_from_bitslice`] instead. That method will never be *slower*
than this. When the source bit-slice does not match the destination bit-vector’s
type parameters, it will still be faster by virtue of knowing the bit-slice
length upfront; when the type parameters match, it will optimize to `memcpy`
with some bookkeeping.
**/
impl<O, T> Extend<bool> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = bool> {
		let mut iter = iter.into_iter();
		#[allow(irrefutable_let_patterns)] // Removing the `if` is unstable.
		if let (_, Some(n)) | (n, None) = iter.size_hint() {
			self.reserve(n);
			let len = self.len();
			let new_len = len + n;
			let new = unsafe { self.get_unchecked_mut(len .. new_len) };

			let mut pulled = 0;
			//  In theory, using direct pointer writes ought to be the fastest
			//  general condition.
			for (ptr, bit) in new.as_mut_bitptr_range().zip(iter.by_ref()) {
				unsafe {
					ptr.write(bit);
				}
				pulled += 1;
			}
			unsafe {
				self.set_len(len + pulled);
			}
		}

		//  Well-behaved iterators will reduce this to a single branch.
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

/// ***DO NOT*** use this. You clearly have a [`BitSlice`]. Use
/// [`BitVec::extend_from_bitslice`].
impl<'a, M, O1, O2, T1, T2> Extend<BitRef<'a, M, O2, T2>> for BitVec<O1, T1>
where
	M: Mutability,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = BitRef<'a, M, O2, T2>> {
		self.extend(iter.into_iter().map(|bit| *bit));
	}
}

impl<O, T> Extend<T> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = T> {
		for elem in iter.into_iter() {
			self.extend_from_bitslice(elem.view_bits::<O>());
		}
	}
}

impl<'a, O, T> Extend<&'a T> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn extend<I>(&mut self, iter: I)
	where I: IntoIterator<Item = &'a T> {
		for elem in iter.into_iter() {
			self.extend_from_bitslice(elem.view_bits::<O>());
		}
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
		Self::new().tap_mut(|bv| bv.extend(iter.into_iter()))
	}
}

/// ***DO NOT*** use this. You clearly have a [`BitSlice`]. Use
/// [`BitVec::from_bitslice`] instead.
impl<'a, M, O1, O2, T1, T2> FromIterator<BitRef<'a, M, O2, T2>>
	for BitVec<O1, T1>
where
	M: Mutability,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = BitRef<'a, M, O2, T2>> {
		Self::new().tap_mut(|bv| bv.extend(iter.into_iter()))
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

/** Collect a sequence of memory elements into a bit-vector.

This is a short-hand for, and implemented as, `iter.collect::<Vec<_>>().into()`.

This is not a standard-library API, and was added for [Issue #83].

[Issue #83]: https://github.com/bitvecto-rs/bitvec/issues/83
**/
impl<O, T> FromIterator<T> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = T> {
		iter.into_iter().collect::<Vec<_>>().pipe(Self::from_vec)
	}
}

impl<'a, O, T> FromIterator<&'a T> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from_iter<I>(iter: I) -> Self
	where I: IntoIterator<Item = &'a T> {
		let mut vec = iter
			.into_iter()
			.map(BitStore::load_value)
			.collect::<Vec<T::Mem>>()
			.pipe(ManuallyDrop::new);
		let (ptr, len, capa) = (vec.as_mut_ptr(), vec.len(), vec.capacity());
		unsafe { Vec::from_raw_parts(ptr as *mut T, len, capa) }
			.pipe(Self::from_vec)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> IntoIterator for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = <BitBox<O, T> as IntoIterator>::IntoIter;
	type Item = <BitBox<O, T> as IntoIterator>::Item;

	#[inline(always)]
	fn into_iter(self) -> Self::IntoIter {
		self.into_boxed_bitslice().into_iter()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> IntoIterator for &'a BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = <&'a BitSlice<O, T> as IntoIterator>::IntoIter;
	type Item = <&'a BitSlice<O, T> as IntoIterator>::Item;

	#[inline(always)]
	fn into_iter(self) -> Self::IntoIter {
		self.as_bitslice().into_iter()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> IntoIterator for &'a mut BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = <&'a mut BitSlice<O, T> as IntoIterator>::IntoIter;
	type Item = <&'a mut BitSlice<O, T> as IntoIterator>::Item;

	#[inline(always)]
	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_bitslice().into_iter()
	}
}

/** A draining iterator for [`BitVec`].

This `struct` is created by the [`.drain()`] method on [`BitVec`].

# Original

[`vec::Drain`](alloc::vec::Drain)

[`BitVec`]: crate::vec::BitVec
[`.drain()`]: crate::vec::BitVec::drain
**/
pub struct Drain<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Exclusive reference to the vector this drains.
	source: &'a mut BitVec<O, T>,
	/// The range of the source vector’s buffer being drained.
	drain: BitPtrRange<Mut, O, T>,
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
		//  Hold the current vector size for bounds comparison.
		let len = source.len();
		//  Normalize the input range and assert that it is within bounds.
		let drain = dvl::normalize_range(range, len);
		dvl::assert_range(drain.clone(), len);

		//  The tail region is everything after the drain, before the real end.
		let tail = drain.end .. len;
		//  The drain span is an iterator over the provided range.
		let drain = unsafe {
			//  Set the source vector to end before the drain.
			source.set_len(drain.start);
			//  Grab the drain range and produce an iterator over it.
			source
				.as_mut_bitslice()
				.get_unchecked_mut(drain)
				//  Detach the region from the `source` borrow.
				.as_mut_bitptr_range()
		};
		Self {
			source,
			drain,
			tail,
		}
	}

	/// Returns the remaining bits of this iterator as a [`BitSlice`].
	///
	/// # Original
	///
	/// [`Drain::as_slice`](alloc::vec::Drain::as_slice)
	///
	/// # API Differences
	///
	/// This method is renamed, as it operates on a [`BitSlice`] rather than an
	/// element slice.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn as_bitslice(&self) -> &'a BitSlice<O, T> {
		self.drain.clone().into_bitspan().to_bitslice_ref()
	}

	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `as_bitslice` to view the underlying slice"]
	pub fn as_slice(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}

	/// Attempts to overwrite the drained region with another iterator.
	///
	/// # Type Parameters
	///
	/// - `I`: Some source of `bool`s.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `iter`: A source of `bool`s with which to overwrite the drained span.
	///
	/// # Returns
	///
	/// Whether the drained span was completely filled, or if the replacement
	/// source `iter`ator was exhausted first.
	///
	/// # Effects
	///
	/// The source vector is extended to include all bits filled in from the
	/// replacement `iter`ator, but is *not* extended to include the tail, even
	/// if drained region is completely filled. This work is done in the
	/// destructor.
	fn fill<I>(&mut self, iter: &mut I) -> FillStatus
	where I: Iterator<Item = bool> {
		let bitvec = &mut *self.source;
		//  Get the length of the source vector. This will be grown as `iter`
		//  writes into the drain span.
		let mut len = bitvec.len();
		//  Get the drain span as a bit-pointer range.
		let span = unsafe { bitvec.get_unchecked_mut(len .. self.tail.start) }
			.as_mut_bitptr_range();

		//  Set the exit flag to assume completion.
		let mut out = FillStatus::FullSpan;
		//  Write the `iter` bits into the drain `span`.
		for ptr in span {
			//  While the `iter` is not exhausted, write it into the span and
			//  increase the vector length counter.
			if let Some(bit) = iter.next() {
				unsafe {
					ptr.write(bit);
				}
				len += 1;
			}
			//  If the `iter` exhausts before the drain `span` is filled, set
			//  the exit flag accordingly.
			else {
				out = FillStatus::EmptyInput;
				break;
			}
		}
		//  Update the vector length counter to include the bits written by
		//  `iter`.
		unsafe {
			bitvec.set_len(len);
		}
		out
	}

	/// Inserts `additional` capacity between the vector and the tail.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `additional`: The amount of new bits to reserve between the head and
	///   tail sections of the vector.
	///
	/// # Effects
	///
	/// This is permitted to reällocate the buffer in order to grow capacity.
	/// After completion, the tail segment will be relocated to begin
	/// `additional` bits after the head segment ends. The drain iteration
	/// cursor will not be modified.
	unsafe fn move_tail(&mut self, additional: usize) {
		if additional == 0 {
			return;
		}

		let bitvec = &mut *self.source;
		let tail_len = self.tail.end - self.tail.start;

		//  Reserve allocation capacity for `additional` and the tail.
		//  `.reserve()` begins from the `bitvec.len()`, so the tail length must
		//  still be included.
		let full_len = additional + tail_len;
		bitvec.reserve(full_len);
		let new_tail_start = additional + self.tail.start;
		let orig_tail = mem::replace(
			&mut self.tail,
			new_tail_start .. new_tail_start + tail_len,
		);
		//  Temporarily resize the vector to include the full buffer. This is
		//  necessary until `copy_within_unchecked` stops using `.len()`
		//  internally.
		let len = bitvec.len();
		bitvec.set_len(full_len);
		bitvec.copy_within_unchecked(orig_tail, new_tail_start);
		bitvec.set_len(len);
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> AsRef<BitSlice<O, T>> for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> Debug for Drain<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("Drain").field(&self.as_bitslice()).finish()
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
		self.drain.next().map(crate::ptr::range::read_raw)
	}

	#[inline(always)]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	#[inline(always)]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth(n).map(crate::ptr::range::read_raw)
	}

	#[inline(always)]
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
		self.drain.next_back().map(crate::ptr::range::read_raw)
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth_back(n).map(crate::ptr::range::read_raw)
	}
}

impl<O, T> ExactSizeIterator for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
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

unsafe impl<O, T> Send for Drain<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

unsafe impl<O, T> Sync for Drain<'_, O, T>
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
		//  Grab the tail range descriptor
		let tail = self.tail.clone();
		//  And compute its length.
		let tail_len = tail.end - tail.start;
		//  If the tail region is empty, then there is no cleanup work to do.
		if tail_len == 0 {
			return;
		}
		//  Otherwise, access the source vector,
		let bitvec = &mut *self.source;
		//  And grab its current end.
		let old_len = bitvec.len();
		let new_len = old_len + tail_len;
		unsafe {
			//  Expand the vector to include where the tail bits will be.
			bitvec.set_len(new_len);
			//  Then move the tail bits into the new location.
			bitvec.copy_within_unchecked(tail, old_len);
			//  This ordering is important! `copy_within_unchecked` uses the
			//  `len` boundary.
		}
	}
}

/** `std` uses a `bool` flag for done/not done, which is less clear about what
it signals.

See <https://github.com/rust-lang/rust/blob/5779815/library/alloc/src/vec.rs#L3327-L3348>.
**/
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum FillStatus {
	/// The drain span is completely filled.
	FullSpan   = 0,
	/// The replacement source is completely emptied.
	EmptyInput = 1,
}

/** A splicing iterator for [`BitVec`].

This struct is created by the [`.splice()`] method on [`BitVec`]. See its
documentation for more.

# Original

[`vec::Splice`](alloc::vec::Splice)

[`BitVec`]: crate::vec::BitVec
[`.splice()`]: crate::vec::BitVec::splice
**/
#[derive(Debug)]
pub struct Splice<'a, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	/// The region of the vector being spliced.
	drain: Drain<'a, O, T>,
	/// The bitstream to be written into the drain.
	splice: I,
}

impl<'a, O, T, I> Splice<'a, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	/// Constructs a splice out of a drain and a replacement.
	#[inline]
	pub(super) fn new<IntoIter>(
		drain: Drain<'a, O, T>,
		splice: IntoIter,
	) -> Self
	where
		IntoIter: IntoIterator<IntoIter = I, Item = bool>,
	{
		let splice = splice.into_iter();
		Self { drain, splice }
	}
}

impl<O, T, I> Iterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.drain.next().tap_some(|_| {
			/* Attempt to write a bit into the now-vacated slot at the front of
			the `Drain`. If the `splice` stream produces a bit, then it is
			written into the end of the `Drain`’s buffer, extending it by one.
			This works because `Drain` always truncates its vector to the front
			edge of the drain region, so `bv.len()` is always the first bit of
			the `Drain` region if the `Drain` is willing to yield a bit.
			*/
			if let Some(bit) = self.splice.next() {
				unsafe {
					let bv = &mut *self.drain.source;
					let len = bv.len();
					bv.set_len_unchecked(len + 1);
					bv.set_unchecked(len, bit);
				}
			}
		})
	}

	#[inline(always)]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	#[inline(always)]
	fn count(self) -> usize {
		self.len()
	}

	#[inline(always)]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T, I> DoubleEndedIterator for Splice<'_, O, T, I>
where
	O: BitOrder,
	T: BitStore,
	I: Iterator<Item = bool>,
{
	#[inline(always)]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}

	#[inline(always)]
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
	#[inline(always)]
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
		let tail = self.drain.tail.clone();
		let tail_len = tail.end - tail.start;
		let bitvec = &mut *self.drain.source;

		//  If the `drain` has no tail span, then extend the vector with the
		//  splice and exit.
		if tail_len == 0 {
			bitvec.extend(self.splice.by_ref());
			return;
		}

		//  Fill the drained range first. If the `splice` exhausts, then the
		//  `Drain` destructor will handle relocating the vector tail segment.
		if let FillStatus::EmptyInput = self.drain.fill(&mut self.splice) {
			return;
		}

		//  If the `splice` has not yet exhausted, then the `Drain` needs to
		//  adjust to receive its contents.
		let len = match self.splice.size_hint() {
			(n, None) | (_, Some(n)) => n,
		};
		unsafe {
			self.drain.move_tail(len);
		}
		//  Now that the tail has been relocated, fill the `splice` into it. If
		//  this exhausts the `splice`, exit.
		if let FillStatus::EmptyInput = self.drain.fill(&mut self.splice) {
			return;
		}

		/* If the `splice` *still* has bits to provide, then its `.size_hint()`
		is untrustworthy. Collect the `splice` into a vector, then insert the
		vector into the spliced region.
		*/
		let mut collected = self.splice.by_ref().collect::<BitVec>().into_iter();
		let len = collected.len();
		if len > 0 {
			unsafe {
				self.drain.move_tail(len);
			}
			let filled = self.drain.fill(&mut collected);
			debug_assert_eq!(filled, FillStatus::EmptyInput);
			debug_assert_eq!(collected.len(), 0);
		}
	}
}
