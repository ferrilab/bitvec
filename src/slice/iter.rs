/*! Iterator implementations for `BitSlice`.

This module defines the various iteration behaviors for `BitSlice`, mirroring
the slice iterators of the standard library.
!*/

use super::{
	BitGuard,
	BitSlice,
};

use crate::{
	cursor::Cursor,
	store::BitStore,
};

use core::{
	cmp,
	iter::FusedIterator,
	mem,
};

#[cfg(feature = "alloc")]
use crate::pointer::BitPtr;

impl<C, T> BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Provides read-only iteration across the slice domain.
	///
	/// The iterator returned from this method implements `ExactSizeIterator`
	/// and `DoubleEndedIterator` just as the consuming `.into_iter()` method’s
	/// iterator does.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An iterator over all bits in the slice domain, in `C` and `T` ordering.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 64u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut iter = bits[.. 2].iter();
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	pub fn iter(&self) -> Iter<C, T> {
		self.into_iter()
	}

	/// Provides writable iteration across the slice domain.
	///
	/// The iterator returned from this method has the same behavior as the
	/// read-only iterator produced by `.iter()`. However, it yields `BitGuard`
	/// writeable references, rather than plain `bool`s.
	pub fn iter_mut(&mut self) -> IterMut<C, T> {
		IterMut {
			inner: self
		}
	}

	/// Produces a sliding iterator over consecutive windows in the slice. Each
	/// windows has the width `size`. The windows overlap. If the slice is
	/// shorter than `size`, the produced iterator is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each window.
	///
	/// # Returns
	///
	/// An iterator which yields sliding views into the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut windows = bits.windows(4);
	/// assert_eq!(windows.next(), Some(&bits[0 .. 4]));
	/// assert_eq!(windows.next(), Some(&bits[1 .. 5]));
	/// assert_eq!(windows.next(), Some(&bits[2 .. 6]));
	/// assert_eq!(windows.next(), Some(&bits[3 .. 7]));
	/// assert_eq!(windows.next(), Some(&bits[4 .. 8]));
	/// assert!(windows.next().is_none());
	/// ```
	pub fn windows(&self, size: usize) -> Windows<C, T> {
		assert_ne!(size, 0, "Window width cannot be zero");
		Windows {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut chunks = bits.chunks(3);
	/// assert_eq!(chunks.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks.next(), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks.next(), Some(&bits[6 .. 8]));
	/// assert!(chunks.next().is_none());
	/// ```
	pub fn chunks(&self, size: usize) -> Chunks<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		Chunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&mut self`: The produced iterator locks this bitslice until the
	///   iterator is destroyed, as each chunk has write access to it.
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut chunks = bits.chunks_mut(3);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(1, false);
	/// }
	/// assert_eq!(src, 0b0110_1110);
	/// ```
	pub fn chunks_mut(&mut self, size: usize) -> ChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		ChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk. The iterator will never produce
	///   subslices narrower than this width.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks_exact.next(), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.next().is_none());
	/// assert_eq!(chunks_exact.remainder(), &bits[6 .. 8]);
	/// ```
	pub fn chunks_exact(&self, size: usize) -> ChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at(len);
		ChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&mut self`: The produced iterator locks this bitslice until the
	///   iterator is destroyed, as each chunk has write access to it.
	/// - `size`: The width of each chunk. The iterator will never produce
	///   subslices narrower than this width.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut chunks_exact = bits.chunks_exact_mut(3);
	///  chunks_exact.next().unwrap().set(2, true);
	///  chunks_exact.next().unwrap().set(2, true);
	///  assert!(chunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0110_1111);
	/// ```
	pub fn chunks_exact_mut(&mut self, size: usize) -> ChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at_mut(len);
		ChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.bits::<BigEndian>();
	/// let mut rchunks = bits.rchunks(3);
	/// assert_eq!(rchunks.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks.next(), Some(&bits[2 .. 5]));
	/// assert_eq!(rchunks.next(), Some(&bits[0 .. 2]));
	/// assert!(rchunks.next().is_none());
	/// ```
	pub fn rchunks(&self, size: usize) -> RChunks<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&mut self`: The produced iterator locks this bitslice until the
	///   iterator is destroyed, as each chunk has write access to it.
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut rchunks = bits.rchunks_mut(3);
	///  rchunks.next().unwrap().set(0, true);
	///  rchunks.next().unwrap().set(2, false);
	///  rchunks.next().unwrap().set(1, false);
	///  assert!(rchunks.next().is_none());
	/// }
	/// assert_eq!(src, 0b0000_0111);
	/// ```
	pub fn rchunks_mut(&mut self, size: usize) -> RChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk. The iterator will never produce
	///   subslices narrower than this width.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b0100_1011u8.bits::<Local>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks_exact.next(), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.next().is_none());
	/// assert_eq!(rchunks_exact.remainder(), &bits[0 .. 2]);
	/// ```
	pub fn rchunks_exact(&self, size: usize) -> RChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at(self.len() % size);
		RChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&mut self`: The produced iterator locks this bitslice until the
	///   iterator is destroyed, as each chunk has write access to it.
	/// - `size`: The width of each chunk. The iterator will never produce
	///   subslices narrower than this width.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.bits_mut::<BigEndian>();
	///  let mut rchunks_exact = bits.rchunks_exact_mut(3);
	///  rchunks_exact.next().unwrap().set(0, true);
	///  rchunks_exact.next().unwrap().set(2, false);
	///  assert!(rchunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0100_0111);
	/// ```
	pub fn rchunks_exact_mut(&mut self, size: usize) -> RChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at_mut(self.len() % size);
		RChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}
}

/** Produces a read-only iterator over all the bits in the `BitSlice`.

This iterator follows the ordering in the `BitSlice` type, and implements
`ExactSizeIterator` as `BitSlice` has a known, fixed, length, and
`DoubleEndedIterator` as it has known ends.
**/
impl<'a, C, T> IntoIterator for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = Iter<'a, C, T>;

	/// Iterates over the slice.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An iterator over the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b1010_1100u8.bits::<BigEndian>();
	/// let mut count = 0;
	/// for bit in bits {
	///   if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		Iter {
			inner: self
		}
	}
}

/** State keeper for chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let size = cmp::min(len, self.width);
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if len == 0 {
			return (0, Some(0));
		}
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| cmp::min(s, len))
			.unwrap_or(len);
		let out = &self.inner[start .. end];
		self.inner = &self.inner[end ..];
		Some(out)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(len - size);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let size = cmp::min(len, self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if len == 0 {
			return (0, Some(0));
		}
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| cmp::min(s, len))
			.unwrap_or(len);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (_, nth) = head.split_at_mut(end - start);
		self.inner = tail;
		Some(nth)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.remainder(), &bits[6 ..]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			//  TODO(myrrlyn): Prove this assignment unnecessary
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(len - self.width);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (_, tail) = self.inner.split_at(start);
		self.inner = tail;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remaining bits not included in chunked iteration.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// A writable bitslice over the remaining bits iteration will not reach.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}

	/// Produces the remaining bits not included in chunked iteration.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A writable bitslice over the remaining bits iteration will not reach.
	pub fn remainder(&mut self) -> &'a mut BitSlice<C, T> {
		mem::replace(&mut self.extra, BitSlice::empty_mut())
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(len - self.width);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (_, tail) = tmp.split_at_mut(start);
		self.inner = tail;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	#[cfg(feature = "alloc")]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> DoubleEndedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let (bit, rest) = self.inner.split_last()?;
		self.inner = rest;
		Some(bit)
	}
}

impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		let (bit, rest) = self.inner.split_first()?;
		self.inner = rest;
		Some(bit)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the urderlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
}

impl<'a, C, T> DoubleEndedIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}

		let (head, tail) = mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_at_mut(len - 1);
		self.inner = head;
		Some(tail.at(0))
	}
}

impl<'a, C, T> ExactSizeIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = BitGuard<'a, C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}

		let (head, tail) = mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_at_mut(1);
		self.inner = tail;
		Some(head.at(0))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		self.inner = &mut mem::replace(&mut self.inner, BitSlice::empty_mut())[n ..];
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for reverse chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let size = cmp::min(len, self.width);
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if len == 0 {
			return (0, Some(0));
		}
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if end >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		// Can't underflow because of the check above
		let end = len - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let nth = &self.inner[start .. end];
		self.inner = &self.inner[.. start];
		Some(nth)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable reverse chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len == 0 {
			return None;
		}
		let size = cmp::min(len, self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - size);
		self.inner = head;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if len == 0 {
			return (0, Some(0));
		}
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if end >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		// Can't underflow because of the check above
		let end = len - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = head;
		Some(nth)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for reverse exact iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that the iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// let rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.remainder(), &bits[.. 2]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(len - self.width);
		self.inner = head;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if end >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, _) = self.inner.split_at(len - end);
		self.inner = head;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for mutable reverse exact chunked iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Debug)]
pub struct RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - self.width);
		self.inner = head;
		Some(tail)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, _) = tmp.split_at_mut(tlen - end);
		self.inner = head;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** State keeper for sliding-window iteration over a `BitSlice`.

# Type Parameters

- `C`: The bit-order type of the underlying `BitSlice`.
- `T`: The storage type of the underlying `BitSlice`.

# Lifetimes

- `'a`: The lifetime of the underlying `BitSlice`.
**/
#[derive(Clone, Debug)]
pub struct Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the windows.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if len < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let out = &self.inner[len - self.width ..];
		self.inner = &self.inner[.. len - 1];
		Some(out)
	}
}

impl<'a, C, T> ExactSizeIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			None
		}
		else {
			let out = &self.inner[.. self.width];
			self.inner = &self.inner[1 ..];
			Some(out)
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if self.width > len {
			(0, Some(0))
		}
		else {
			let len = len - self.width + 1;
			(len, Some(len))
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_add(self.width);
		if end > self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let out = &self.inner[n .. end];
		self.inner = &self.inner[n + 1 ..];
		Some(out)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}
