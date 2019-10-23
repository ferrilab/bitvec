/*! Iteration processes for `BitSlice`.
!*/

use super::*;

use core::{
	cmp,
	mem,
};

impl<'a, C, T> IntoIterator for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = Iter<'a, C, T>;

	fn into_iter(self) -> Self::IntoIter {
		Iter {
			inner: self
		}
	}
}

/** Immutable slice iterator

This struct is created by the [`iter`] method on [`BitSlice`]s.

# Examples

Basic usage:

```rust
# use bitvec::prelude::*;
let data = 5u8;
let bits = data.bits::<LittleEndian>();

for bit in bits[.. 4].iter() {
    println!("{}", bit);
}
```

[`BitSlice`]: struct.BitSlice.html
[`iter`]: struct.BitSlice.html#method.iter
**/
#[derive(Clone, Debug)]
pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Views the underlying data as a subslice of the original data.
	///
	/// This has the same lifetime as the original slice, and so the iterator
	/// can continue to be used while this exists.
	pub fn as_bitslice(&self) -> &'a BitSlice<C, T> {
		self.inner
	}

	/// Views the underlying buffer.
	///
	/// This has the same rules as `BitSlice::as_slice`.
	pub fn as_slice(&self) -> &'a [T] {
		self.inner.as_slice()
	}

	/// Accesses the `BitPtr` representation of the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The `BitPtr` representation of the remaining slice.
	//  The linter is incorrect; this method is absolutely used.
	#[allow(dead_code)]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a bool;

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
	/// let bits = &1u8.bits::<LittleEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.split_first().map(|(b, r)| {
			self.inner = r;
			b
		})
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
	/// let bits = &0x4Bu8.bits::<BigEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of bits remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert_eq!(bits.iter().count(), 8);
	/// ```
	fn count(self) -> usize {
		self.len()
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
	///
	/// let bits = 2u8.bits::<BigEndian>();
	/// let mut iter = bits.iter();
	/// assert!(iter.nth(6).unwrap());
	/// assert!(!iter.nth(0).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty())
			.get(n ..)
			.and_then(|s| {
				self.inner = s;
				self.next()
			})
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.bits::<BigEndian>();
	/// assert!(bits.iter().last().unwrap());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next bit from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last bit in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.bits::<BigEndian>()[6 ..];
	/// let mut iter = bits.iter();
	/// assert!(iter.next_back().unwrap());
	/// assert!(!iter.next_back().unwrap());
	/// assert!(iter.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.split_last().map(|(b, r)| {
			self.inner = r;
			b
		})
	}
}

impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<C, T> AsRef<BitSlice<C, T>> for Iter<'_, C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.inner
	}
}

#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Send for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Sync for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> IntoIterator for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = BitGuard<'a, C, T>;
	type IntoIter = IterMut<'a, C, T>;

	fn into_iter(self) -> Self::IntoIter {
		IterMut {
			inner: self
		}
	}
}

/** Mutable slice iterator.

This struct is created by the [`iter_mut`] method on [`BitSlice`]s.

# Examples

Basic usage:

```rust
# use bitvec::prelude::*;
let mut data = 0u8;
let bits = data.bits_mut::<BigEndian>();
assert!(bits.not_any());
for mut bit in bits.iter_mut() {
    *bit = true;
}
assert!(bits.all());
```

[`BitSlice`]: struct.BitSlice.html
[`iter_mut`]: struct.BitSlice.html#method.iter_mut
**/
#[derive(Debug)]
pub struct IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<C, T>,
}

impl<'a, C, T> IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Views the underlying data as a subslice of the original data.
	///
	/// To avoid creating `&mut` references that alias, this is forced to
	/// consume the iterator.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	///
	/// {
	///     // Get an iterator over the bits:
	///     let mut iter = bits.iter_mut();
	///     // Advance to the next bit:
	///     iter.next();
	///     // If we print this bitslice, it will be seven bits long.
	///     println!("{}", iter.into_bitslice());
	/// }
	///
	/// // Now let’s modify a bit of the slice:
	/// {
	///     // Rebuild the iterator:
	///     let mut iter = bits.iter_mut();
	///     // Change the value of the first bit:
	///     *iter.next().unwrap() = true;
	/// }
	/// assert!(bits[0]);
	/// println!("{}", bits); // [10000000]
	/// ```
	pub fn into_bitslice(self) -> &'a mut BitSlice<C, T> {
		self.inner
	}

	/// Views the underlying buffer.
	///
	/// To avoid creating `&mut` references that alias, this is forced to
	/// consume the iterator.
	pub fn into_slice(self) -> &'a mut [T] {
		self.inner.as_mut_slice()
	}

	#[allow(dead_code)]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> Iterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = BitGuard<'a, C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_first_mut()
			.map(|(b, r)| {
				self.inner = r;
				b
			})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.inner.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.get_mut(n ..)
			.and_then(|s| {
				self.inner = s;
				self.next()
			})
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_last_mut()
			.map(|(b, r)| {
				self.inner = r;
				b
			})
	}
}

impl<'a, C, T> ExactSizeIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Send for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Sync for IterMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`chunk_size` bits at
a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`chunks`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks`]: struct.BitSlice.html#method.chunks
**/
#[derive(Clone, Debug)]
pub struct Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The width of the produced chunks.
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n if n < self.chunk_size =>
				Some(mem::replace(&mut self.inner, BitSlice::empty())),
			_ => {
				let (head, rest) = self.inner.split_at(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			len => {
				let (n, r) = (len / self.chunk_size, len % self.chunk_size);
				let out = n + (r > 0) as usize;
				(out, Some(out))
			},
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.chunk_size);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = start.checked_add(self.chunk_size)
			.map(|s| cmp::min(s, len))
			.unwrap_or(len);
		let (head, rest) = self.inner.split_at(end);
		self.inner = rest;
		Some(unsafe { head.get_unchecked(start .. ) })
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let rem = n % self.chunk_size;
				let size = if rem == 0 { self.chunk_size } else { rem };
				let (rest, tail) = self.inner.split_at(n - size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`chunk_size` bits at a
time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`chunk_size - 1` bits will be omitted but can be retrieved from the
[`remainder`] function from the iterator.

This struct is created by the [`chunks_exact`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks_exact`]: struct.BitSlice.html#method.chunks_exact
[`remainder`]: #method.remainder
**/
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<C, T>,
	/// Remainder of the original `BitSlice`.
	pub(super) extra: &'a BitSlice<C, T>,
	/// The width of the produced chunks.
	pub(super) chunk_size: usize,
}

impl<'a, C, T> ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `chunk_size - 1` bits.
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> Iterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.chunk_size => {
				self.inner = BitSlice::empty();
				None
			},
			_ => {
				let (head, rest) = self.inner.split_at(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.chunk_size;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.chunk_size);
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

impl<'a, C, T> DoubleEndedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.chunk_size => {
				self.inner = BitSlice::empty();
				None
			},
			n => {
				let (rest, tail) = self.inner.split_at(n - self.chunk_size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[derive(Debug)]
pub struct ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// Remainder of the original `BitSlice`.
	pub(super) extra: &'a mut BitSlice<C, T>,
	/// The width of the produced chunks.
	pub(super) chunk_size: usize,
}

impl<'a, C, T> ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `chunk_size - 1` elements.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> Iterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.chunk_size => None,
			_ => {
				let (head, rest) = slice.split_at_mut(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.chunk_size;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (start, ovf) = n.overflowing_mul(self.chunk_size);
		if start >= slice.len() || ovf {
			return None;
		}
		let (_, tail) = slice.split_at_mut(start);
		self.inner = tail;
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.chunk_size => None,
			n => {
				let (rest, tail) = slice.split_at_mut(n - self.chunk_size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/** An iterator over a slice in (non-overlapping) mutable chunks (`chunk_size`
bits at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`chunks_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks_mut`]: struct.BitSlice.html#chunks_mut
**/
#[derive(Debug)]
pub struct ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<C, T>,
	/// The width of the produced chunks.
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			n if n < self.chunk_size =>
				Some(slice),
			_ => {
				let (head, rest) = slice.split_at_mut(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			len => {
				let (n, r) = (len / self.chunk_size, len % self.chunk_size);
				let out = n + (r > 0) as usize;
				(out, Some(out))
			},
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.chunk_size);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let end = start.checked_add(self.chunk_size)
			.map(|s| cmp::min(s, len))
			.unwrap_or(len);
		let (head, rest) = mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_at_mut(end);
		self.inner = rest;
		Some(unsafe { head.get_unchecked_mut(start ..) })
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let rem = n % self.chunk_size;
				let size = if rem == 0 { self.chunk_size } else { rem };
				let (rest, tail) = mem::replace(
					&mut self.inner,
					BitSlice::empty_mut(),
				).split_at_mut(n - size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[derive(Clone, Debug)]
pub struct RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	pub(super) inner: &'a BitSlice<C, T>,
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let len = cmp::min(n, self.chunk_size);
				let (rest, tail) = self.inner.split_at(n - len);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			n => {
				let (len, rem) = (n / self.chunk_size, n % self.chunk_size);
				let len = len + (rem > 0) as usize;
				(len, Some(len))
			},
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.inner.len();
		let (end, ovf) = n.overflowing_mul(self.chunk_size);
		if end >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = len - end;
		self.inner = unsafe { self.inner.get_unchecked(.. end) };
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let rem = n % self.chunk_size;
				let len = if rem == 0 { self.chunk_size } else { rem };
				let (head, rest) = self.inner.split_at(len);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[derive(Clone, Debug)]
pub struct RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	pub(super) inner: &'a BitSlice<C, T>,
	pub(super) extra: &'a BitSlice<C, T>,
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.chunk_size => {
				self.inner = BitSlice::empty();
				None
			},
			n => {
				let (rest, tail) = self.inner.split_at(n - self.chunk_size);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.chunk_size;
		(len, Some(len))
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.inner.len();
		let (end, ovf) = n.overflowing_mul(self.chunk_size);
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

impl<'a, C, T> DoubleEndedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.chunk_size => {
				self.inner = BitSlice::empty();
				None
			},
			_ => {
				let (head, rest) = self.inner.split_at(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[derive(Debug)]
pub struct RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	pub(super) inner: &'a mut BitSlice<C, T>,
	pub(super) extra: &'a mut BitSlice<C, T>,
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.chunk_size => None,
			n => {
				let (rest, tail) = slice.split_at_mut(n - self.chunk_size);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.chunk_size => None,
			_ => {
				let (head, rest) = slice.split_at_mut(self.chunk_size);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

#[derive(Debug)]
pub struct RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	pub(super) inner: &'a mut BitSlice<C, T>,
	pub(super) chunk_size: usize,
}

impl<'a, C, T> Iterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			n => {
				let len = cmp::min(n, self.chunk_size);
				let (rest, tail) = slice.split_at_mut(n - len);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			n => {
				let (len, rem) = (n / self.chunk_size, n % self.chunk_size);
				let len = len + (rem > 0) as usize;
				(len, Some(len))
			},
		}
	}

	fn count(self) -> usize {
		self.len()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let len = slice.len();
		let (end, ovf) = n.overflowing_mul(self.chunk_size);
		if end >= len || ovf {
			return None;
		}
		let end = len - end;
		let start = end.checked_sub(self.chunk_size).unwrap_or(0);
		let (rest, tail) = slice.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = rest;
		Some(nth)
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			n => {
				let rem = n % self.chunk_size;
				let len = if rem == 0 { self.chunk_size } else { rem };
				let (head, rest) = slice.split_at_mut(len);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/** An iterator over overlapping subslices of some width.

This struct is created by the [`windows`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`windows`]: struct.BitSlice.html#method.windows
**/
#[derive(Clone, Debug)]
pub struct Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<C, T>,
	/// The width of the produced windows.
	pub(super) width: usize,
}

impl<'a, C, T> Iterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			None
		}
		else {
			let out = unsafe { self.inner.get_unchecked(.. self.width) };
			self.inner = unsafe { self.inner.get_unchecked(1 ..) };
			Some(out)
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if self.width > len {
			(0, Some(0))
		}
		else {
			let count = len - self.width + 1;
			(count, Some(count))
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
		self.inner = unsafe { self.inner.get_unchecked(n ..) };
		self.next()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, C, T> DoubleEndedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if !(1 .. self.width).contains(&len) {
			self.inner = BitSlice::empty();
			return None;
		}
		let out = unsafe { self.inner.get_unchecked(len - self.width ..) };
		self.inner = unsafe { self.inner.get_unchecked(.. len - 1) };
		Some(out)
	}
}

impl<'a, C, T> ExactSizeIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}
