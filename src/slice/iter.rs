//! Iteration processes for `BitSlice`.

//  TODO(myrrlyn, 2019-10-23): Upgrade to 1.37.0 and add `nth_back` implementations.

use super::*;

use core::{
	cmp,
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::FusedIterator,
	mem,
};

impl<'a, O, T> IntoIterator for &'a BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = Iter<'a, O, T>;

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
let bits = data.bits::<Lsb0>();

for bit in bits[.. 4].iter() {
    println!("{}", bit);
}
```

[`BitSlice`]: struct.BitSlice.html
[`iter`]: struct.BitSlice.html#method.iter
**/
#[derive(Clone, Debug)]
pub struct Iter<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
}

impl<'a, O, T> Iter<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Views the underlying data as a subslice of the original data.
	///
	/// This has the same lifetime as the original slice, and so the iterator
	/// can continue to be used while this exists.
	#[inline]
	pub fn as_bitslice(&self) -> &'a BitSlice<O, T> {
		self.inner
	}

	/// Views the underlying buffer.
	///
	/// This has the same rules as `BitSlice::as_slice`.
	#[inline]
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

impl<'a, O, T> Iterator for Iter<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.split_first().map(|(b, r)| {
			self.inner = r;
			b
		})
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty())
			.get(n ..)
			.and_then(|s| {
				self.inner = s;
				self.next()
			})
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for Iter<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.split_last().map(|(b, r)| {
			self.inner = r;
			b
		})
	}
}

impl<O, T> ExactSizeIterator for Iter<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for Iter<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> AsRef<BitSlice<O, T>> for Iter<'_, O, T>
where O: BitOrder, T: BitStore {
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.inner
	}
}

impl<O, T> AsRef<[T]> for Iter<'_, O, T>
where O: BitOrder, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.inner.as_slice()
	}
}

impl<'a, O, T> IntoIterator for &'a mut BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = BitMut<'a, O, T>;
	type IntoIter = IterMut<'a, O, T>;

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
let bits = data.bits_mut::<Msb0>();
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
pub struct IterMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
}

impl<'a, O, T> IterMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
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
	/// let bits = data.bits_mut::<Msb0>();
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
	pub fn into_bitslice(self) -> &'a mut BitSlice<O, T> {
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

impl<'a, O, T> Iterator for IterMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = BitMut<'a, O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_first_mut()
			.map(|(b, r)| {
				self.inner = r;
				b
			})
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.inner.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.get_mut(n ..)
			.and_then(|s| {
				self.inner = s;
				self.next()
			})
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for IterMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		mem::replace(&mut self.inner, BitSlice::empty_mut())
			.split_last_mut()
			.map(|(b, r)| {
				self.inner = r;
				b
			})
	}
}

impl<O, T> ExactSizeIterator for IterMut<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for IterMut<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`width` bits at a
time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`chunks`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks`]: struct.BitSlice.html#method.chunks
**/
#[derive(Clone, Debug)]
pub struct Chunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> Iterator for Chunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n if n <= self.width =>
				Some(mem::replace(&mut self.inner, BitSlice::empty())),
			_ => {
				let (head, rest) = self.inner.split_at(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			len => {
				let (n, r) = (len / self.width, len % self.width);
				let out = n + (r > 0) as usize;
				(out, Some(out))
			},
		}
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = self.width.overflowing_mul(n);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = unsafe { self.inner.get_unchecked(start ..) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for Chunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			len => {
				let rem = len % self.width;
				let size = if rem == 0 { self.width } else { rem };
				let (rest, tail) = self.inner.split_at(len - size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for Chunks<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for Chunks<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`width` bits at a
time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`width - 1` bits will be omitted but can be retrieved from the
[`remainder`] function from the iterator.

This struct is created by the [`chunks_exact`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks_exact`]: struct.BitSlice.html#method.chunks_exact
[`remainder`]: #method.remainder
**/
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// Remainder of the original `BitSlice`.
	pub(super) extra: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> ChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `width - 1` bits.
	pub fn remainder(&self) -> &'a BitSlice<O, T> {
		self.extra
	}
}

impl<'a, O, T> Iterator for ChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.width => {
				self.inner = BitSlice::empty();
				None
			},
			_ => {
				let (head, rest) = self.inner.split_at(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = self.width.overflowing_mul(n);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = unsafe { self.inner.get_unchecked(start ..) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for ChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			len if len < self.width => {
				self.inner = BitSlice::empty();
				None
			},
			len => {
				let (rest, tail) = self.inner.split_at(len - self.width);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for ChunksExact<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for ChunksExact<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-ovelapping) mutable chunks (`width` bits at
a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`width - 1` elements will be omitted but can be retrieved from the
[`into_remainder`] function from the iterator.

This struct is created by the [`chunks_exact_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks_exact_mut`]: struct.BitSlice.html#method.chunks_exact_mut
[`into_remainder`]: #method.into_remainder
**/
#[derive(Debug)]
pub struct ChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
	/// Remainder of the original `BitSlice`.
	pub(super) extra: &'a mut BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> ChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `width - 1` bits.
	pub fn into_remainder(self) -> &'a mut BitSlice<O, T> {
		self.extra
	}
}

impl<'a, O, T> Iterator for ChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.width => None,
			_ => {
				let (head, rest) = slice.split_at_mut(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (start, ovf) = self.width.overflowing_mul(n);
		if start >= slice.len() || ovf {
			return None;
		}
		self.inner = unsafe { slice.get_unchecked_mut(start ..) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for ChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			len if len < self.width => None,
			len => {
				let (rest, tail) = slice.split_at_mut(len - self.width);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for ChunksExactMut<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for ChunksExactMut<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) mutable chunks (`width` bits
at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`chunks_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`chunks_mut`]: struct.BitSlice.html#chunks_mut
**/
#[derive(Debug)]
pub struct ChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> Iterator for ChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			n if n <= self.width => Some(slice),
			_ => {
				let (head, rest) = slice.split_at_mut(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			len => {
				let (n, r) = (len / self.width, len % self.width);
				let out = n + (r > 0) as usize;
				(out, Some(out))
			},
		}
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (start, ovf) = self.width.overflowing_mul(n);
		if start >= slice.len() || ovf {
			return None;
		}
		self.inner = unsafe { slice.get_unchecked_mut(start ..) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for ChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			len => {
				let rem = len % self.width;
				let size = if rem == 0 { self.width } else { rem };
				let (rest, tail) = slice.split_at_mut(len - size);
				self.inner = rest;
				Some(tail)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for ChunksMut<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for ChunksMut<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`width` bits at a
time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`rchunks`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rchunks`]: struct.BitSlice.html#method.rchunks
**/
#[derive(Clone, Debug)]
pub struct RChunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> Iterator for RChunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let len = cmp::min(n, self.width);
				let (rest, tail) = self.inner.split_at(n - len);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			n => {
				let (len, rem) = (n / self.width, n % self.width);
				let len = len + (rem > 0) as usize;
				(len, Some(len))
			},
		}
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.inner.len();
		let (end, ovf) = self.width.overflowing_mul(n);
		if end >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = len - end;
		self.inner = unsafe { self.inner.get_unchecked(.. end) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for RChunks<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			0 => None,
			n => {
				let rem = n % self.width;
				let len = if rem == 0 { self.width } else { rem };
				let (head, rest) = self.inner.split_at(len);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for RChunks<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for RChunks<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) chunks (`width` bits
at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`width - 1` bits will be omitted but can be retrieved from the [`remainder`]
function from the iterator.

This struct is created by the [`rchunks_exact`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rchunks_exact`]: struct.BitSlice.html#method.rchunks_exact
[`remainder`]: #method.remainder
**/
#[derive(Clone, Debug)]
pub struct RChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// Remainder of the original `BitSlice`.
	pub(super) extra: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> RChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `width - 1` bits.
	pub fn remainder(&self) -> &'a BitSlice<O, T> {
		self.extra
	}
}

impl<'a, O, T> Iterator for RChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.width => {
				self.inner = BitSlice::empty();
				None
			},
			n => {
				let (rest, tail) = self.inner.split_at(n - self.width);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.inner.len();
		let (end, ovf) = self.width.overflowing_mul(n);
		if end >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = unsafe { self.inner.get_unchecked(len - end ..) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for RChunksExact<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.inner.len() {
			n if n < self.width => {
				self.inner = BitSlice::empty();
				None
			},
			_ => {
				let (head, rest) = self.inner.split_at(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for RChunksExact<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for RChunksExact<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) mutable chunks (`width` bits
at a time), starting at the end of the slice.

When the slice len is not evenly divided by the chunk size, the last up to
`width - 1` bits will be omitted but can be retrieved from the
[`into_remainder`] function from the iterator.

This struct is created by the [`rchunks_exact_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`into_remainder`]: #method.into_remainder
[`rchunks_exact_mut`]: struct.BitSlice.html#rchunks_exact_mut
**/
#[derive(Debug)]
pub struct RChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
	/// Remainder of the original BitSlice`.
	pub(super) extra: &'a mut BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> RChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Returns the remainder of the original slice that is not going to be
	/// returned by the iterator. The returned slice has at most
	/// `width - 1` bits.
	pub fn into_remainder(self) -> &'a mut BitSlice<O, T> {
		self.extra
	}
}

impl<'a, O, T> Iterator for RChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.width => None,
			n => {
				let (rest, tail) = slice.split_at_mut(n - self.width);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let len = slice.len();
		let (end, ovf) = self.width.overflowing_mul(n);
		if end >= len || ovf {
			return None;
		}
		self.inner = unsafe { slice.get_unchecked_mut(.. len - end) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for RChunksExactMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			n if n < self.width => None,
			_ => {
				let (head, rest) = slice.split_at_mut(self.width);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for RChunksExactMut<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for RChunksExactMut<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An iterator over a slice in (non-overlapping) mutable chunks (`width` bits
at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`rchunks_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rchunks_mut`]: struct.BitSlice.html#method.rchunks_mut
**/
#[derive(Debug)]
pub struct RChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
	/// The width of the produced chunks.
	pub(super) width: usize,
}

impl<'a, O, T> Iterator for RChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			len => {
				let mid = cmp::min(len, self.width);
				let (rest, tail) = slice.split_at_mut(len - mid);
				self.inner = rest;
				Some(tail)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.inner.len() {
			0 => (0, Some(0)),
			n => {
				let (len, rem) = (n / self.width, n % self.width);
				let len = len + (rem > 0) as usize;
				(len, Some(len))
			},
		}
	}

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let len = slice.len();
		let (end, ovf) = self.width.overflowing_mul(n);
		if end >= len || ovf {
			return None;
		}
		self.inner = unsafe { slice.get_unchecked_mut(.. len - end) };
		self.next()
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for RChunksMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::replace(&mut self.inner, BitSlice::empty_mut());
		match slice.len() {
			0 => None,
			n => {
				let rem = n % self.width;
				let len = if rem == 0 { self.width } else { rem };
				let (head, rest) = slice.split_at_mut(len);
				self.inner = rest;
				Some(head)
			},
		}
	}
}

impl<O, T> ExactSizeIterator for RChunksMut<'_, O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> FusedIterator for RChunksMut<'_, O, T>
where O: BitOrder, T: BitStore {}

/** An internal abstraction over the splitting iterators, so that
`{,r}splitn{,_mut}` can have a single implementation.
**/
#[doc(hidden)]
pub(super) trait SplitIter: DoubleEndedIterator {
	/// Marks the underlying iterator as complete, extracting the remaining
	/// portion of the slice.
	fn finish(&mut self) -> Option<Self::Item>;
}

/** An iterator over subslices separated by bits that satisfy a predicate
function.

This struct is created by the [`split`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`split`]: struct.BitSlice.html#method.split
**/
#[derive(Clone)]
pub struct Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// The offset from the original slice to the current `inner`. If `None`,
	/// the split is done operating.
	pub(super) place: Option<usize>,
	/// The testing function.
	pub(super) func: F,
}

impl<'a, O, T, F> Debug for Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.debug_struct("Split")
			.field("inner", &self.inner)
			.field("place", &self.place)
			.finish()
	}
}

impl<'a, O, T, F> SplitIter for Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn finish(&mut self) -> Option<&'a BitSlice<O, T>> {
		self.place.take().map(|_| self.inner)
	}
}

impl<'a, O, T, F> Iterator for Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let place = self.place?;
		match self.inner
			.iter()
			.zip(place ..)
			.position(|(bit, idx)| (self.func)(place + idx, bit))
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let out = self.inner.get_unchecked(.. idx);
				self.inner = self.inner.get_unchecked(idx + 1 ..);
				self.place = Some(place + idx + 1);
				Some(out)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.place {
			None => (0, Some(0)),
			Some(_) => (1, Some(self.inner.len() + 1)),
		}
	}
}

impl<'a, O, T, F> DoubleEndedIterator for Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let place = self.place?;

		match self.inner
			.iter()
			.zip(place .. place + self.inner.len())
			.rposition(|(bit, idx)| (self.func)(place + idx, bit))
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let out = self.inner.get_unchecked(idx + 1 ..);
				self.inner = self.inner.get_unchecked(.. idx);
				Some(out)
			},
		}
	}
}

impl<'a, O, T, F> FusedIterator for Split<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}

/** An iterator over subslices separated by positions that satisfy a predicate
function.

This struct is created by the [`split_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`split_mut`]: struct.BitSlice.html#method.split_mut
**/
pub struct SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a mut BitSlice<O, T>,
	/// The offset from the original slice to the current `inner`. If `None`,
	/// the split is done operating.
	pub(super) place: Option<usize>,
	/// The testing function.
	pub(super) func: F,
}

impl<'a, O, T, F> Debug for SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("SplitMut")
			.field("inner", &self.inner)
			.field("place", &self.place)
			.finish()
	}
}

impl<'a, O, T, F> SplitIter for SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn finish(&mut self) -> Option<&'a mut BitSlice<O, T>> {
		self.place.take().map(|_| mem::replace(&mut self.inner, BitSlice::empty_mut()))
	}
}

impl<'a, O, T, F> Iterator for SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		let place = self.place?;
		match {
			let func = &mut self.func;
			self.inner
				.iter()
				.zip(place ..)
				.position(|(bit, idx)| (*func)(place + idx, bit))
		} {
			None => self.finish(),
			Some(idx) => unsafe {
				let (out, rest) = mem::replace(
					&mut self.inner,
					BitSlice::empty_mut(),
				).split_at_mut(idx);
				self.inner = rest.get_unchecked_mut(1 ..);
				self.place = Some(place + idx + 1);
				Some(out)
			},
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		match self.place {
			None => (0, Some(0)),
			Some(_) => (1, Some(self.inner.len() + 1)),
		}
	}
}

impl<'a, O, T, F> DoubleEndedIterator for SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let place = self.place?;

		match {
			let func = &mut self.func;
			self.inner
				.iter()
				.zip(place .. place + self.inner.len())
				.rposition(|(bit, idx)| (*func)(place + idx, bit))
		} {
			None => self.finish(),
			Some(idx) => unsafe {
				let (rest, out) = mem::replace(
					&mut self.inner,
					BitSlice::empty_mut(),
				).split_at_mut(idx);
				self.inner = rest;
				self.place = Some(place + idx + 1);
				Some(out.get_unchecked_mut(1 ..))
			},
		}
	}
}

impl<'a, O, T, F> FusedIterator for SplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}

/** An iterator over subslices separated by bits that satisfy a predicate
function, starting from the end of the slice.

This struct is created by the [`rsplit`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rsplit`]: struct.BitSlice.html#rsplit
**/
#[derive(Clone)]
pub struct RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// This delegates to `Split`, and switches `next` and `next_back`.
	pub(super) inner: Split<'a, O, T, F>,
}

impl<'a, O, T, F> Debug for RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.debug_struct("RSplit")
			.field("inner", &self.inner.inner)
			.field("place", &self.inner.place)
			.finish()
	}
}

impl<'a, O, T, F> SplitIter for RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn finish(&mut self) -> Option<Self::Item> {
		self.inner.finish()
	}
}

impl<'a, O, T, F> Iterator for RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next_back()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<'a, O, T, F> DoubleEndedIterator for RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<'a, O, T, F> FusedIterator for RSplit<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}

/** An iterator over subslices separated by bits that satisfy a predicate
function, starting from the end of the slice.

This struct is created by the [`rsplit_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rsplit_mut`]: struct.BitSlice.html#rsplit_mut
**/
pub struct RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// This delegates to `SplitMut`, and switches `next` and `next_back`.
	pub(super) inner: SplitMut<'a, O, T, F>,
}

impl<'a, O, T, F> Debug for RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.debug_struct("RSplitMut")
			.field("inner", &self.inner.inner)
			.field("place", &self.inner.place)
			.finish()
	}
}

impl<'a, O, T, F> SplitIter for RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn finish(&mut self) -> Option<Self::Item> {
		self.inner.finish()
	}
}

impl<'a, O, T, F> Iterator for RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	type Item = &'a mut BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next_back()
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.inner.size_hint()
	}
}

impl<'a, O, T, F> DoubleEndedIterator for RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<'a, O, T, F> FusedIterator for RSplitMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}

pub(super) struct GenericSplitN<I>
where I: SplitIter {
	/// Some splitting wrapper.
	pub(super) inner: I,
	/// The count of remaining splits that may occur.
	pub(super) count: usize,
}

impl<I> Iterator for GenericSplitN<I>
where I: SplitIter {
	type Item = I::Item;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		match self.count {
			0 => None,
			1 => { self.count = 0; self.inner.finish() },
			_ => { self.count -= 1; self.inner.next() },
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let (floor, ceil) = self.inner.size_hint();
		(floor, ceil.map(|c| cmp::min(self.count, c)))
	}
}

/** An iterator over subslices separated by positions that satisfy a predicate
function, limited to a given number of splits.

This struct is created by the [`splitn`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`splitn`]: struct.BitSlice.html#method.splitn
**/
pub struct SplitN<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The interior splitter.
	pub(super) inner: GenericSplitN<Split<'a, O, T, F>>,
}

impl<'a, O, T, F> Debug for SplitN<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("SplitN")
			.field("inner", &self.inner.inner)
			.field("count", &self.inner.count)
			.finish()
	}
}

/** An iterator over mutable subslices separated by positions that satisfy a
predicate function, limited to a given number of splits.

This struct is created by the [`splitn_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`splitn_mut`]: struct.BitSlice.html#method.splitn_mut
**/
pub struct SplitNMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The interior splitter.
	pub(super) inner: GenericSplitN<SplitMut<'a, O, T, F>>,
}

impl<'a, O, T, F> Debug for SplitNMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("SplitNMut")
			.field("inner", &self.inner.inner)
			.field("count", &self.inner.count)
			.finish()
	}
}

/** An iterator over subslices separated by positions that satisfy a predicate
function, limited to a given number of splits, starting from the end of the
slice.

This struct is created by the [`rsplitn`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rsplitn`]: struct.BitSlice.html#method.rsplitn
**/
pub struct RSplitN<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The interior splitter.
	pub(super) inner: GenericSplitN<RSplit<'a, O, T, F>>,
}

impl<'a, O, T, F> Debug for RSplitN<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("RSplitN")
			.field("inner", &self.inner.inner)
			.field("count", &self.inner.count)
			.finish()
	}
}

/** An iterator over mutable subslices separated by positions that satisfy a
predicate function, limited to a given number of splits, starting from the end
of the slice.

This struct is created by the [`rsplitn_mut`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`rsplitn_mut`]: struct.BitSlice.html#method.rsplitn_mut
**/
pub struct RSplitNMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	/// The interior splitter.
	pub(super) inner: GenericSplitN<RSplitMut<'a, O, T, F>>,
}

impl<'a, O, T, F> Debug for RSplitNMut<'a, O, T, F>
where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("RSplitNMut")
			.field("inner", &self.inner.inner)
			.field("count", &self.inner.count)
			.finish()
	}
}

macro_rules! forward_iterator {
	( $name:ident ) => {
		impl<'a, O, T, F> Iterator for $name <'a, O, T, F>
		where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
			type Item = &'a BitSlice<O, T>;

			#[inline]
			fn next(&mut self) -> Option<Self::Item> {
				self.inner.next()
			}

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				self.inner.size_hint()
			}
		}

		impl<'a, O, T, F> FusedIterator for $name <'a, O, T, F>
		where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}
	};

	( $name:ident mut ) => {
		impl<'a, O, T, F> Iterator for $name <'a, O, T, F>
		where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {
			type Item = &'a mut BitSlice<O, T>;

			#[inline]
			fn next(&mut self) -> Option<Self::Item> {
				self.inner.next()
			}

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				self.inner.size_hint()
			}
		}

		impl<'a, O, T, F> FusedIterator for $name <'a, O, T, F>
		where O: BitOrder, T: 'a + BitStore, F: FnMut(usize, &bool) -> bool {}
	};
}

forward_iterator!(SplitN);
forward_iterator!(RSplitN);
forward_iterator!(SplitNMut mut);
forward_iterator!(RSplitNMut mut);

/** An iterator over overlapping subslices of some width.

This struct is created by the [`windows`] method on [`BitSlice`]s.

[`BitSlice`]: struct.BitSlice.html
[`windows`]: struct.BitSlice.html#method.windows
**/
#[derive(Clone, Debug)]
pub struct Windows<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// The `BitSlice` undergoing iteration.
	pub(super) inner: &'a BitSlice<O, T>,
	/// The width of the produced windows.
	pub(super) width: usize,
}

impl<'a, O, T> Iterator for Windows<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	type Item = &'a BitSlice<O, T>;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			None
		}
		else {
			unsafe {
				let out = self.inner.get_unchecked(.. self.width);
				self.inner = self.inner.get_unchecked(1 ..);
			Some(out)
			}
		}
	}

	#[inline]
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

	#[inline]
	fn count(self) -> usize {
		self.len()
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = self.width.overflowing_add(n);
		if end > self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		unsafe {
			let out = self.inner.get_unchecked(n .. end);
			self.inner = self.inner.get_unchecked(n + 1 ..);
			Some(out)
		}
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, O, T> DoubleEndedIterator for Windows<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.inner.len();
		if !(1 .. self.width).contains(&len) {
			self.inner = BitSlice::empty();
			return None;
		}
		unsafe {
			let out = self.inner.get_unchecked(len - self.width ..);
			self.inner = self.inner.get_unchecked(.. len - 1);
			Some(out)
		}
	}
}

impl<'a, O, T> ExactSizeIterator for Windows<'a, O, T>
where O: BitOrder, T: 'a + BitStore {}

impl<'a, O, T> FusedIterator for Windows<'a, O, T>
where O: BitOrder, T: 'a + BitStore {}
