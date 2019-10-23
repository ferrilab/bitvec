/*! Reimplementation of the slice fundamental’s inherent method API.
!*/

use super::*;

use core::{
	ops::{
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
	},
};

/// Reimplementation of the `[T]` inherent-method API.
impl<C, T> BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Returns the number of bits in the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 0u8.bits::<Local>();
	/// assert_eq!(bits.len(), 8);
	/// ```
	pub fn len(&self) -> usize {
		self.bitptr().len()
	}

	/// Returns `true` if the slice has a length of 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 0u8.bits::<Local>();
	/// assert!(!bits.is_empty());
	///
	/// assert!(BitSlice::<Local, Word>::empty().is_empty())
	/// ```
	pub fn is_empty(&self) -> bool {
		self.bitptr().len() == 0
	}

	/// Returns the first bit of the slice, or `None` if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<LittleEndian>();
	/// assert_eq!(bits.first(), Some(&true));
	///
	/// assert!(BitSlice::<Local, Word>::empty().first().is_none());
	/// ```
	pub fn first(&self) -> Option<&bool> {
		if self.is_empty() {
			None
		}
		else {
			Some(&self[0])
		}
	}

	/// Returns a mutable pointer to the first bit of the slice, or `None` if it
	/// is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// if let Some(mut first) = bits.first_mut() {
	///     *first = true;
	/// }
	/// assert_eq!(data, 1u8);
	/// ```
	pub fn first_mut(&mut self) -> Option<BitGuard<C, T>> {
		if self.is_empty() {
			None
		}
		else {
			Some(self.at(0))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<LittleEndian>();
	/// if let Some((first, rest)) = bits.split_first() {
	///     assert_eq!(first, &true);
	///     assert_eq!(rest, &bits[1 ..]);
	/// }
	/// ```
	pub fn split_first(&self) -> Option<(&bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((&self[0], &self[1 ..]))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// if let Some((mut first, rest)) = bits.split_first_mut() {
	///     *first = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 7);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(BitGuard<C, T>, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			let (head, rest) = self.split_at_mut(1);
			Some((head.at(0), rest))
		}
	}

	/// Returns the last and all the rest of the bits of the slice, or `None` if
	/// it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<BigEndian>();
	/// if let Some((last, rest)) = bits.split_last() {
	///     assert_eq!(last, &true);
	///     assert_eq!(rest, &bits[.. 7]);
	/// }
	/// ```
	pub fn split_last(&self) -> Option<(&bool, &Self)> {
		match self.len() {
			0 => None,
			len => Some((&self[len - 1], &self[.. len - 1])),
		}
	}

	/// Returns the last and all the rest of the bits of the slice, or `None` if
	/// it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// if let Some((mut last, rest)) = bits.split_last_mut() {
	///     *last = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 128 | 64 | 1);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(BitGuard<C, T>, &mut Self)> {
		match self.len() {
			0 => None,
			len => {
				let (rest, tail) = self.split_at_mut(len - 1);
				Some((tail.at(0), rest))
			},
		}
	}

	/// Returns the last bit of the slice, or `None` if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<BigEndian>();
	/// assert_eq!(Some(&true), bits.last());
	/// assert!(BitSlice::<Local, Word>::empty().last().is_none());
	/// ```
	pub fn last(&self) -> Option<&bool> {
		match self.len() {
			0 => None,
			len => Some(&self[len - 1]),
		}
	}

	/// Returns a mutable pointer to the last bit in the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// if let Some(mut last) = bits.last_mut() {
	///     *last = true;
	/// }
	/// assert!(bits[7]);
	pub fn last_mut(&mut self) -> Option<BitGuard<C, T>> {
		match self.len() {
			0 => None,
			len => Some(self.at(len - 1)),
		}
	}

	/// Returns a reference to a bit or subslice depending on the type of
	/// `index`.
	///
	/// - If given a position, returns a reference to the bit at that position
	///   or `None` if out of bounds.
	/// - If given a range, returns the subslice corresponding to that range, or
	///   `None` if out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 1u8;
	/// let bits = data.bits::<LittleEndian>();
	/// assert_eq!(Some(&true), bits.get(0));
	/// assert!(bits.get(8).is_none());
	/// assert!(bits.get(1 ..).expect("in bounds").not_any());
	/// assert!(bits.get(.. 12).is_none());
	/// ```
	pub fn get<'a, I>(
		&'a self,
		index: I,
	) -> Option<<I as BitSliceIndex<'a, C, T>>::ImmutOutput>
	where I: BitSliceIndex<'a, C, T> {
		index.get(self)
	}

	/// Returns a mutable reference to a bit or subslice depending on the type
	/// of `index` (see [`get`]) or `None` if the index is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// if let Some(mut bit) = bits.get_mut(1) {
	///     *bit = true;
	/// }
	/// if let Some(bits) = bits.get_mut(5 .. 7) {
	///     bits.set_all(true);
	/// }
	/// assert_eq!(data, 64 | 32 | 2);
	/// ```
	///
	/// [`get`]: #method.get
	pub fn get_mut<'a, I>(
		&'a mut self,
		index: I,
	) -> Option<<I as BitSliceIndex<'a, C, T>>::MutOutput>
	where I: BitSliceIndex<'a, C, T> {
		index.get_mut(self)
	}

	/// Returns a reference to a bit or subslice, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get`].
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 4u8;
	/// let bits = data.bits::<LittleEndian>();
	/// unsafe {
	///     assert!(bits.get_unchecked(2));
	///     assert!(!bits.get_unchecked(1));
	/// }
	/// ```
	///
	/// [`get`]: #method.get
	pub unsafe fn get_unchecked<'a, I>(
		&'a self,
		index: I,
	) -> <I as BitSliceIndex<'a, C, T>>::ImmutOutput
	where I: BitSliceIndex<'a, C, T> {
		index.get_unchecked(self)
	}

	/// Returns a mutable reference to a bit or subslice, without doing bounds
	/// checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get_mut`].
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// unsafe {
	///     let mut bit = bits.get_unchecked_mut(0);
	///     *bit = true;
	///     drop(bit); // release the borrow immediately
	///     let bits = bits.get_unchecked_mut(6 ..);
	///     bits.set_all(true);
	/// }
	/// assert_eq!(data, 1 | 2 | 128);
	/// ```
	///
	/// [`get_mut`]: #method.get_mut
	pub unsafe fn get_unchecked_mut<'a, I>(
		&'a mut self,
		index: I,
	) -> <I as BitSliceIndex<'a, C, T>>::MutOutput
	where I: BitSliceIndex<'a, C, T> {
		index.get_unchecked_mut(self)
	}

	/// Returns a raw pointer to the slice’s buffer.
	///
	/// The caller must ensure that the slice outlives the pointer this function
	/// returns, or else it will end up pointing to garbage.
	///
	/// The caller must also ensure that the memory the pointer
	/// (non-transitively) points to is never written to (except inside an
	/// `UnsafeCell`) using this pointer or any pointer derived from it. If you
	/// need to mutate the contents of the buffer, use [`as_mut_ptr`].
	///
	/// Modifying the container referenced by this slice may cause its buffer to
	/// be reallocated, which would also make any pointers to it invalid.
	///
	/// # Notes
	///
	/// This pointer is always to the first `T` element in the backing storage,
	/// even if that element is only partially used by the `self` slice.
	/// Multiple separate `BitSlice` handles may produce the same pointer with
	/// this method.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = [0u8; 2];
	/// let bits = data.bits::<BigEndian>();
	/// let (head, rest) = bits.split_at(4);
	/// assert_eq!(head.as_ptr(), rest.as_ptr());
	/// ```
	///
	/// [`as_mut_ptr`]: #method.as_mut_ptr
	//  FIXME(myrrlyn, 2019-10-22): Blocked on issue #57563.
	pub /* const */ fn as_ptr(&self) -> *const T {
		self.bitptr().pointer().r()
	}

	/// Returns an unsafe mutable pointer to the slice’s buffer.
	///
	/// The caller must ensure thath the slice outlives the pointer this
	/// function returns, or else it will end up pointing to garbage.
	///
	/// Modifying the container referenced by this slice may couse its buffer to
	/// be reallocated, which would also make any pointers to it invalid.
	///
	/// # Notes
	///
	/// This pointer is always to the first `T` element in the backing storage,
	/// even if that element is only partially used by the `self` slice.
	/// Multiple separate `BitSlice` handles may produce the same pointer with
	/// this method.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = [0u8; 2];
	/// let bits = data.bits_mut::<BigEndian>();
	/// let (head, rest) = bits.split_at_mut(4);
	/// assert_eq!(head.as_mut_ptr(), rest.as_mut_ptr());
	/// unsafe { *head.as_mut_ptr() = 2; }
	/// assert!(rest[2]);
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		self.bitptr().pointer().w()
	}

	/// Swaps two bits in the slice.
	///
	/// # Arguments
	///
	/// - `a`: The index of the first bit
	/// - `b`: The index of the second bit
	///
	/// # Panics
	///
	/// Panics if `a` or `b` are out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 2u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// bits.swap(0, 1);
	/// assert_eq!(data, 1);
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) {
		let len = self.len();
		assert!(a < len, "Index {} out of bounds: {}", a, len);
		assert!(b < len, "Index {} out of bounds: {}", b, len);
		unsafe {
			let bit_a = *self.get_unchecked(a);
			let bit_b = *self.get_unchecked(b);
			self.set_unchecked(a, bit_b);
			self.set_unchecked(b, bit_a);
		}
	}

	/// Reverses the order of bits in the slice, in place.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let mut data = 0b1_1001100u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// bits[1 ..].reverse();
	/// assert_eq!(data, 0b1_0011001);
	/// ```
	pub fn reverse(&mut self) {
		/* This is better implemented as a recursive algorithm, but Rust doesn’t
		yet flatten recursive tail calls into a loop, so it is done manually
		here.
		*/
		let mut cur: &mut Self = self;
		loop {
			let len = cur.len();
			//  Terminate when only one or zero bits remain to switch.
			if len < 2 {
				return;
			}
			let back = len - 1;
			//  `swap` has two assertions, which can be skipped here.
			unsafe {
				let h = *cur.get_unchecked(0);
				let t = *cur.get_unchecked(back);
				cur.set_unchecked(0, t);
				cur.set_unchecked(back, h);
				cur = cur.get_unchecked_mut(1 .. back);
			}
		}
	}

	/// Returns an iterator over the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 3u8;
	/// let bits = data.bits::<LittleEndian>();
	/// let mut iter = bits[.. 4].iter();
	/// assert_eq!(iter.next(), Some(&true));
	/// assert_eq!(iter.next(), Some(&true));
	/// assert_eq!(iter.next(), Some(&false));
	/// assert_eq!(iter.next(), Some(&false));
	/// assert!(iter.next().is_none());
	/// ```
	pub fn iter(&self) -> super::Iter<C, T> {
		self.into_iter()
	}

	/// Returns an iterator that allows modifying each bit.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = &mut data.bits_mut::<LittleEndian>()[.. 2];
	/// for mut bit in bits.iter_mut() {
	///     *bit = true;
	/// }
	/// assert_eq!(data, 3);
	/// ```
	pub fn iter_mut(&mut self) -> super::IterMut<C, T> {
		self.into_iter()
	}

	/// Returns an iterator over all contiguous windows of width `width`.
	///
	/// The windows overlap. If the slice is shorter than `width`, the iterator
	/// returns no values.
	///
	/// # Panics
	///
	/// Panics if `width` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b100_010_01u8;
	/// let bits = data.bits::<BigEndian>();
	/// let mut iter = bits[.. 5].windows(3);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert_eq!(iter.next().unwrap(), &bits[1 .. 4]);
	/// assert_eq!(iter.next().unwrap(), &bits[2 .. 5]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// If the slice is shorter than `width`:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0u8;
	/// let bits = data.bits::<Local>();
	/// let mut iter = bits[.. 3].windows(4);
	/// assert!(iter.next().is_none());
	pub fn windows(&self, width: usize) -> super::Windows<C, T> {
		assert_ne!(width, 0, "Window width cannot be zero");
		super::Windows {
			inner: self,
			width,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the beginning of the slice.
	///
	/// The chunks are slices and do not overlap. If `chunk_size` does not
	/// divide the length of the slice, then the last chunk will not have length
	/// `chunk_size`.
	///
	/// See [`chunks_exact`] for a variant of this iterator that returns chunks
	/// of always exactly `chunk_size` elements, and [`rchunks`] for the same
	/// iterator but starting at the end of the slice.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b001_010_10u8;
	/// let bits = data.bits::<BigEndian>();
	/// let mut iter = bits.chunks(3);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert_eq!(iter.next().unwrap(), &bits[3 .. 6]);
	/// assert_eq!(iter.next().unwrap(), &bits[6 .. 8]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// [`chunks_exact`]: #method.chunks_exact
	/// [`rchunks`]: #method.rchunks
	pub fn chunks(&self, chunk_size: usize) -> super::Chunks<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		super::Chunks {
			inner: self,
			chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the beginning of the slice.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does
	/// not divide the length of the slice, then the last chunk will not have
	/// length `chunk_size`.
	///
	/// See [`chunks_exact_mut`] for a variant of this iterator that returns
	/// chunks of always exactly `chunk_size` bits, and [`rchunks_mut`] for the
	/// same iterator but starting at the end of the slice.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// let mut count = 0;
	///
	/// for chunk in bits.chunks_mut(3) {
	///     chunk.store(4 >> count);
	///     count += 1;
	/// }
	/// assert_eq!(count, 3);
	/// assert_eq!(data, 0b100_010_01);
	/// ```
	///
	/// [`chunks_exact_mut`]: #method.chunks_exact_mut
	/// [`rchunks_mut`]: #method.rchunks_mut
	pub fn chunks_mut(&mut self, chunk_size: usize) -> super::ChunksMut<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		super::ChunksMut {
			inner: self,
			chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` elements of the slice at a time,
	/// starting at the beginning of the slice.
	///
	/// The chunks are slices and do not overlap. If `chunk_size` does not
	/// divide the length of the slice, then the last up to `chunk_size - 1`
	/// elements will be omitted and can be retrieved from the `remainder`
	/// function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can
	/// often optimize the resulting code better than in the case of [`chunks`].
	///
	/// See [`chunks`] for a variant of this iterator that also returns the
	/// remainder as a smaller chunk, and [`rchunks_exact`] for the same
	/// iterator but starting at the end of the slice.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b100_010_01u8;
	/// let bits = data.bits::<BigEndian>();
	/// let mut iter = bits.chunks_exact(3);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert_eq!(iter.next().unwrap(), &bits[3 .. 6]);
	/// assert!(iter.next().is_none());
	/// assert_eq!(iter.remainder(), &bits[6 .. 8]);
	/// ```
	///
	/// [`chunks`]: #method.chunks
	/// [`rchunks_exact`]: #method.rchunks_exact
	pub fn chunks_exact(&self, chunk_size: usize) -> super::ChunksExact<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let len = self.len();
		let rem = len % chunk_size;
		let mid = len - rem;
		let (inner, extra) = self.split_at(mid);
		super::ChunksExact {
			inner,
			extra,
			chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` elements of the slice at a time,
	/// starting at the beginning of the slice.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does
	/// not divide the length of the slice, then the last up to `chunk_size - 1`
	/// elements will be omitted and can be retrieved from the `into_remainder`
	/// function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` elements, the compiler can
	/// often optimize the resulting code better than in the case of
	/// [`chunks_mut`].
	///
	/// See [`chunks_mut`] for a variant of this iterator that also returns the
	/// remainder as a smaller chunk, and [`rchunks_exact_mut`] for the same
	/// iterator but starting at the end of the slice of the slice.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// let mut count = 0;
	///
	/// let mut iter = bits.chunks_exact_mut(3);
	/// for chunk in &mut iter {
	///     chunk.store(4 >> count);
	///     count += 1;
	/// }
	/// iter.into_remainder().store(1);
	/// assert_eq!(count, 2);
	/// assert_eq!(data, 0b100_010_01);
	/// ```
	///
	/// [`chunks_mut`]: #method.chunks_mut
	/// [`rchunks_exact_mut`]: #method.rchunks_exact_mut
	pub fn chunks_exact_mut(&mut self, chunk_size: usize) -> super::ChunksExactMut<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let len = self.len();
		let rem = len % chunk_size;
		let mid = len - rem;
		let (inner, extra) = self.split_at_mut(mid);
		super::ChunksExactMut {
			inner,
			extra,
			chunk_size,
		}
	}

	pub fn rchunks(&self, chunk_size: usize) -> super::RChunks<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		RChunks {
			inner: self,
			chunk_size,
		}
	}

	pub fn rchunks_mut(&mut self, chunk_size: usize) -> super::RChunksMut<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		RChunksMut {
			inner: self,
			chunk_size,
		}
	}

	pub fn rchunks_exact(&mut self, chunk_size: usize) -> super::RChunksExact<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let (extra, inner) = self.split_at(self.len() % chunk_size);
		RChunksExact {
			inner,
			extra,
			chunk_size,
		}
	}

	pub fn rchunks_exact_mut(&mut self, chunk_size: usize) -> super::RChunksExactMut<C, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let (extra, inner) = self.split_at_mut(self.len() % chunk_size);
		RChunksExactMut {
			inner,
			extra,
			chunk_size,
		}
	}
}

/** Replacement for [`core::slice::SliceIndex`].

This trait is stabilized in definition and `type Output` only, but all methods
are unstable. This makes it unusable in non-`libstd` slice libraries, and so it
must be duplicated here.

There is no tracking issue for `feature(slice_index_methods)`.

[`core::slice::SliceIndex`]: https://doc.rust-lang.org/stable/core/slice/trait.SliceIndex.html
**/
pub trait BitSliceIndex<'a, C, T>
where C: 'a + Cursor, T: 'a + BitStore {
	/// Immutable output type.
	type ImmutOutput;

	/// Mutable output type. This is necessary because `&mut BitSlice` is
	/// producible for range indices, but `&mut bool` is not producable for
	/// `usize` indices.
	type MutOutput;

	/// Returns a shared reference to the output at this location, if in bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output, if `self` is in bounds; otherwise `None`.
	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput>;

	/// Returns a mutable reference to the output at this location, if in
	/// bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output, if `self` is in bounds; otherwise `None`.
	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput>;

	/// Returns a shared reference to the output at this location, without
	/// performing any bounds checking.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output.
	unsafe fn get_unchecked(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput;

	/// Returns a mutable reference to the output at this location, without
	/// performing any bounds checking.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output.
	unsafe fn get_unchecked_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput;

	/// Returns a shared reference to the output at this location, panicking if
	/// out of bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output.
	///
	/// # Panics
	///
	/// This panics if `self` is out of bounds of `slice`.
	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput;

	/// Returns a mutable reference to the output at this location, panicking if
	/// out of bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output.
	///
	/// # Panics
	///
	/// This panics if `self` is out of bounds of `slice`.
	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput;
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for usize
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a bool;
	type MutOutput = BitGuard<'a, C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		if self >= slice.len() {
			None
		}
		else {
			Some(unsafe { self.get_unchecked(slice) })
		}
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		if self < slice.len() {
			Some(slice.at(self))
		}
		else {
			None
		}
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		let bitptr = slice.bitptr();
		let (elt, bit) = bitptr.head().offset(self as isize);
		let data_ptr = bitptr.pointer().a();

		if (&*data_ptr.offset(elt)).get::<C>(bit) {
			&true
		}
		else {
			&false
		}
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		slice.at_unchecked(self)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		match self.get(slice) {
			None => panic!("Index {} out of bounds: {}", self, slice.len()),
			Some(out) => out,
		}
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		slice.at(self)
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for Range<usize>
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		let Range { start, end } = self;
		let len = slice.len();
		if start > len || end > len || start > end {
			return None;
		}

		Some(unsafe { self.get_unchecked(slice) })
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		self.get(slice).map(|s| s.bitptr().into_bitslice_mut::<C>())
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		let Range { start, end } = self;
		let (data, head, _) = slice.bitptr().raw_parts();

		let (skip, new_head) = head.offset(start as isize);
		let new_bits = end - start;

		BitPtr::new_unchecked(
			data.r().offset(skip),
			new_head,
			new_bits,
		).into_bitslice::<C>()
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		self.get_unchecked(slice).bitptr().into_bitslice_mut::<C>()
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		match self.clone().get(slice) {
			None => panic!("Range {:?} exceeds length {}", self, slice.len()),
			Some(out) => out,
		}
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		self.index(slice).bitptr().into_bitslice_mut::<C>()
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeInclusive<usize>
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		(*self.start() .. *self.end() + 1).get(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		(*self.start() .. *self.end() + 1).get_mut(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		(*self.start() .. *self.end() + 1).get_unchecked(slice)
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		(*self.start() .. *self.end() + 1).get_unchecked_mut(slice)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		(*self.start() .. *self.end() + 1).index(slice)
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		(*self.start() .. *self.end() + 1).index_mut(slice)
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeFrom<usize>
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		(self.start .. slice.len()).get(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		(self.start .. slice.len()).get_mut(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		(self.start .. slice.len()).get_unchecked(slice)
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		(self.start .. slice.len()).get_unchecked_mut(slice)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		(self.start .. slice.len()).index(slice)
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		(self.start .. slice.len()).index_mut(slice)
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeFull
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		Some(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		Some(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		slice
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		slice
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		slice
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		slice
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeTo<usize>
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		(0 .. self.end).get(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		(0 .. self.end).get_mut(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		(0 .. self.end).get_unchecked(slice)
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		(0 .. self.end).get_unchecked_mut(slice)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		(0 .. self.end).index(slice)
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		(0 .. self.end).index_mut(slice)
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeToInclusive<usize>
where C: 'a + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		(0 .. self.end + 1).get(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		(0 .. self.end + 1).get_mut(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		(0 .. self.end + 1).get_unchecked(slice)
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		(0 .. self.end + 1).get_unchecked_mut(slice)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		(0 .. self.end + 1).index(slice)
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		(0 .. self.end + 1).index_mut(slice)
	}
}
