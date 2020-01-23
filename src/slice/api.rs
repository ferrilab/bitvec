/*! Reïmplementation of the `[T]` API.

This module tracks the [`slice`] primitive and [`core::slice`] module in the
version of Rust specified in the `rust-toolchain` file. It is required to
provide an exact or equivalent API surface matching the `Box<[T]>` type, to the
extent that it is possible in the language. Where differences occur, they must
be documented in a section called `API Differences`.

[`core::slice`]: https://doc.rust-lang.org/core/slice
[`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
!*/

use crate::{
	access::BitAccess,
	indices::BitIdx,
	order::BitOrder,
	pointer::BitPtr,
	slice::{
		BitSlice,
		iter::{
			Chunks,
			ChunksExact,
			ChunksExactMut,
			ChunksMut,
			GenericSplitN,
			Iter,
			IterMut,
			RChunks,
			RChunksExact,
			RChunksExactMut,
			RChunksMut,
			RSplit,
			RSplitMut,
			RSplitN,
			RSplitNMut,
			Split,
			SplitMut,
			SplitN,
			SplitNMut,
			Windows,
		},
		proxy::BitMut,
	},
	store::BitStore,
};

use core::{
	cmp,
	marker::PhantomData,
	ops::{
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
	},
	ptr::NonNull,
	slice,
};

#[cfg(feature = "alloc")]
use crate::vec::BitVec;

/** Forms a `BitSlice` from a pointer, starting position, and length.

The `head` argument is the starting *index*, not the starting *bit position*.
The `bits` argumnent is the number of **bits**, not the number of elements `T`.

This function is the semantic equivalent to `[T]::from_raw_parts`, in contrast
to [`from_raw_parts`] which is the API equivalent.

# Safety

This function is unsafe as there is no guarantee that the given pointer is valid
for the elements required to hold `head + bits` bits, nor whether the lifetime
inferred is a suitable lifetime for the returned slice.

`data` must be non-null and aligned, even for zero-length slices. This is due to
requirements in the `bitvec` data structure operations. You can obtain a pointer
that is usable as `data` for zero-length slices from [`NonNull::dangling()`].

The total size of the bit slice must be no larger than `BitPtr::<T>::MAX_BITS`
**bits** in memory. See the safety documentation of `BitPtr` (if available).

# Caveat

The lifetime for the returned slice is inferred from its usage. To prevent
accidental misuse, it’s suggested to tie the lifetime to whichever source
lifetime is safe in the context, such as by providing a helper function taking
the lifetime of a host value for the slice, or by explicit annotation.

# Examples

```rust
use bitvec::{
    indices::BitIdx,
    order::Local,
    slice,
    slice::BitSlice,
};

// manifest a slice for a single element
let x = 42u8;
let ptr = &x as *const u8;
let bits: &BitSlice<Local, u8> = unsafe { slice::bits_from_raw_parts(
    ptr,
    BitIdx::new(2).unwrap(),
    5
) };
assert_eq!(bits.len(), 5);
```

[`from_raw_parts`]: #fn.from_raw_parts
**/
pub unsafe fn bits_from_raw_parts<'a, O, T>(
	data: *const T,
	head: BitIdx<T>,
	bits: usize,
) -> &'a BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	BitPtr::new(data, head, bits).into_bitslice()
}

/** Performs the same functionality as [`bits_from_raw_parts`], except that a
mutable slice is returned.

This function is unsafe for the same reasons as [`bits_from_raw_parts`], as well
as not being able to provide a non-aliasing guarantee of the returned mutable
slice. `data` must be non-null and aligned even for zero-length slices as with
[`bits_from_raw_parts`]. The total size of the slice must be no larger than
`BitPtr::<T>::MAX_ELTS` **elements** `T` in memory.

See the documentation of [`bits_from_raw_parts`] for more details.

# Safety

Beyond the ordinary Rust requirements for aliasing, this function *also*
requires that the described region, when combined with the `O` [`BitOrder`]
type parameter, not cause aliasing with another `BitSlice` whose head and `O`
arguments cause aliasing in the underlying memory positions.

[`BitOrder`]: ../order/trait.BitOrder.html
[`bits_from_raw_parts`]: #fn.bits_from_raw_parts
**/
pub unsafe fn bits_from_raw_parts_mut<'a, O, T>(
	data: *mut T,
	head: BitIdx<T>,
	bits: usize,
) -> &'a mut BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	BitPtr::new(data, head, bits).into_bitslice_mut()
}

/** Converts a reference to `T` into a `BitSlice` of that element (without
copying).

# Original

[`core::slice::from_mut`](https://doc.rust-lang.org/core/slice/fn.from_mut.html)
**/
pub fn from_mut<O, T>(elt: &mut T) -> &mut BitSlice<O, T>
where O: BitOrder, T: BitStore {
	BitSlice::from_element_mut(elt)
}

/** Forms a bit slice from a pointer and a length.

The `len` argument is the number of **elements**, not the number of bits.

# Safety

This function is unsafe as there is no guarantee that the given pointer is valid
for `len` elements, nor whether the lifetime inferred is a suitable lifetime for
the returned slice.

`data` must be non-null and aligned, even for zero-length slices. This is due to
requirements in the `bitvec` data structure operations. You can obtain a pointer
that is usable as `data` for zero-length slices from [`NonNull::dangling()`].

The total size of the bit slice must be no larger than `BitPtr::<T>::MAX_BITS`
**bits** in memory. See the safety documentation of `BitPtr` (if available).

# Caveat

The lifetime for the returned slice is inferred from its usage. To prevent
accidental misuse, it’s suggested to tie the lifetime to whichever source
lifetime is safe in the context, such as by providing a helper function taking
the lifetime of a host value for the slice, or by explicit annotation.

# Original

[`core::slice::from_raw_parts`](https://doc.rust-lang.org/core/slice/fn.from_raw_parts.html)

# Examples

```rust
# use bitvec::prelude::*;
use bitvec::slice as bitslice;

//  manifest a slice for a single element
let x = 42u8; // 0b0010_1010
let ptr = &x as *const _;
let bitslice = unsafe { bitslice::from_raw_parts::<Msb0, _>(ptr, 1) };
assert!(bitslice[2]);
```
**/
pub unsafe fn from_raw_parts<'a, O, T>(
	data: *const T,
	len: usize,
) -> &'a BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	BitSlice::from_slice(slice::from_raw_parts(data, len))
}

/** Performs the same functionality as [`from_raw_parts`], except that a mutable
slice is returned.

This function is unsafe for the same reason as [`from_raw_parts`], as well as
not being able to provide a non-aliasing guarantee of the returned mutable
slice. `data` must be non-null and aligned even for zero-length slices as with
[`from_raw_parts`]. The total size of the slice must be no larger than
`BitPtr::<T>::MAX_ELTS` **elements** in memory.

See the documentation of [`from_raw_parts`] for more details.

# Safety

See `from_raw_parts`.

# Original

[`core::slice::from_raw_parts_mut`](https://doc.rust-lang.org/core/slice/fn.from_raw_parts_mut.html)

[`from_raw_parts`]: #fn.from_raw_parts
**/
pub unsafe fn from_raw_parts_mut<'a, O, T>(
	data: *mut T,
	len: usize,
) -> &'a mut BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
	BitSlice::from_slice_mut(slice::from_raw_parts_mut(data, len))
}

/** Converts a reference to `T` into a bit slice one element long (without
copying).

# Original

[`core::slice::from_ref`](https://doc.rust-lang.org/core/slice/fn.from_ref.html)
**/
pub fn from_ref<O, T>(elt: &T) -> &BitSlice<O, T>
where O: BitOrder, T: BitStore {
	BitSlice::from_element(elt)
}

/// Reimplementation of the `[T]` inherent-method API.
impl<O, T> BitSlice<O, T>
where O: BitOrder, T: BitStore {
	/// Returns the number of bits in the slice.
	///
	/// # Original
	///
	/// [`slice::len`](https://doc.rust-lang.org/std/primitive.slice.html#method.len)
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
	/// # Original
	///
	/// [`slice::is_empty`](https://doc.rust-lang.org/std/primitive.slice.html#method.is_empty)
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 0u8.bits::<Local>();
	/// assert!(!bits.is_empty());
	///
	/// assert!(BitSlice::<Local, usize>::empty().is_empty())
	/// ```
	pub fn is_empty(&self) -> bool {
		self.bitptr().len() == 0
	}

	/// Returns the first bit of the slice, or `None` if it is empty.
	///
	/// # Original
	///
	/// [`slice::first`](https://doc.rust-lang.org/std/primitive.slice.html#method.first)
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<Lsb0>();
	/// assert_eq!(bits.first(), Some(&true));
	///
	/// assert!(BitSlice::<Local, usize>::empty().first().is_none());
	/// ```
	#[inline]
	pub fn first(&self) -> Option<&bool> {
		0.get(self)
	}

	/// Returns a mutable pointer to the first bit of the slice, or `None` if it
	/// is empty.
	///
	/// # Original
	///
	/// [`slice::first_mut`](https://doc.rust-lang.org/std/primitive.slice.html#method.first_mut)
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Lsb0>();
	/// if let Some(mut first) = bits.first_mut() {
	///     *first = true;
	/// }
	/// assert_eq!(data, 1u8);
	/// ```
	#[inline]
	pub fn first_mut(&mut self) -> Option<BitMut<O, T>> {
		0.get_mut(self)
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<Lsb0>();
	/// if let Some((first, rest)) = bits.split_first() {
	///     assert_eq!(first, &true);
	///     assert_eq!(rest, &bits[1 ..]);
	/// }
	/// ```
	#[inline]
	pub fn split_first(&self) -> Option<(&bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			let (head, rest) = self.split_at(1);
			unsafe { Some((0.get_unchecked(head), rest)) }
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
	/// let bits = data.bits_mut::<Lsb0>();
	/// if let Some((mut first, rest)) = bits.split_first_mut() {
	///     *first = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 7);
	/// ```
	#[inline]
	pub fn split_first_mut(&mut self) -> Option<(BitMut<O, T>, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			let (head, rest) = self.split_at_mut(1);
			Some((unsafe { 0.get_unchecked_mut(head) }, rest))
		}
	}

	/// Returns the last and all the rest of the bits of the slice, or `None` if
	/// it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<Msb0>();
	/// if let Some((last, rest)) = bits.split_last() {
	///     assert_eq!(last, &true);
	///     assert_eq!(rest, &bits[.. 7]);
	/// }
	/// ```
	#[inline]
	pub fn split_last(&self) -> Option<(&bool, &Self)> {
		match self.len() {
			0 => None,
			len => {
				let (rest, tail) = self.split_at(len - 1);
				Some((unsafe { 0.get_unchecked(tail) }, rest))
			},
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
	/// let bits = data.bits_mut::<Msb0>();
	/// if let Some((mut last, rest)) = bits.split_last_mut() {
	///     *last = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 128 | 64 | 1);
	/// ```
	#[inline]
	pub fn split_last_mut(&mut self) -> Option<(BitMut<O, T>, &mut Self)> {
		match self.len() {
			0 => None,
			len => {
				let (rest, tail) = self.split_at_mut(len - 1);
				Some((unsafe { 0.get_unchecked_mut(tail) }, rest))
			},
		}
	}

	/// Returns the last bit of the slice, or `None` if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<Msb0>();
	/// assert_eq!(Some(&true), bits.last());
	/// assert!(BitSlice::<Local, usize>::empty().last().is_none());
	/// ```
	#[inline]
	pub fn last(&self) -> Option<&bool> {
		match self.len() {
			0 => None,
			len => Some(unsafe { (len - 1).get_unchecked(self) }),
		}
	}

	/// Returns a mutable pointer to the last bit in the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// if let Some(mut last) = bits.last_mut() {
	///     *last = true;
	/// }
	/// assert!(bits[7]);
	#[inline]
	pub fn last_mut(&mut self) -> Option<BitMut<O, T>> {
		match self.len() {
			0 => None,
			len => Some(unsafe { (len - 1).get_unchecked_mut(self) }),
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
	/// let bits = data.bits::<Lsb0>();
	/// assert_eq!(Some(&true), bits.get(0));
	/// assert!(bits.get(8).is_none());
	/// assert!(bits.get(1 ..).expect("in bounds").not_any());
	/// assert!(bits.get(.. 12).is_none());
	/// ```
	#[inline]
	pub fn get<'a, I>(&'a self, index: I) -> Option<I::Immut>
	where I: BitSliceIndex<'a, O, T> {
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
	/// let bits = data.bits_mut::<Lsb0>();
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
	#[inline]
	pub fn get_mut<'a, I>(&'a mut self, index: I) -> Option<I::Mut>
	where I: BitSliceIndex<'a, O, T> {
		index.get_mut(self)
	}

	/// Returns a reference to a bit or subslice, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get`].
	///
	/// # Safety
	///
	/// As this function does not perform boundary checking, the caller must
	/// ensure that `self` is an index within the boundaries of `slice` before
	/// calling in order to avoid boundary escapes and ensuing safety
	/// violations.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 4u8;
	/// let bits = data.bits::<Lsb0>();
	/// unsafe {
	///     assert!(bits.get_unchecked(2));
	///     assert!(!bits.get_unchecked(1));
	/// }
	/// ```
	///
	/// [`get`]: #method.get
	#[inline]
	pub unsafe fn get_unchecked<'a, I>(&'a self, index: I) -> I::Immut
	where I: BitSliceIndex<'a, O, T> {
		index.get_unchecked(self)
	}

	/// Returns a mutable reference to a bit or subslice, without doing bounds
	/// checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get_mut`].
	///
	/// # Safety
	///
	/// As this function does not perform boundary checking, the caller must
	/// ensure that `self` is an index within the boundaries of `slice` before
	/// calling in order to avoid boundary escapes and ensuing safety
	/// violations.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
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
	#[inline]
	pub unsafe fn get_unchecked_mut<'a, I>(&'a mut self, index: I) -> I::Mut
	where I: BitSliceIndex<'a, O, T> {
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
	/// let bits = data.bits::<Msb0>();
	/// let (head, rest) = bits.split_at(4);
	/// assert_eq!(head.as_ptr(), rest.as_ptr());
	/// ```
	///
	/// [`as_mut_ptr`]: #method.as_mut_ptr
	//  FIXME(myrrlyn, 2019-10-22): Blocked on issue #57563.
	#[inline]
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
	/// let bits = data.bits_mut::<Msb0>();
	/// let (head, rest) = bits.split_at_mut(4);
	/// assert_eq!(head.as_mut_ptr(), rest.as_mut_ptr());
	/// unsafe { *head.as_mut_ptr() = 2; }
	/// assert!(rest[2]);
	/// ```
	#[inline]
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
	/// let bits = data.bits_mut::<Lsb0>();
	/// bits.swap(0, 1);
	/// assert_eq!(data, 1);
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) {
		let len = self.len();
		assert!(a < len, "Index {} out of bounds: {}", a, len);
		assert!(b < len, "Index {} out of bounds: {}", b, len);
		unsafe { self.swap_unchecked(a, b); }
	}

	/// Reverses the order of bits in the slice, in place.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let mut data = 0b1_1001100u8;
	/// let bits = data.bits_mut::<Msb0>();
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
			unsafe {
				cur.swap_unchecked(0, back);
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
	/// let bits = data.bits::<Lsb0>();
	/// let mut iter = bits[.. 4].iter();
	/// assert_eq!(iter.next(), Some(&true));
	/// assert_eq!(iter.next(), Some(&true));
	/// assert_eq!(iter.next(), Some(&false));
	/// assert_eq!(iter.next(), Some(&false));
	/// assert!(iter.next().is_none());
	/// ```
	#[inline]
	pub fn iter(&self) -> Iter<O, T> {
		self.into_iter()
	}

	/// Returns an iterator that allows modifying each bit.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = &mut data.bits_mut::<Lsb0>()[.. 2];
	/// for mut bit in bits.iter_mut() {
	///     *bit = true;
	/// }
	/// assert_eq!(data, 3);
	/// ```
	#[inline]
	pub fn iter_mut(&mut self) -> IterMut<O, T> {
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
	/// let bits = data.bits::<Msb0>();
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
	pub fn windows(&self, width: usize) -> Windows<O, T> {
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
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.chunks(3);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert_eq!(iter.next().unwrap(), &bits[3 .. 6]);
	/// assert_eq!(iter.next().unwrap(), &bits[6 .. 8]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// [`chunks_exact`]: #method.chunks_exact
	/// [`rchunks`]: #method.rchunks
	pub fn chunks(&self, chunk_size: usize) -> Chunks<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		super::Chunks {
			inner: self,
			width: chunk_size,
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
	/// let bits = data.bits_mut::<Msb0>();
	/// let mut count = 0;
	///
	/// for chunk in bits.chunks_mut(3) {
	///     chunk.store(4u8 >> count);
	///     count += 1;
	/// }
	/// assert_eq!(count, 3);
	/// assert_eq!(data, 0b100_010_01);
	/// ```
	///
	/// [`chunks_exact_mut`]: #method.chunks_exact_mut
	/// [`rchunks_mut`]: #method.rchunks_mut
	pub fn chunks_mut(&mut self, chunk_size: usize) -> ChunksMut<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		super::ChunksMut {
			inner: self,
			width: chunk_size,
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
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.chunks_exact(3);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert_eq!(iter.next().unwrap(), &bits[3 .. 6]);
	/// assert!(iter.next().is_none());
	/// assert_eq!(iter.remainder(), &bits[6 .. 8]);
	/// ```
	///
	/// [`chunks`]: #method.chunks
	/// [`rchunks_exact`]: #method.rchunks_exact
	pub fn chunks_exact(&self, chunk_size: usize) -> ChunksExact<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let len = self.len();
		let rem = len % chunk_size;
		let mid = len - rem;
		let (inner, extra) = self.split_at(mid);
		super::ChunksExact {
			inner,
			extra,
			width: chunk_size,
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
	/// let bits = data.bits_mut::<Msb0>();
	/// let mut count = 0u8;
	///
	/// let mut iter = bits.chunks_exact_mut(3);
	/// for chunk in &mut iter {
	///     chunk.store(4u8 >> count);
	///     count += 1;
	/// }
	/// iter.into_remainder().store(1u8);
	/// assert_eq!(count, 2);
	/// assert_eq!(data, 0b100_010_01);
	/// ```
	///
	/// [`chunks_mut`]: #method.chunks_mut
	/// [`rchunks_exact_mut`]: #method.rchunks_exact_mut
	pub fn chunks_exact_mut(&mut self, chunk_size: usize) -> ChunksExactMut<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let len = self.len();
		let rem = len % chunk_size;
		let mid = len - rem;
		let (inner, extra) = self.split_at_mut(mid);
		super::ChunksExactMut {
			inner,
			extra,
			width: chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the end of the slice.
	///
	/// The chunks are slices and do not overlap. If `chunk_size` does not
	/// divide the length of the slice, then the last chunk will not have length
	/// of the slice, then the last chunk will not have length `chunk_size`.
	///
	/// See [`rchunks_exact`] for a variant of this iterator that returns chunks
	/// of always exactly `chunk_size` bits, and [`chunks`] for the same
	/// iterator but starting at the beginning of the slice.
	///
	/// # Panics
	///
	/// Panics if `chunk_size` is 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b01_010_100u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.rchunks(3);
	/// assert_eq!(iter.next().unwrap(), &bits[5 .. 8]);
	/// assert_eq!(iter.next().unwrap(), &bits[2 .. 5]);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 2]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// [`chunks`]: #method.chunks
	/// [`rchunks_exact`]: #method.rchunks_exact
	pub fn rchunks(&self, chunk_size: usize) -> RChunks<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		RChunks {
			inner: self,
			width: chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the end of the slice.
	///
	/// The chunks are mutable slices and do not overlap. If `chunk_size` does
	/// not divide the length of the slice, then the last chunk will not have
	/// length of the slice, then the last chunk will not have length
	/// `chunk_size`.
	///
	/// See [`rchunks_exact_mut`] for a variant of this iterator that returns
	/// chunks of always exactly `chunk_size` bits, and [`chunks_mut`] for the
	/// same iterator but starting at the beginning of the slice.
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
	/// let bits = data.bits_mut::<Lsb0>();
	/// let mut count = 0;
	///
	/// for chunk in bits.rchunks_mut(3) {
	///     chunk.store(4u8 >> count);
	///     count += 1;
	/// }
	/// assert_eq!(count, 3);
	/// assert_eq!(data, 0b100_010_01);
	/// ```
	///
	/// [`chunks_mut`]: #method.chunks_mut
	/// [`rchunks_exact_mut`]: #method.rchunks_exact_mut
	pub fn rchunks_mut(&mut self, chunk_size: usize) -> RChunksMut<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		RChunksMut {
			inner: self,
			width: chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the end of the slice.
	///
	/// The chunks are slices and do not overlap. If `chunk_size` does not
	/// divide the length of the slice, then the last up to `chunk_size - 1`
	/// bits will be omitted and can be retrieved from the `remainder` function
	/// of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` bits, the compiler can
	/// often optimize the resulting code better than in the case of [`chunks`].
	///
	/// See [`rchunks`] for a variant of this iterator that also returns the
	/// remainder as a smaller chunk, and [`chunks_exact`] for the same iterator
	/// but starting at the beginning of the slice.
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
	/// let bits = data.bits::<Lsb0>();
	/// let mut iter = bits.rchunks_exact(3);
	/// assert_eq!(iter.next().unwrap(), &bits[5 .. 8]);
	/// assert_eq!(iter.next().unwrap(), &bits[2 .. 5]);
	/// assert!(iter.next().is_none());
	/// assert_eq!(iter.remainder(), &bits[0 ..2]);
	/// ```
	///
	/// [`chunks`]: #method.chunks
	/// [`rchunks`]: #method.rchunks
	/// [`chunks_exact`]: #method.chunks_exact
	pub fn rchunks_exact(&self, chunk_size: usize) -> RChunksExact<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let (extra, inner) = self.split_at(self.len() % chunk_size);
		RChunksExact {
			inner,
			extra,
			width: chunk_size,
		}
	}

	/// Returns an iterator over `chunk_size` bits of the slice at a time,
	/// starting at the end of the slice.
	///
	/// The chunks are mutable slices, and do not overlap. If `chunk_size` does
	/// not divide the length of the slice, then the last up to `chunk_size - 1`
	/// bits will be omitted and can be retrieved from the `into_remainder`
	/// function of the iterator.
	///
	/// Due to each chunk having exactly `chunk_size` bits, the compiler can
	/// often optimize the resulting code better than in the case of
	/// [`chunks_mut`].
	///
	/// See [`rchunks_mut`] for a variant of this iterator that also returns the
	/// remainder as a smaller chunk, and [`chunks_exact_mut`] for the same
	/// iterator but starting at the beginning of the slice.
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
	/// let bits = data.bits_mut::<Lsb0>();
	/// let mut count = 0;
	/// let mut iter = bits.rchunks_exact_mut(3);
	///
	/// for chunk in &mut iter {
	///     chunk.store(4u8 >> count);
	///     count += 1;
	/// }
	/// iter.into_remainder().store(1u8);
	/// assert_eq!(data, 0b100_010_01);
	/// assert_eq!(count, 2);
	/// ```
	///
	/// [`chunks_mut`]: #method.chunks_mut
	/// [`rchunks_mut`]: #method.rchunks_mut
	/// [`chunks_exact_mut`]: #method.chunks_exact_mut
	pub fn rchunks_exact_mut(&mut self, chunk_size: usize) -> RChunksExactMut<O, T> {
		assert_ne!(chunk_size, 0, "Chunk width cannot be zero");
		let (extra, inner) = self.split_at_mut(self.len() % chunk_size);
		RChunksExactMut {
			inner,
			extra,
			width: chunk_size,
		}
	}

	/// Divides one slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Panics
	///
	/// Panics if `mid > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0x0Fu8;
	/// let bits = data.bits::<Msb0>();
	///
	/// {
	///     let (left, right) = bits.split_at(0);
	///     assert!(left.is_empty());
	///     assert_eq!(right, bits);
	/// }
	///
	/// {
	///     let (left, right) = bits.split_at(4);
	///     assert!(left.not_any());
	///     assert!(right.all());
	/// }
	///
	/// {
	///     let (left, right) = bits.split_at(8);
	///     assert_eq!(left, bits);
	///     assert!(right.is_empty());
	/// }
	/// ```
	pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
		let len = self.len();
		assert!(mid <= len, "Index {} out of bounds: {}", mid, len);
		unsafe { self.split_at_unchecked(mid) }
	}

	/// Divides one mutable slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Panics
	///
	/// Panics if `mid > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0x0Fu8;
	/// let bits = data.bits_mut::<Msb0>();
	///
	/// let (left, right) = bits.split_at_mut(4);
	/// assert!(left.not_any());
	/// assert!(right.all());
	/// *left.at(1) = true;
	/// *right.at(2) = false;
	///
	/// assert_eq!(data, 0b0100_1101);
	/// ```
	#[inline]
	pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
		let (head, tail) = self.split_at(mid);
		(head.bitptr().into_bitslice_mut(), tail.bitptr().into_bitslice_mut())
	}

	/// Returns an iterator over subslices separated by indexed bits that
	/// satisfy the predicate `func`tion. The matched position is not contained
	/// in the subslices.
	///
	/// # API Differences
	///
	/// The [`slice::split`] method takes a predicate function with signature
	/// `(&T) -> bool`, whereas this method’s predicate function has signature
	/// `(usize, &T) -> bool`. This difference is in place because `BitSlice` by
	/// definition has only one bit of information per slice item, and including
	/// the index allows the callback function to make more informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b01_001_000u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.split(|pos, bit| *bit);
	///
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 1]);
	/// assert_eq!(iter.next().unwrap(), &bits[2 .. 4]);
	/// assert_eq!(iter.next().unwrap(), &bits[5 .. 8]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// If the first position is matched, an empty slice will be the first item
	/// returned by the iterator. Similarly, if the last position in the slice
	/// is matched, an empty slice will be the last item returned by the
	/// iterator:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 1u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.split(|pos, bit| *bit);
	///
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 7]);
	/// assert_eq!(iter.next().unwrap(), BitSlice::<Local, usize>::empty());
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// If two matched positions are directly adjacent, an empty slice will be
	/// present between them.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b001_100_00u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.split(|pos, bit| *bit);
	///
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 2]);
	/// assert_eq!(iter.next().unwrap(), BitSlice::<Local, usize>::empty());
	/// assert_eq!(iter.next().unwrap(), &bits[4 .. 8]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// [`slice::split`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.split
	#[inline]
	pub fn split<F>(&self, func: F) -> Split<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		Split {
			inner: self,
			place: Some(0),
			func,
		}
	}

	/// Returns an iterator over mutable subslices separated by indexed bits
	/// that satisfy the predicate `func`tion. The matched position is not
	/// contained in the subslices.
	///
	/// # API Differences
	///
	/// The [`slice::split_mut`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0b001_000_10u8;
	/// let bits = data.bits_mut::<Msb0>();
	///
	/// for group in bits.split_mut(|pos, bit| *bit) {
	///     *group.at(0) = true;
	/// }
	/// assert_eq!(data, 0b101_1001_1u8);
	/// ```
	///
	/// [`slice::split_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.split_mut
	#[inline]
	pub fn split_mut<F>(&mut self, func: F) -> SplitMut<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		SplitMut {
			inner: self,
			place: Some(0),
			func,
		}
	}

	/// Returns an iterator over subslices separated by indexed bits that
	/// satisfy a predicate `func`tion, starting at the end of the slice and
	/// working backwards. The matched position is not contained in the
	/// subslices.
	///
	/// # API Differences
	///
	/// The [`slice::rsplit`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b0001_0000u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.rsplit(|pos, bit| *bit);
	///
	/// assert_eq!(iter.next().unwrap(), &bits[4 .. 8]);
	/// assert_eq!(iter.next().unwrap(), &bits[0 .. 3]);
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// As with `split()`, if the first or last position is matched, an empty
	/// slice will be the first (or last) item returned by the iterator.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b1001_0001u8;
	/// let bits = data.bits::<Msb0>();
	/// let mut iter = bits.rsplit(|pos, bit| *bit);
	/// assert!(iter.next().unwrap().is_empty());
	/// assert_eq!(iter.next().unwrap(), &bits[4 .. 7]);
	/// assert_eq!(iter.next().unwrap(), &bits[1 .. 3]);
	/// assert!(iter.next().unwrap().is_empty());
	/// assert!(iter.next().is_none());
	/// ```
	///
	/// [`slice::rsplit`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.rsplit
	#[inline]
	pub fn rsplit<F>(&self, func: F) -> RSplit<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		RSplit {
			inner: self.split(func),
		}
	}

	/// Returns an iterator over mutable subslices separated by indexed bits
	/// that satisfy a predicate `func`tion, starting at the end of the slice
	/// and working backwards. The matched position is not contained in the
	/// subslices.
	///
	/// # API Differences
	///
	/// The [`slice::rsplit_mut`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	///
	/// let mut count = 0u8;
	/// for group in bits.rsplit_mut(|pos, bit| pos % 3 == 2) {
	///     count += 1;
	///     group.store(count);
	/// }
	/// assert_eq!(data, 0b11_0_10_0_01);
	/// ```
	///
	/// [`slice::rsplit_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.rsplit_mut
	#[inline]
	pub fn rsplit_mut<F>(&mut self, func: F) -> RSplitMut<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		RSplitMut {
			inner: self.split_mut(func),
		}
	}

	/// Returns an iterator over subslices separated by indexed bits that
	/// satisfy the predicate `func`tion, limited to returning at most `n`
	/// items. The matched position is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the
	/// slice.
	///
	/// # API Differences
	///
	/// The [`slice::splitn`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// Print the slice split once by indices divisible by 3:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0xA5u8;
	/// let bits = data.bits::<Msb0>();
	///
	/// for group in bits.splitn(2, |pos, bit| pos % 3 == 2) {
	///     println!("{}", group);
	/// }
	/// //  [10]
	/// //  [00101]
	/// ```
	///
	/// [`slice::splitn`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.splitn
	#[inline]
	pub fn splitn<F>(&self, n: usize, func: F) -> SplitN<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		SplitN {
			inner: GenericSplitN {
				inner: self.split(func),
				count: n,
			}
		}
	}

	/// Returns an iterator over mutable subslices separated by indexed bits
	/// that satisfy the predicate `func`tion, limited to returning at most `n`
	/// items. The matched position is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the
	/// slice.
	///
	/// # API Differences
	///
	/// The [`slice::splitn_mut`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let mut counter = 0u8;
	///
	/// for group in bits.splitn_mut(2, |pos, bit| pos % 4 == 3) {
	///     counter += 1;
	///     group.store(counter);
	/// }
	/// assert_eq!(data, 0b001_0_0010);
	/// ```
	///
	/// [`slice::splitn_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.splitn_mut
	#[inline]
	pub fn splitn_mut<F>(&mut self, n: usize, func: F) -> SplitNMut<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		SplitNMut {
			inner: GenericSplitN {
				inner: self.split_mut(func),
				count: n,
			}
		}
	}

	/// Returns an iterator over subslices separated by indexed bits that
	/// satisfy a predicate `func`tion, limited to returning at most `n` items.
	/// This starts at the end of the slice and works backwards. The matched
	/// position is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the
	/// slice.
	///
	/// # API Differences
	///
	/// The [`slice::rsplitn`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// Print the slice split once, starting from the end, by indices divisible
	/// by 3:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0xA5u8;
	/// let bits = data.bits::<Msb0>();
	///
	/// for group in bits.rsplitn(2, |pos, bit| pos % 3 == 2) {
	///     println!("{}", group);
	/// }
	/// //  [01]
	/// //  [10100]
	/// ```
	///
	/// [`slice::rsplitn`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.rsplitn
	#[inline]
	pub fn rsplitn<F>(&self, n: usize, func: F) -> RSplitN<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		RSplitN {
			inner: GenericSplitN {
				inner: self.rsplit(func),
				count: n,
			}
		}
	}

	/// Returns an iterator over mutable subslices separated by indexed bits
	/// that satisfy a predicate `func`tion, limited to returning at most `n`
	/// items. This starts at the end of the slice and works backwards. The
	/// matched position is not contained in the subslices.
	///
	/// The last element returned, if any, will contain the remainder of the
	/// slice.
	///
	/// # API Differences
	///
	/// The [`slice::rsplitn_mut`] method takes a predicate function with
	/// signature `(&T) -> bool`, whereas this method’s predicate function has
	/// signature `(usize, &T) -> bool`. This difference is in place because
	/// `BitSlice` by definition has only one bit of information per slice item,
	/// and including the index allows the callback function to make more
	/// informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let mut counter = 0u8;
	///
	/// for group in bits.rsplitn_mut(2, |pos, bit| pos % 3 == 2) {
	///     counter += 1;
	///     group.store(counter);
	/// }
	/// assert_eq!(data, 0b00010_0_01);
	/// ```
	///
	/// [`slice::rsplitn_mut`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.rsplitn_mut
	#[inline]
	pub fn rsplitn_mut<F>(&mut self, n: usize, func: F) -> RSplitNMut<'_, O, T, F>
	where F: FnMut(usize, &bool) -> bool {
		RSplitNMut {
			inner: GenericSplitN {
				inner: self.rsplit_mut(func),
				count: n,
			}
		}
	}

	/// Returns `true` if the slice contains a region that matches the given
	/// span.
	///
	/// # API Differences
	///
	/// The [`slice::contains`] method tests for a single slice element.
	/// Because this is a slice of single bits, testing for the presence of one
	/// `bool` value is not very informative. This instead searches for a
	/// subslice, which may be one or more bits.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b0101_1010u8;
	/// let bits_be = data.bits::<Msb0>();
	/// let bits_le = data.bits::<Lsb0>();
	/// assert!(bits_be.contains(&bits_le[1 .. 5]));
	/// ```
	///
	/// This example uses a palindrome pattern to demonstrate that the query
	/// does not need to have the same type parameters as the searched slice.
	///
	/// [`slice::contains`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.contains
	pub fn contains<P, U>(&self, query: &BitSlice<P, U>) -> bool
	where P: BitOrder, U: BitStore {
		let len = query.len();
		if len > self.len() {
			return false;
		}
		self.windows(len).any(|s| s == query)
	}

	/// Returns `true` if `prefix` is a prefix of the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b0110_1110u8;
	/// let bits = data.bits::<Msb0>();
	/// assert!(bits.starts_with(&data.bits::<Lsb0>()[.. 2]));
	/// ```
	pub fn starts_with<P, U>(&self, prefix: &BitSlice<P, U>) -> bool
	where P: BitOrder, U: BitStore {
		let plen = prefix.len();
		self.len() >= plen && prefix == unsafe { self.get_unchecked(.. plen) }
	}

	/// Returns `true` if `suffix` is a suffix of the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = 0b0111_1010u8;
	/// let bits = data.bits::<Msb0>();
	/// assert!(bits.ends_with(&data.bits::<Lsb0>()[6 ..]));
	/// ```
	pub fn ends_with<P, U>(&self, suffix: &BitSlice<P, U>) -> bool
	where P: BitOrder, U: BitStore, {
		let slen = suffix.len();
		let len = self.len();
		len >= slen && suffix == unsafe { self.get_unchecked(len - slen ..) }
	}

	/// Rotates the slice in-place such that the first `by` bits of the slice
	/// move to the end while the last `self.len() - by` bits move to the
	/// front. After calling `rotate_left`, the bit previously at index `by`
	/// will become the first bit in the slice.
	///
	/// # Panics
	///
	/// This function will panic if `by` is greater than the length of the
	/// slice. Note that `by == self.len()` does *not* panic and is a noöp
	/// rotation.
	///
	/// # Complexity
	///
	/// Takes linear (in `self.len()`) time.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0xF0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits.rotate_left(2);
	/// assert_eq!(data, 0xC3);
	/// ```
	///
	/// Rotating a subslice:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0xF0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits[1 .. 5].rotate_left(1);
	/// assert_eq!(data, 0b1_1101_000);
	/// ```
	pub fn rotate_left(&mut self, mut by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == 0 || by == len {
			return;
		}

		/* Rotation can be accelerated by copying chunks out onto the stack,
		then moving each bit down by a longer distance. This block collects up
		to a single `usize`’s worth of bits from the start of the slice, then
		moves all remaining bits down by the collection amount, then writes the
		collected bits into the back of the slice. While this is does not affect
		the length-determined runtime cost, it does reduce the
		distance-determined cost by a factor of the target word width.
		*/
		let mut tmp = 0usize;
		let bits = BitSlice::<O, _>::from_element_mut(&mut tmp);

		while by > 0 {
			//  Clamp the collection count by the word size and shift distance.
			let shamt = cmp::min(usize::BITS as usize, by);
			//  Bounds checking is already performed. This block erases all
			//  interior checks in the iteration body.
			unsafe {
				//  Collect bits from the front of the slice into scratch.
				bits.get_unchecked_mut(.. shamt)
					.clone_from_slice(self.get_unchecked(.. shamt));
				//  Move all remaining bits down to the front of the slice.
				for (to, from) in (shamt .. len).enumerate() {
					self.copy_unchecked(from, to);
				}
				//  Emit the scratch bits into the back of the slice.
				self.get_unchecked_mut(len - shamt ..)
					.clone_from_slice(bits.get_unchecked(.. shamt));
			}
			by -= shamt;
		}
	}

	/// Rotates the slice in-place such that the first `self.len() - by` bits of
	/// the slice move to the end while the last `by` bits move to the front.
	/// After calling `rotate_right`, the bit previously at index
	/// `self.len() - by` will become the first bit in the slice.
	///
	/// # Panics
	///
	/// This function will panic if `by` is greater than the length of the
	/// slice. Note that `by == self.len()` does *not* panic and is a noöp
	/// rotation.
	///
	/// # Complexity
	///
	/// Takes linear (in `self.len()`) time.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0xF0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits.rotate_right(2);
	/// assert_eq!(data, 0x3C);
	/// ```
	///
	/// Rotate a subslice:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0xF0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits[1 .. 5].rotate_right(1);
	/// assert_eq!(data, 0b1_0111_000);
	/// ```
	pub fn rotate_right(&mut self, mut by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == 0 || by == len {
			return;
		}

		/* Rotation can be accelerated by copying chunks out onto the stack,
		then moving each bit down by a longer distance. This block collects up
		to a single `usize`’s worth of bits from the end of the slice, then
		moves all remaining bits up by the collection amount, then writes the
		collected bits into the front of the slice. While this is does not
		affect the length-determined runtime cost, it does reduce the
		distance-determined cost by a factor of the target word width.
		*/
		let mut tmp = 0usize;
		let bits = BitSlice::<O, _>::from_element_mut(&mut tmp);

		while by > 0 {
			//  Clamp the collection count by the word size and shift distance.
			let shamt = cmp::min(usize::BITS as usize, by);
			//  Bounds checking is already performed. This block erases all
			//  interior checks in the iteration body.
			unsafe {
				//  Collect bits from the back of the slice into scratch.
				bits.get_unchecked_mut(.. shamt)
					.clone_from_slice(self.get_unchecked(len - shamt ..));
				//  Move all remaining bits up to the back of the slice.
				for (from, to) in (shamt .. len).enumerate().rev() {
					self.copy_unchecked(from, to);
				}
				//  Emit the scratch bits into the front of the slice.
				self.get_unchecked_mut(.. shamt)
					.clone_from_slice(bits.get_unchecked(.. shamt));
			}
			by -= shamt;
		}
	}

	/// Copies the elements from `src` into `self`.
	///
	/// The length of `src` must be the same as `self`.
	///
	/// This is equivalent to `copy_from_slice`; this function is only included
	/// for API surface equivalence.
	///
	/// # Panics
	///
	/// This function will panic if the two slices have different lengths.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let src = 0x0Fu16.bits::<Lsb0>();
	/// bits.clone_from_slice(&src[.. 8]);
	/// assert_eq!(data, 0xF0);
	/// ```
	///
	/// Rust enforces that there can only be one mutable reference with no
	/// immutable references to a particular piece of data in a particular
	/// scope. Because of this, attempting to use `clone_from_slice` on a single
	/// slice will result in a compile failure:
	///
	/// ```rust,compile_fail
	/// # use bitvec::prelude::*;
	/// let mut data = 3u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits[.. 2].clone_from_slice(&bits[6 ..]);
	/// ```
	///
	/// To work around this, we can use [`split_at_mut`] to create two distinct
	/// sub-slices from a slice:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 3u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let (head, tail) = bits.split_at_mut(4);
	/// head.clone_from_slice(tail);
	/// assert_eq!(data, 0x33);
	/// ```
	pub fn clone_from_slice<P, U>(&mut self, src: &BitSlice<P, U>)
	where P: BitOrder, U: BitStore {
		assert_eq!(
			self.len(),
			src.len(),
			"Cloning from slice requires equal lengths",
		);
		for idx in 0 .. self.len() {
			unsafe {
				self.set_unchecked(idx, *src.get_unchecked(idx));
			}
		}
	}

	/// Copies the elements from `src` into `self`.
	///
	/// The length of `src` must be the same as `self`.
	///
	/// This is restricted to take exactly the same type of bit slice as the
	/// source slice, so that the implementation has the chace to use faster
	/// `memcpy` if possible.
	///
	/// # Panics
	///
	/// This function will panic if the two slices have different lengths.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let src = 0x0Fu8.bits::<Msb0>();
	/// bits.copy_from_slice(src);
	/// assert_eq!(data, 0x0F);
	/// ```
	///
	/// Rust enforces that there can only be one mutable reference with no
	/// immutable references to a particular piece of data in a particular
	/// scope. Because of this, attempting to use `copy_from_slice` on a single
	/// slice will result in a compile failure:
	///
	/// ```rust,compile_fail
	/// # use bitvec::prelude::*;
	/// let mut data = 3u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits[.. 2].copy_from_slice(&bits[6 ..]);
	/// ```
	///
	/// To work around this, we can use [`split_at_mut`] to create two distinct
	/// sub-slices from a slice:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 3u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// let (head, tail) = bits.split_at_mut(4);
	/// head.copy_from_slice(tail);
	/// assert_eq!(data, 0x33);
	/// ```
	pub fn copy_from_slice(&mut self, src: &Self) {
		self.clone_from_slice(src)
	}

	/// Swaps all bits in `self` with those in `other`.
	///
	/// The length of `other` must be the same as `self`.
	///
	/// # Panics
	///
	/// This function will panic if the two slices hav different lengths.
	///
	/// # Example
	///
	/// Swapping two elements across slices:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut a = 0u8;
	/// let mut b = 0x96A5u16;
	/// let bits_a = a.bits_mut::<Lsb0>();
	/// let bits_b = b.bits_mut::<Msb0>();
	///
	/// bits_a.swap_with_slice(&mut bits_b[4 .. 12]);
	///
	/// assert_eq!(a, 0x56);
	/// assert_eq!(b, 0x9005);
	/// ```
	///
	/// Rust enforces that there can only be one mutable reference to a
	/// particular piece of data in a particular scope. Because of this,
	/// attempting to use `swap_with_slice` on a single slice will result in a
	/// compile failure:
	///
	/// ```rust,compile_fail
	/// # use bitvec::prelude::*;
	/// let mut data = 15u8;
	/// let bits = data.bits_mut::<Msb0>();
	/// bits[.. 3].swap_with_slice(&mut bits[5 ..]);
	/// ```
	///
	/// To work around this, we can use [`split_at_mut`] to create two distinct
	/// mutable sub-slices from a slice:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 15u8;
	/// let bits = data.bits_mut::<Msb0>();
	///
	/// {
	///     let (left, right) = bits.split_at_mut(4);
	///     left[.. 2].swap_with_slice(&mut right[2 ..]);
	/// }
	///
	/// assert_eq!(data, 0xCC);
	/// ```
	pub fn swap_with_slice<P, U>(&mut self, other: &mut BitSlice<P, U>)
	where P: BitOrder, U: BitStore {
		assert_eq!(
			self.len(),
			other.len(),
			"Swapping between slices requires equal lengths",
		);
		self.iter_mut().zip(other.iter_mut()).for_each(|(mut this, mut that)| {
			let (a, b) = (*this, *that);
			*this = b;
			*that = a;
		})
	}

	/// Transmute the slice to a slice with a different backing store, ensuring
	/// alignment of the types is maintained.
	///
	/// This method splits the slice into three distinct slices: prefix,
	/// correctly aligned middle slice of a new backing type, and the suffix
	/// slice. The method does a best effort to make the middle slice the
	/// greatest length possible for a given type and input slice, but only your
	/// algorithm’s performance should depend on that, not its correctness.
	///
	/// # Safety
	///
	/// This method is essentially a `transmute` with respect to the elements in
	/// the returned middle slice, so all the usual caveats pertaining to
	/// `transmute::<T, U>` also apply here.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// unsafe {
	///     let bytes: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
	///     let bits = bytes.bits::<Local>();
	///     let (prefix, shorts, suffix) = bits.align_to::<u16>();
	///     match prefix.len() {
	///         0 => {
	///             assert_eq!(shorts, bits[.. 48]);
	///             assert_eq!(suffix, bits[48 ..]);
	///         },
	///         8 => {
	///             assert_eq!(prefix, bits[.. 8]);
	///             assert_eq!(shorts, bits[8 ..]);
	///         },
	///         _ => unreachable!("This case will not occur")
	///     }
	/// }
	/// ```
	pub unsafe fn align_to<U>(&self) -> (&Self, &BitSlice<O, U>, &Self)
	where U: BitStore {
		let bitptr = self.bitptr();
		let (l, c, r) = bitptr.as_slice().align_to::<U>();
		let l_start = *bitptr.head() as usize;
		let l = &Self::from_slice(l)[l_start ..];
		let c = BitSlice::from_slice(c);
		let r = &Self::from_slice(r)[.. bitptr.len() - l.len() - c.len()];
		(l, c, r)
	}

	/// Transmute the slice to a slice with a different backing store, ensuring
	/// alignment of the types is maintained.
	///
	/// This method splits the slice into three distinct slices: prefix,
	/// correctly aligned middle slice of a new backing type, and the suffix
	/// slice. The method does a best effort to make the middle slice the
	/// greatest length possible for a given type and input slice, but only your
	/// algorithm’s performance should depend on that, not its correctness.
	///
	/// # Safety
	///
	/// This method is essentially a `transmute` with respect to the elements in
	/// the returned middle slice, so all the usual caveats pertaining to
	/// `transmute::<T, U>` also apply here.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// unsafe {
	///     let mut bytes: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
	///     let bits = bytes.bits_mut::<Local>();
	///     let (prefix, shorts, suffix) = bits.align_to_mut::<u16>();
	///     //  same access and behavior as in `align_to`
	/// }
	/// ```
	#[inline]
	pub unsafe fn align_to_mut<U>(&mut self) -> (
		&mut Self,
		&mut BitSlice<O, U>,
		&mut Self,
	)
	where U: BitStore {
		let (l, c, r) = self.align_to::<U>();
		(
			l.bitptr().into_bitslice_mut(),
			c.bitptr().into_bitslice_mut(),
			r.bitptr().into_bitslice_mut(),
		)
	}

	/// Copies `self` into a new `BitVec`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let data = [0u8, !0u8];
	/// let bits = data.bits::<Local>();
	/// let vec = bits.to_vec();
	/// assert_eq!(bits, vec);
	/// ```
	#[cfg(feature = "alloc")]
	#[inline]
	pub fn to_vec(&self) -> BitVec<O, T> {
		BitVec::from_bitslice(self)
	}
}

/** Replacement for [`slice::SliceIndex`].

This trait is stabilized in definition and `type Output` only, but all methods
are unstable. This makes it unusable in non-`libstd` slice libraries, and so it
must be duplicated here.

There is no tracking issue for `feature(slice_index_methods)`.

[`slice::SliceIndex`]: https://doc.rust-lang.org/stable/core/slice/trait.SliceIndex.html
**/
pub trait BitSliceIndex<'a, O, T>
where O: 'a + BitOrder, T: 'a + BitStore {
	/// Immutable output type.
	type Immut;

	/// Mutable output type. This is necessary because `&mut BitSlice` is
	/// producible for range indices, but `&mut bool` is not producable for
	/// `usize` indices.
	type Mut;

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
	fn get(self, slice: &'a BitSlice<O, T>) -> Option<Self::Immut>;

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
	fn get_mut(self, slice: &'a mut BitSlice<O, T>) -> Option<Self::Mut>;

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
	///
	/// # Safety
	///
	/// As this function does not perform boundary checking, the caller must
	/// ensure that `self` is an index within the boundaries of `slice` before
	/// calling in order to avoid boundary escapes and ensuing safety
	/// violations.
	unsafe fn get_unchecked(self, slice: &'a BitSlice<O, T>) -> Self::Immut;

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
	///
	/// # Safety
	///
	/// As this function does not perform boundary checking, the caller must
	/// ensure that `self` is an index within the boundaries of `slice` before
	/// calling in order to avoid boundary escapes and ensuing safety
	/// violations.
	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<O, T>,
	) -> Self::Mut;

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
	fn index(self, slice: &'a BitSlice<O, T>) -> Self::Immut;

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
	fn index_mut(self, slice: &'a mut BitSlice<O, T>) -> Self::Mut;
}

impl<'a, O, T> BitSliceIndex<'a, O, T> for usize
where O: 'a + BitOrder, T: 'a + BitStore {
	type Immut = &'a bool;
	type Mut = BitMut<'a, O, T>;

	fn get(self, slice: &'a BitSlice<O, T>) -> Option<Self::Immut> {
		if self < slice.len() {
			Some(unsafe { self.get_unchecked(slice) })
		}
		else {
			None
		}
	}

	fn get_mut(self, slice: &'a mut BitSlice<O, T>) -> Option<Self::Mut> {
		if self < slice.len() {
			Some(unsafe { self.get_unchecked_mut(slice) })
		}
		else {
			None
		}
	}

	unsafe fn get_unchecked(self, slice: &'a BitSlice<O, T>) -> Self::Immut {
		let bitptr = slice.bitptr();
		let (elt, bit) = bitptr.head().offset(self as isize);
		let data_ptr = bitptr.pointer().a();

		if (&*data_ptr.offset(elt)).get::<O>(bit) {
			&true
		}
		else {
			&false
		}
	}

	#[inline]
	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<O, T>,
	) -> Self::Mut {
		let bp = slice.bitptr();
		let (offset, head) = bp.head().offset(self as isize);
		let ptr = bp.pointer().a().offset(offset);
		BitMut {
			_parent: PhantomData,
			data: NonNull::new_unchecked(ptr as *mut T::Access),
			head,
			bit: (*ptr).get::<O>(head)
		}
	}

	fn index(self, slice: &'a BitSlice<O, T>) -> Self::Immut {
		self.get(slice).unwrap_or_else(|| {
			panic!("Index {} out of bounds: {}", self, slice.len())
		})
	}

	fn index_mut(self, slice: &'a mut BitSlice<O, T>) -> Self::Mut {
		let len = slice.len();
		self.get_mut(slice).unwrap_or_else(|| {
			panic!("Index {} out of bounds: {}", self, len)
		})
	}
}

/// This macro allows each range implementation to have its own copy of the
/// trait methods, rather than reshaping the range to route through `Range` and
/// deepen the call AST.
///
/// Only `get` and `get_unchecked` are interesting; the other four methods can
/// all be implemented in terms of these two.
///
/// This macro can be invoked either with definition bodies for `get` and
/// `get_unchecked`, or with a range transform. The latter is useful for
/// converting inclusive ranges to exclusive; the former allows different range
/// shape to perform only the work that they actually need.
macro_rules! range_impl {
	( $( $r:ty => get $get:expr, unchecked $unchecked:expr; )* ) => { $(
		impl<'a, O, T> BitSliceIndex<'a, O, T> for $r
		where O: 'a + BitOrder, T: 'a + BitStore {
			type Immut = &'a BitSlice<O, T>;
			type Mut = &'a mut BitSlice<O, T>;

			fn get(self, slice: Self::Immut) -> Option<Self::Immut> {
				$get(self, slice)
			}

			#[inline]
			fn get_mut(self, slice: Self::Mut) -> Option<Self::Mut> {
				self.get(slice).map(|s| s.bitptr().into_bitslice_mut())
			}

			unsafe fn get_unchecked(self, slice: Self::Immut) -> Self::Immut {
				$unchecked(self, slice)
			}

			#[inline]
			unsafe fn get_unchecked_mut(self, slice: Self::Mut) -> Self::Mut {
				self.get_unchecked(slice).bitptr().into_bitslice_mut()
			}

			#[inline]
			fn index(self, slice: Self::Immut) -> Self::Immut {
				let r = self.clone();
				let l = slice.len();
				self.clone()
					.get(slice)
					.unwrap_or_else(|| {
						panic!("Range {:?} out of bounds: {}", r, l)
					})
			}

			#[inline]
			fn index_mut(self, slice: Self::Mut) -> Self::Mut {
				self.index(slice).bitptr().into_bitslice_mut()
			}
		}
	)* };

	( $( $r:ty => map $func:expr; )* ) => { $(
		impl<'a, O, T> BitSliceIndex<'a, O, T> for $r
		where O: 'a + BitOrder, T: 'a + BitStore {
			type Immut = &'a BitSlice<O, T>;
			type Mut = &'a mut BitSlice<O, T>;

			#[inline]
			fn get(self, slice: Self::Immut) -> Option<Self::Immut> {
				$func(self).get(slice)
			}

			#[inline]
			fn get_mut(self, slice: Self::Mut) -> Option<Self::Mut> {
				$func(self).get_mut(slice)
			}

			#[inline]
			unsafe fn get_unchecked(self, slice: Self::Immut) -> Self::Immut {
				$func(self).get_unchecked(slice)
			}

			#[inline]
			unsafe fn get_unchecked_mut(self, slice: Self::Mut) -> Self::Mut {
				$func(self).get_unchecked_mut(slice)
			}

			#[inline]
			fn index(self, slice: Self::Immut) -> Self::Immut {
				$func(self).index(slice)
			}

			#[inline]
			fn index_mut(self, slice: Self::Mut) -> Self::Mut {
				$func(self).index_mut(slice)
			}
		}
	)* };
}

range_impl! {
	Range<usize> => get |Range { start, end }, slice: Self::Immut| {
		let len = slice.len();

		if start > len || end > len || start > end {
			return None;
		}

		Some(unsafe { (start .. end).get_unchecked(slice) })
	},
	unchecked |Range { start, end }, slice: Self::Immut| {
		let (data, head, _) = slice.bitptr().raw_parts();

		let (skip, new_head) = head.offset(start as isize);

		BitPtr::new_unchecked(
			data.r().offset(skip),
			new_head,
			end - start,
		).into_bitslice()
	};

	RangeFrom<usize> => get |RangeFrom { start }, slice: Self::Immut| {
		let len = slice.len();
		if start <= len {
			Some(unsafe { (start ..).get_unchecked(slice) })
		}
		else {
			None
		}
	},
	unchecked |RangeFrom { start }, slice: Self::Immut| {
		let (data, head, bits) = slice.bitptr().raw_parts();

		let (skip, new_head) = head.offset(start as isize);

		BitPtr::new_unchecked(
			data.r().offset(skip),
			new_head,
			bits - start,
		).into_bitslice()
	};

	// `.. end` just changes the length
	RangeTo<usize> => get |RangeTo { end }, slice: Self::Immut| {
		let len = slice.len();
		if end <= len {
			Some(unsafe { (.. end).get_unchecked(slice) })
		}
		else {
			None
		}
	},
	unchecked |RangeTo { end }, slice: Self::Immut| {
		let mut bp = slice.bitptr();
		bp.set_len(end);
		bp.into_bitslice()
	};
}

range_impl! {
	RangeInclusive<usize> => map |this: Self| {
		#[allow(clippy::range_plus_one)]
		(*this.start() .. *this.end() + 1)
	};

	RangeToInclusive<usize> => map |RangeToInclusive { end }| {
		#[allow(clippy::range_plus_one)]
		(.. end + 1)
	};
}

/// `RangeFull` is the identity function.
impl<'a, O, T> BitSliceIndex<'a, O, T> for RangeFull
where O: 'a + BitOrder, T: 'a + BitStore {
	type Immut = &'a BitSlice<O, T>;
	type Mut = &'a mut BitSlice<O, T>;

	#[inline]
	fn get(self, slice: Self::Immut) -> Option<Self::Immut> {
		Some(slice)
	}

	#[inline]
	fn get_mut(self, slice: Self::Mut) -> Option<Self::Mut> {
		Some(slice)
	}

	#[inline]
	unsafe fn get_unchecked(self, slice: Self::Immut) -> Self::Immut {
		slice
	}

	#[inline]
	unsafe fn get_unchecked_mut(self, slice: Self::Mut) -> Self::Mut {
		slice
	}

	#[inline]
	fn index(self, slice: Self::Immut) -> Self::Immut {
		slice
	}

	#[inline]
	fn index_mut(self, slice: Self::Mut) -> Self::Mut {
		slice
	}
}
