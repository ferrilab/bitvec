/*! Reimplementation of the standard library’s `Vec` inherent method API.
!*/

use super::*;

use crate::{
	cursor::Cursor,
	pointer::BitPtr,
	store::BitStore,
};

use alloc::{
	vec::Vec,
};

use core::{
	hint::unreachable_unchecked,
};

impl<C, T> BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Constructs a new, empty `BitVec<C, T>`.
	///
	/// The vector will not allocate until elements are pushed onto it.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv: BitVec<Local, Word> = BitVec::new();
	/// ```
	pub /* const */ fn new() -> Self {
		Self::with_capacity(0)
	}

	/// Constructs a new, empty `BitVec<C, T>` with the specified capacity.
	///
	/// The vector will be able to hold at least `capacity` bits without
	/// reallocating. If `capacity` is 0, the vector will not allocate.
	///
	/// It is important to note that although the returned vector has the
	/// *capacity* specified, the vector will have a zero *length*. For an
	/// explanation of the difference between length and capacity, see
	/// [*Capacity and reallocation*].
	///
	/// [*Capacity and reallocation*]: #capacity-and-reallocation
	pub fn with_capacity(capacity: usize) -> Self {
		//  Get the number of `T` elements needed to store the requested bit
		//  capacity.
		let (elts, _) = 0u8.idx::<T>().span(capacity);
		//  Allocate a buffer that can hold that many elements.
		let v = Vec::with_capacity(elts);
		let (ptr, cap) = (v.as_ptr(), v.capacity());
		//  Disarm the `Vec` destructor.
		mem::forget(v);
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::uninhabited(ptr),
			capacity: cap,
		}
	}

	/// Returns the number of bits the vector can hold without reallocating.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bv: BitVec<Local, Word> = BitVec::with_capacity(100);
	/// assert!(bv.capacity() >= 100);
	pub fn capacity(&self) -> usize {
		self.capacity
			.checked_mul(T::BITS as usize)
			.expect("Vector capacity overflow")
	}

	/// Reserves capacity for at least `additional` more bits to be inserted in
	/// the given `BitVec<C, T>`. The collection may reserve more space to avoid
	/// frequent reallocations. After calling `reserve`, the capacity will be
	/// greater than or equal to `self.len() + additional`. Does nothing if the
	/// capacity is already sufficient.
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows `BitPtr::<T>::MAX_BITS`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1];
	/// bv.reserve(10);
	/// assert!(bv.capacity() >= 11);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		let newlen = self.len() + additional;
		assert!(
			newlen <= BitPtr::<T>::MAX_BITS,
			"Capacity overflow: {} exceeds {}",
			newlen,
			BitPtr::<T>::MAX_BITS,
		);
		let (total_elts, _) = self.pointer.head().span(newlen);
		if let Some(extra) = total_elts.checked_sub(self.capacity) {
			self.do_unto_vec(|v| v.reserve(extra));
		}
	}

	/// Reserves the minimum capacity for exactly `additional` more bits to be
	/// inserted in the given `BitVec<C, T>`. After calling `reserve_exact`,
	/// capacity will be greater than or equal to `self.len() + additional`.
	/// Does nothing if the capacity is already sufficient.
	///
	/// Note that the allocator may give the collection more space than it
	/// requests. Therefore, capacity can not be relied upon to be precisely
	/// minimal. Prefer `reserve` if future insertions are expected.
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows `BitPtr::<T>::MAX_BITS`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1];
	/// bv.reserve_exact(10);
	/// assert!(bv.capacity() >= 11);
	/// ```
	pub fn reserve_exact(&mut self, additional: usize) {
		let newlen = self.len() + additional;
		assert!(
			newlen <= BitPtr::<T>::MAX_BITS,
			"Capacity overflow: {} exceeds {}",
			newlen,
			BitPtr::<T>::MAX_BITS,
		);
		let (total_elts, _) = self.pointer.head().span(newlen);
		let extra = total_elts - self.capacity;
		self.do_unto_vec(|v| v.reserve_exact(extra));
	}

	/// Shrinks the capacity of the vector as much as possible.
	///
	/// It will drop down as close as possible to the length but the allocator
	/// may still inform the vector that there is space for a few more elements.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv: BitVec<Local, Word> = BitVec::with_capacity(10);
	/// bv.extend([true, false, true].iter().copied());
	/// assert!(bv.capacity() >= 10);
	/// bv.shrink_to_fit();
	/// assert!(bv.capacity() >= 3);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		self.do_unto_vec(Vec::shrink_to_fit);
	}

	/// Converts the bit-vector into [`Box<[T]>`].
	///
	/// Note that this will drop any excess capacity.
	///
	/// For the vec-to-box equivalent that produces a [`BitBox<C, T>`], see
	/// [`into_boxed_bitslice`].
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bv = bitvec![1, 0, 1];
	///
	/// let slice = bv.into_boxed_slice();
	/// ```
	///
	/// Any excess capacity is removed:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = BitVec::<Local, Word>::with_capacity(100);
	/// bv.extend([true, false, true].iter().copied());
	///
	/// assert!(bv.capacity() >= 100);
	/// let slice = bv.into_boxed_slice();
	/// let boxed_bitslice = BitBox::<Local, Word>::from_boxed_slice(slice);
	/// let bv = BitVec::from_boxed_bitslice(boxed_bitslice);
	/// assert!(bv.capacity() >= 3);
	/// ```
	///
	/// [`BitBox<C, T>`]: ../boxed/struct.BitBox.html
	/// [`Box<[T]>`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
	/// [`into_boxed_bitslice`]: #method.into_boxed_bitslice
	pub fn into_boxed_slice(self) -> Box<[T]> {
		self.into_vec().into_boxed_slice()
	}

	/// Shortens the vector, keeping the first `len` bits and dropping the rest.
	///
	/// If `len` is greater than the vector’s current length, this has no
	/// effect.
	///
	/// The [`drain`] method can emulate `truncate`, but causes the excess bits
	/// to be returned instead of dropped.
	///
	/// Note that this method has no effect on the allocated capacity of the
	/// vector.
	///
	/// # Examples
	///
	/// Truncating a five-bit vector to two bits:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1, 0, 1, 0, 1];
	/// bv.truncate(2);
	/// assert_eq!(bv, bitvec![1, 0]);
	/// ```
	///
	/// No truncation occurs when `len` is greater than the vector’s current
	/// length:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1; 5];
	/// bv.truncate(10);
	/// assert_eq!(bv, bitvec![1; 5]);
	/// ```
	///
	/// Truncating to zero is equivalent to calling the [`clear`] method.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![0; 5];
	/// bv.truncate(0);
	/// assert!(bv.is_empty());
	/// ```
	pub fn truncate(&mut self, len: usize) {
		if len < self.len() {
			unsafe { self.set_len(len) }
		}
	}

	/// Extracts an element slice containing the entire vector.
	///
	/// Unlike [`BitSlice::as_slice`], this will produce partial edge elements,
	/// as they are known to not be aliased by any other slice handles.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// # #[cfg(feature = "std")] {
	/// use std::io::{self, Write};
	/// let buffer = bitvec![Local, u8; 1, 0, 1, 0, 1];
	/// io::sink().write(buffer.as_slice()).unwrap();
	/// # }
	/// ```
	///
	/// [`BitSlice::as_slice`]: ../slice/struct.BitSlice.html#method.as_slice
	pub fn as_slice(&self) -> &[T] {
		self.pointer.as_slice()
	}

	/// Extracts a mutable slice of the entire vector.
	///
	/// Unlike [`BitSlice::as_mut_slice`], this will produce partial edge
	/// elements, as they are known to not be aliased by any other slice
	/// handles.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// # #[cfg(feature = "std")] {
	/// use std::io::{self, Read};
	/// let mut buffer = bitvec![Local, u8; 0; 24];
	/// io::repeat(0xA5u8).read_exact(buffer.as_mut_slice()).unwrap();
	/// # }
	/// ```
	///
	/// [`BitSlice::as_mut_slice`]: ../slice/struct.BitSlice.html#method.as_mut_slice
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		self.pointer.as_mut_slice()
	}

	/// Forces the length of the vector to `new_len`.
	///
	/// This is a low-level operation that maintains none of the normal
	/// invariants of the type. Normally changing the length of a vector is done
	/// using one of the safe operations instead, such as [`truncate`],
	/// [`resize`], [`extend`], or [`clear`].
	///
	/// # Safety
	///
	/// - `new_len` must be less than or equal to [`capacity()`].
	/// - The underlying elements at `old_len ..new_len` must be initialized.
	///
	/// # Examples
	///
	/// This method can be useful for situations in which the vector is serving
	/// as a buffer for other code, particularly over FFI.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = BitVec::<Local, Word>::with_capacity(17);
	/// assert!(bv.is_empty());
	/// unsafe { bv.set_len(23) };
	/// assert_eq!(bv.len(), 23);
	/// ```
	///
	/// This example executes correctly, because the allocator can only reserve
	/// even multiples of bytes, and so rounds up from the `with_capacity`
	/// argument.
	pub unsafe fn set_len(&mut self, new_len: usize) {
		assert!(
			new_len <= BitPtr::<T>::MAX_BITS,
			"Capacity overflow: {} overflows maximum length {}",
			new_len,
			BitPtr::<T>::MAX_BITS,
		);
		let cap = self.capacity();
		assert!(
			new_len <= cap,
			"Capacity overflow: {} overflows allocation size {}",
			new_len,
			cap,
		);
		self.pointer.set_len(new_len);
	}

	/// Removes a bit from the vector and returns it.
	///
	/// The removed bit is replaced by the last bit of the vector.
	///
	/// This does not preserve ordering, but is O(1).
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1, 0, 1, 0, 1];
	///
	/// assert!(!bv.swap_remove(1));
	/// assert_eq!(bv, bitvec![1, 1, 1, 0]);
	///
	/// assert!(bv.swap_remove(0));
	/// assert_eq!(bv, bitvec![0, 1, 1]);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> bool {
		let len = self.len();
		assert!(len != 0, "Empty vectors cannot remove");
		assert!(index < len, "Index {} out of bounds: {}", index, len);
		self.swap(index, len - 1);
		self.pop().unwrap_or_else(|| unsafe { unreachable_unchecked() })
	}

	/// Inserts a bit at position `index` within the vector, shifting all bits
	/// after it to the right.
	///
	/// # Panics
	///
	/// Panics if `index > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1, 0, 1, 0, 1];
	/// bv.insert(1, false);
	/// assert_eq!(bv, bitvec![1, 0, 0, 1, 0, 1]);
	/// bv.insert(4, true);
	/// assert_eq!(bv, bitvec![1, 0, 0, 1, 1, 0, 1]);
	/// ```
	pub fn insert(&mut self, index: usize, value: bool) {
		let len = self.len();
		assert!(index <= len, "Index {} is out of bounds: {}", index, len);
		self.push(value);
		unsafe { self.get_unchecked_mut(index ..) }.rotate_right(1);
	}

	/// Removes and returns the bit at position `index` within the vector,
	/// shifting all bits after it to the left.
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1, 0, 1, 0, 1];
	/// assert!(!bv.remove(1));
	/// assert_eq!(bv, bitvec![1, 1, 0, 1]);
	/// ```
	pub fn remove(&mut self, index: usize) -> bool {
		let len = self.len();
		assert!(len != 0, "Empty vectors cannot remove");
		assert!(index < len, "Index {} is out of bounds: {}", index, len);
		unsafe {
			self.get_unchecked_mut(index ..).rotate_left(1);
			self.pop().unwrap_or_else(|| unreachable_unchecked())
		}
	}
}
