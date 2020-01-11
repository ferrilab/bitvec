//! Reimplementation of the standard library’s `Vec` inherent method API.

use super::*;

use crate::{
	order::BitOrder,
	pointer::BitPtr,
	store::BitStore,
};

use alloc::{
	boxed::Box,
	vec::Vec,
};

use core::{
	cmp,
	hint::unreachable_unchecked,
	ops::RangeBounds,
	ptr::NonNull,
};

impl<O, T> BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Constructs a new, empty `BitVec<C, T>`.
	///
	/// The vector will not allocate until elements are pushed onto it.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv: BitVec<Local, usize> = BitVec::new();
	/// ```
	#[inline]
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
			_order: PhantomData,
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
	/// let bv: BitVec<Local, usize> = BitVec::with_capacity(100);
	/// assert!(bv.capacity() >= 100);
	#[inline]
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
		if let Some(extra) = total_elts.checked_sub(self.pointer.elements()) {
			self.with_vec(|v| v.reserve(extra));
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
		self.with_vec(|v| v.reserve_exact(extra));
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
	/// let mut bv: BitVec<Local, usize> = BitVec::with_capacity(10);
	/// bv.extend([true, false, true].iter().copied());
	/// assert!(bv.capacity() >= 10);
	/// bv.shrink_to_fit();
	/// assert!(bv.capacity() >= 3);
	/// ```
	#[inline]
	pub fn shrink_to_fit(&mut self) {
		self.with_vec(Vec::shrink_to_fit);
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
	/// let mut bv = BitVec::<Local, usize>::with_capacity(100);
	/// bv.extend([true, false, true].iter().copied());
	///
	/// assert!(bv.capacity() >= 100);
	/// let slice = bv.into_boxed_slice();
	/// let boxed_bitslice = BitBox::<Local, usize>::from_boxed_slice(slice);
	/// let bv = BitVec::from_boxed_bitslice(boxed_bitslice);
	/// assert!(bv.capacity() >= 3);
	/// ```
	///
	/// [`BitBox<C, T>`]: ../boxed/struct.BitBox.html
	/// [`Box<[T]>`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
	/// [`into_boxed_bitslice`]: #method.into_boxed_bitslice
	#[inline]
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
	#[inline]
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
	#[inline]
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
	#[inline]
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
	/// let mut bv = BitVec::<Local, usize>::with_capacity(17);
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

	/// Retains only the bits that pass the predicate.
	///
	/// This removes all bits `b` where `f(e)` returns `false`. This method
	/// operates in place and preserves the order of the retained bits. Because
	/// it is in-place, it operates in `O(n²)` time.
	///
	/// # API Differences
	///
	/// The [`Vec::retain`] method takes a predicate function with signature
	/// `(&T) -> bool`, whereas this method’s predicate function has signature
	/// `(usize, &T) -> bool`. This difference is in place because `BitSlice` by
	/// definition has only one bit of information per slice item, and including
	/// the index allows the callback function to make more informed choices.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![0, 1, 0, 1, 0, 1];
	/// bv.retain(|_, b| b);
	/// assert_eq!(bv, bitvec![1, 1, 1]);
	/// ```
	///
	/// [`BitSlice::for_each`]: ../slice/struct.BitSlice.html#method.for_each
	pub fn retain<F>(&mut self, mut pred: F)
	where F: FnMut(usize, bool) -> bool {
		for n in (0 .. self.len()).rev() {
			if !pred(n, self[n]) {
				self.remove(n);
			}
		}
	}

	/// Appends a bit to the back of the vector.
	///
	/// If the vector is at capacity, this may cause a reallocation.
	///
	/// # Panics
	///
	/// This will panic if the push will cause the vector to allocate above
	/// `BitPtr<T>::MAX_ELTS` or machine capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	/// ```
	pub fn push(&mut self, value: bool) {
		let len = self.len();
		assert!(
			len <= BitPtr::<T>::MAX_BITS,
			"Capacity overflow: {} >= {}",
			len,
			BitPtr::<T>::MAX_BITS,
		);
		//  If self is empty *or* tail is at the back edge of an element, push
		//  an element onto the vector.
		if self.is_empty() || *self.pointer.tail() == T::BITS {
			self.with_vec(|v| v.push(T::FALSE));
		}
		//  At this point, it is always safe to increment the tail, and then
		//  write to the newly live bit.
		unsafe {
			self.pointer.set_len(len + 1);
			self.set_unchecked(len, value);
		}
	}

	/// Removes the last element from a vector and returns it, or `None` if it
	/// is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	///
	/// assert!(bv.pop().unwrap());
	/// assert!(bv.is_empty());
	/// assert!(bv.pop().is_none());
	/// ```
	pub fn pop(&mut self) -> Option<bool> {
		self.len().checked_sub(1).map(|new_len| unsafe {
			let out = *self.get_unchecked(new_len);
			self.set_len(new_len);
			out
		})
	}

	/// Moves all the elements of `other` into `self`, leaving `other` empty.
	///
	/// # Panics
	///
	/// Panics if the number of bits in the vector overflows
	/// `BitPtr::<T>::MAX_ELTS`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv1 = bitvec![0; 10];
	/// let mut bv2 = bitvec![1; 10];
	/// bv1.append(&mut bv2);
	/// assert_eq!(bv1.len(), 20);
	/// assert!(bv1[10]);
	/// assert!(bv2.is_empty());
	/// ```
	#[inline]
	pub fn append<D, U>(&mut self, other: &mut BitVec<D, U>)
	where D: BitOrder, U: BitStore {
		self.extend(other.iter().copied());
		other.clear();
	}

	/// Creates a draining iterator that removes the specified range from the
	/// vector and yields the removed bits.
	///
	/// # Notes
	///
	/// 1. The element range is removed even if the iterator is only partially
	///    consumed or not consumed at all.
	/// 2. It is unspecified how many bits are removed from the vector if the
	///    `Drain` value is leaked.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end
	/// point is greater than the length of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![0, 0, 1, 1, 1, 0, 0];
	/// assert_eq!(bv.len(), 7);
	/// for bit in bv.drain(2 .. 5) {
	///   assert!(bit);
	/// }
	/// assert!(bv.not_any());
	/// assert_eq!(bv.len(), 4);
	/// ```
	pub fn drain<R>(&mut self, range: R) -> Drain<O, T>
	where R: RangeBounds<usize> {
		use core::ops::Bound::*;
		let len = self.len();
		let from = match range.start_bound() {
			Included(&n) => n,
			Excluded(&n) => n + 1,
			Unbounded    => 0,
		};
		//  First index beyond the end of the drain.
		let upto = match range.end_bound() {
			Included(&n) => n + 1,
			Excluded(&n) => n,
			Unbounded    => len,
		};
		assert!(from <= upto, "The drain start must be below the drain end");
		assert!(upto <= len, "The drain end must be within the vector bounds");

		unsafe {
			let ranging: &BitSlice<O, T> = self.as_bitslice()[from..upto]
				//  remove the lifetime and borrow awareness
				.bitptr()
				.into_bitslice();
			self.set_len(from);

			Drain {
				bitvec: NonNull::from(self),
				iter: ranging.iter(),
				tail_start: upto,
				tail_len: len - upto,
			}
		}
	}

	/// Clears the vector, removing all values.
	///
	/// Note that this method has no effect on the allocated capacity of the
	/// vector.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1; 30];
	/// assert_eq!(bv.len(), 30);
	/// assert!(bv.iter().all(|b| *b));
	/// bv.clear();
	/// assert!(bv.is_empty());
	/// ```
	///
	/// After calling `clear()`, `bv` will no longer show raw memory, so the
	/// above test cannot show that the underlying memory is not altered. This
	/// is also an implementation detail on which you should not rely.
	pub fn clear(&mut self) {
		unsafe { self.set_len(0) }
	}

	/// Splits the collection into two at the given index.
	///
	/// Returns a newly allocated `Self`. `self` contains elements `[0, at)`,
	/// and the returned `Self` contains elements `[at, len)`.
	///
	/// Note that the capacity of `self` does not change.
	///
	/// # Panics
	///
	/// Panics if `at > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv1 = bitvec![0, 0, 0, 1, 1, 1];
	/// let bv2 = bv1.split_off(3);
	/// assert_eq!(bv1, bitvec![0, 0, 0]);
	/// assert_eq!(bv2, bitvec![1, 1, 1]);
	/// ```
	pub fn split_off(&mut self, at: usize) -> Self {
		let len = self.len();
		assert!(at <= len, "Index out of bounds: {} is beyond {}", at, len);
		match at {
			0 => mem::replace(self, Self::new()),
			n if n == len => Self::new(),
			_ => {
				let out = self[at ..].to_owned();
				self.truncate(at);
				out
			},
		}
	}

	/// Resizes the `BitVec` in-place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the `BitVec` is extended by the
	/// difference, with each additional slot filled with the result of calling
	/// the closure `f`. The return values from `f` will end up in the `BitVec`
	/// in the order they have been generated.
	///
	/// If `new_len` is less than `len`, the `BitVec` is simply truncated.
	///
	/// This method uses a closure to create new values on every push. If you’d
	/// rather [`Clone`] a given value, use [`resize`]. If you want to use the
	/// [`Default`] trait to generate values, you can pass
	/// [`Default::default()`] as the second argument.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1, 0, 1];
	/// bv.resize_with(5, Default::default);
	/// assert_eq!(bv, bitvec![1, 0, 1, 0, 0]);
	///
	/// let mut bv = bitvec![];
	/// let mut p = 1;
	/// bv.resize_with(4, || { p += 1; p % 2 == 0});
	/// assert_eq!(bv, bitvec![1, 0, 1, 0]);
	/// ```
	///
	/// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
	/// [`Default`]: https://doc.rust-lang.org/std/default/trait.Default.html
	/// [`Default::default()`]: https://doc.rust-lang.org/std/default/trait.Default.html#tymethod.default
	/// [`resize`]: #method.resize
	pub fn resize_with<F>(&mut self, new_len: usize, mut f: F)
	where F: FnMut() -> bool {
		let len = self.len();
		match new_len.cmp(&len) {
			cmp::Ordering::Less => self.truncate(new_len),
			cmp::Ordering::Greater => {
				let diff = new_len - len;
				self.reserve(diff);
				for _ in 0 .. (new_len - len) {
					self.push(f());
				}
			},
			cmp::Ordering::Equal => {},
		}
	}

	/// Resizes the `BitVec` in place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the `BitVec` is extended by the
	/// difference, with each additional slot filled with `value`. If `new_len`
	/// is less than `len`, the `BitVec` is simply truncated.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![0; 4];
	/// bv.resize(8, true);
	/// assert_eq!(bv, bitvec![0, 0, 0, 0, 1, 1, 1, 1]);
	/// bv.resize(5, false);
	/// assert_eq!(bv, bitvec![0, 0, 0, 0, 1]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: bool) {
		let len = self.len();
		match new_len.cmp(&len) {
			cmp::Ordering::Less => self.truncate(new_len),
			cmp::Ordering::Greater => {
				let diff = new_len - len;
				self.reserve(diff);
				unsafe { self.set_len(new_len); }
				self[len ..].set_all(value);
			},
			cmp::Ordering::Equal => {},
		}
	}

	/// Clones and appends all bits in a bit-slice to the `BitVec`.
	///
	/// Iterates over the bit-slice `other`, clones each bit, and then appends
	/// it to this `BitVec`. The `other` slice is traversed in-order.
	///
	/// Note that this function is the same as [`extend`] except that it is
	/// specialized to work with bit-slices instead. If and when Rust gets
	/// specialization this function will likely be deprecated (but still
	/// available).
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![1];
	/// bv.extend_from_slice(0xA5u8.bits::<Lsb0>());
	/// assert_eq!(bv, bitvec![1, 1, 0, 1, 0, 0, 1, 0, 1]);
	/// ```
	///
	/// [`extend`]: #method.extend
	pub fn extend_from_slice<D, U>(&mut self, other: &BitSlice<D, U>)
	where D: BitOrder, U: BitStore {
		let len = self.len();
		let olen = other.len();
		self.reserve(olen);
		unsafe { self.set_len(len + olen); }
		self[len ..].clone_from_slice(other)
	}

	/// Creates a splicing iterator that replaces the specified range in the
	/// vector with the given `replace_with` iterator and yields the removed
	/// bits. `replace_with` does not need to be the same length as `range`.
	///
	/// # Notes
	///
	/// 1. The element range is removed and replaced even if the iterator
	///    produced by this method is not consumed until the end.
	/// 2. It is unspecified how many bits are removed from the vector if the
	///    `Splice` value is leaked.
	/// 3. The input iterator `replace_with` is only consumed when the `Splice`
	///    value is dropped.
	/// 4. This is optimal if:
	///    - the tail (elements in the vector after `range`) is empty,
	///    - or `replace_with` yields fewer bits than `range`’s length,
	///    - the lower bound of its `size_hint()` is exact.
	///
	///    Otherwise, a temporary vector is allocated and the tail is moved
	///    twice.
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end
	/// point is greater than the length of the vector.
	///
	/// # Examples
	///
	/// This example starts with six bits of zero, and then splices out bits 2
	/// and 3 and replaces them with four bits of one.
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut bv = bitvec![0; 6];
	/// let bv2 = bitvec![1; 4];
	///
	/// let s = bv.splice(2 .. 4, bv2).collect::<BitVec>();
	/// assert_eq!(s.len(), 2);
	/// assert!(!s[0]);
	/// assert_eq!(bv, bitvec![0, 0, 1, 1, 1, 1, 0, 0]);
	/// ```
	pub fn splice<R, I>(
		&mut self,
		range: R,
		replace_with: I,
	) -> Splice<O, T, <I as IntoIterator>::IntoIter>
	where I: IntoIterator<Item=bool>, R: RangeBounds<usize> {
		Splice {
			drain: self.drain(range),
			splice: replace_with.into_iter(),
		}
	}
}
