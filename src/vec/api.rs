//! Port of the `Vec<T>` inherent API.

use crate::{
	mem::BitMemory,
	mutability::Mut,
	order::BitOrder,
	ptr::{
		Address,
		BitPtr,
		BitSpan,
	},
	slice::BitSlice,
	store::BitStore,
	vec::{
		iter::{
			Drain,
			Splice,
		},
		BitVec,
	},
};

use alloc::{
	boxed::Box,
	vec::Vec,
};

use core::{
	mem::{
		self,
		ManuallyDrop,
	},
	ops::RangeBounds,
	slice,
};

use tap::pipe::Pipe;

impl<O, T> BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Constructs a new, empty, `BitVec<O, T>`.
	///
	/// The vector will not allocate until bits are pushed into it.
	///
	/// # Original
	///
	/// [`Vec::new`](alloc::vec::Vec::new)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::new();
	/// ```
	pub fn new() -> Self {
		Self {
			bitspan: BitSpan::<Mut, O, T>::EMPTY,
			capacity: 0,
		}
	}

	/// Constructs a new, empty, `BitVec<O, T>` with the specified capacity.
	///
	/// The vector will be able to hold at least `capacity` bits without
	/// reällocating. If `capacity` is 0, the vector will not allocate.
	///
	/// It is important to note that although the returned vector has the
	/// *capacity* specified, the vector will have a zero *length*. For an
	/// explanation of the difference between length and capacity, see
	/// *[Capacity and reällocation]*.
	///
	/// # Original
	///
	/// [`Vec::with_capacity`](alloc::vec::Vec::with_capacity)
	///
	/// # Panics
	///
	/// Panics if the requested capacity exceeds the vector’s limits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::with_capacity(128);
	///
	/// // The vector contains no bits, even
	/// // though it has the capacity for more
	/// assert_eq!(bv.len(), 0);
	/// assert!(bv.capacity() >= 128);
	///
	/// // These are all done
	/// // without reällocating…
	/// for i in 0 .. 128 {
	///   bv.push(i & 0xC0 == i);
	/// }
	/// assert_eq!(bv.len(), 128);
	/// assert!(bv.capacity() >= 128);
	///
	/// // …but this may make
	/// // the vector reällocate
	/// bv.push(false);
	/// assert_eq!(bv.len(), 129);
	/// assert!(bv.capacity() >= 129);
	/// ```
	///
	/// [Capacity and reällocation]: #capacity-and-reallocation
	pub fn with_capacity(capacity: usize) -> Self {
		assert!(
			capacity <= BitSlice::<O, T>::MAX_BITS,
			"Vector capacity exceeded: {} > {}",
			capacity,
			BitSlice::<O, T>::MAX_BITS
		);
		let mut vec = capacity
			.pipe(crate::mem::elts::<T>)
			.pipe(Vec::<T>::with_capacity)
			.pipe(ManuallyDrop::new);
		let (addr, capacity) = (vec.as_mut_ptr(), vec.capacity());
		let bitspan = addr
			.pipe(|a| unsafe { Address::new_unchecked(a as usize) })
			.pipe(BitSpan::uninhabited);
		Self { bitspan, capacity }
	}

	/// Decomposes a `BitVec<O, T>` into its raw components.
	///
	/// Returns the raw bit-pointer to the underlying buffer, the length of the
	/// bit-vector (in bits), and the allocated capacity of the buffer (in
	/// bits). These are the same arguments in the same order as the arguments
	/// to [`from_raw_parts`].
	///
	/// After calling this function, the caller is responsible for the memory
	/// previously managed by the `BitVec`. The only way to do this is to
	/// convert the raw pointer and capacity back into a `BitVec` with the
	/// [`from_raw_parts`] function, allowing the destructor to perform the
	/// cleanup.
	///
	/// # Original
	///
	/// [`Vec::into_raw_parts`](alloc::vec::Vec::into_raw_parts)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![1; 70];
	/// let (ptr, len, cap) = bv.into_raw_parts();
	///
	/// let rebuilt = unsafe {
	///   BitVec::from_raw_parts(ptr, len, cap)
	/// };
	/// assert_eq!(rebuilt, bits![1; 70]);
	/// ```
	///
	/// [`from_raw_parts`]: Self::from_raw_parts
	pub fn into_raw_parts(self) -> (BitPtr<Mut, O, T>, usize, usize) {
		let (ptr, len, capa) = (
			self.bitspan.as_bitptr(),
			self.bitspan.len(),
			self.capacity(),
		);
		mem::forget(self);
		(ptr, len, capa)
	}

	/// Creates a `BitVec<O, T>` directly from the raw components of another
	/// bit-vector.
	///
	/// # Original
	///
	/// [`Vec::from_raw_parts`](alloc::vec::Vec::from_raw_parts)
	///
	/// # Safety
	///
	/// This is highly unsafe, due to the number of invariants that aren’t
	/// checked:
	///
	/// - `ptr` needs to have been previously allocated via `BitVec<O, T>` (at
	///   least, it’s highly likely to be incorrect if it wasn’t).
	///
	/// - `T` needs to have the same size and alignment as what `ptr` was
	///   initially allocated with. (`T` having a less strict alignment isn’t
	///   sufficient; the alignment really needs to be equal to satisfy the
	///   [`dealloc`] requirement that memory be allocated and deällocated with
	///   the same layout.)
	///
	///   You may use [`BitPtr::cast`] to change between bare integers, `Cell`s,
	///   and atoms, as long as they all have the same memory width.
	///
	/// - `length` needs to be less than or equal to `capacity`.
	///
	/// - `capacity` needs to be the capacity, in bits, that the bit-pointer was
	///   allocated with.
	///
	/// Violating these **will** cause problems like corrupting the allocator’s
	/// internal data structures. For example, it is **not** safe to build a
	/// `BitVec<_, u16>` from a pointer to a C `char` array with length
	/// `size_t`. It’s also not safe to build one from a `Vec<u8>` and its
	/// length, because the allocator cares about the alignment, and these two
	/// types have different alignments. The buffer was allocated with alignment
	/// `1` (for `u8`), but after turning it into a `BitVec<_, u16>` it’ll be
	/// deällocated with alignment 2.
	///
	/// The ownership of `pointer` is effectively transferred to the `BitVec<O,
	/// T>` which may then deällocate, reällocate, or change the contents of
	/// memory pointed to by the pointer at will. Ensure that nothing else uses
	/// the pointer after calling this function.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::ptr as bv_ptr;
	/// use core::mem::ManuallyDrop;
	///
	/// let bv = bitvec![0, 1, 0, 0, 1];
	/// // Disarm the destructor so we are in full control of the allocation.
	/// let mut bv = ManuallyDrop::new(bv);
	///
	/// // Pull out the various important pieces of information about `bv`.
	/// let ptr = bv.as_mut_bitptr();
	/// let len = bv.len();
	/// let cap = bv.capacity();
	///
	/// unsafe {
	///   // Overwrite memory with the inverse bits.
	///   for i in 0 .. len {
	///     let bp = ptr.add(i);
	///     bv_ptr::write(bp, !bv_ptr::read(bp.immut()));
	///   }
	///
	///   // Put everything back together into a `BitVec`
	///   let rebuilt = BitVec::from_raw_parts(ptr, len, cap);
	///   assert_eq!(rebuilt, bits![1, 0, 1, 1, 0]);
	/// }
	/// ```
	///
	/// [`BitPtr::cast`]: crate::ptr::BitPtr::cast
	/// [`dealloc`]: alloc::alloc::GlobalAlloc::dealloc
	pub unsafe fn from_raw_parts(
		ptr: BitPtr<Mut, O, T>,
		length: usize,
		capacity: usize,
	) -> Self {
		Self {
			bitspan: ptr.span_unchecked(length),
			capacity: crate::mem::elts::<T>(capacity),
		}
	}

	/// Returns the number of bits the vector can hold without reällocating.
	///
	/// # Original
	///
	/// [`Vec::capacity`](alloc::vec::Vec::capacity)
	///
	/// # API Differences
	///
	/// This returns the number of *bits* available in the allocation’s storage
	/// space. This is technically correct ([`Vec::<bool>::capacity`] would
	/// return the same amount), but this value **cannot** be used to describe
	/// the allocation underlying the vector.
	///
	/// Use [`alloc_capacity`] to get the capacity of the underlying
	/// allocation, measured in `T`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec<LocalBits, usize> = BitVec::with_capacity(100);
	/// assert!(bv.capacity() >= 100);
	/// ```
	///
	/// [`Vec::<bool>::capacity`]: alloc::vec::Vec::capacity
	/// [`alloc_capacity`]: Self::alloc_capacity
	pub fn capacity(&self) -> usize {
		self.capacity
			.checked_mul(T::Mem::BITS as usize)
			.expect("Vector capacity exceeded")
			//  Don’t forget to subtract any dead bits in the front of the base!
			//  This has to be saturating, becase a non-zero head on a zero
			//  capacity underflows.
			.saturating_sub(self.bitspan.head().value() as usize)
	}

	/// Reserves capacity for at least `additional` more bits to be inserted in
	/// the given `BitVec<O, T>`. The collection may reserve more space to avoid
	/// frequent reällocations. After calling `.reserve()`, capacity will be
	/// greater than or equal to `self.len() + additional`. Does nothing if
	/// capacity is already sufficient.
	///
	/// # Original
	///
	/// [`Vec::reserve`](alloc::vec::Vec::reserve)
	///
	/// # Panics
	///
	/// Panics if the new capacity exceeds the vector’s limits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1];
	/// bv.reserve(100);
	/// assert!(bv.capacity() >= 101);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		let len = self.len();
		let new_len = len
			.checked_add(additional)
			.expect("Vector capacity exceeded");
		assert!(
			new_len <= BitSlice::<O, T>::MAX_BITS,
			"Vector capacity exceeded: {} > {}",
			new_len,
			BitSlice::<O, T>::MAX_BITS
		);
		let bitspan = self.bitspan;
		let head = bitspan.head();
		let elts = bitspan.elements();
		//  Only reserve if the request needs new elements.
		if let Some(extra) = head.span(new_len).0.checked_sub(elts) {
			self.with_vec(|v| v.reserve(extra));
			let capa = self.capacity();
			//  Zero the newly-reserved buffer.
			unsafe { self.get_unchecked_mut(len .. capa) }.set_all(false);
		}
	}

	/// Reserves the minimum capacity for exactly `additional` more bits to be
	/// inserted in the given `BitVec<O, T>`. After calling `.reserve_exact()`,
	/// capacity will be greater than or equal to `self.len() + additional`.
	/// Does nothing if the capacity is already sufficient.
	///
	/// Note that the allocator may give the collection more space than it
	/// requests. Therefore, capacity can not be relied upon to be precisely
	/// minimal. Prefer [`.reserve()`] if future insertions are expected.
	///
	/// # Original
	///
	/// [`Vec::reserve_exact`](alloc::vec::Vec::reserve_exact)
	///
	/// # Panics
	///
	/// Panics if the new capacity exceeds the vector’s limits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1];
	/// bv.reserve_exact(100);
	/// assert!(bv.capacity() >= 101);
	/// ```
	///
	/// [`.reserve()`]: Self::reserve
	pub fn reserve_exact(&mut self, additional: usize) {
		let new_len = self
			.len()
			.checked_add(additional)
			.expect("Vector capacity exceeded");
		assert!(
			new_len <= BitSlice::<O, T>::MAX_BITS,
			"Vector capacity exceeded: {} > {}",
			new_len,
			BitSlice::<O, T>::MAX_BITS
		);
		let bitspan = self.bitspan;
		let head = bitspan.head();
		let elts = bitspan.elements();
		//  Only reserve if the request needs new elements.
		if let Some(extra) = head.span(new_len).0.checked_sub(elts) {
			self.with_vec(|v| v.reserve_exact(extra));
		}
	}

	/// Shrinks the capacity of the vector as much as possible.
	///
	/// It will drop down as close as possible to the length but the allocator
	/// may still inform the vector that there is space for a few more bits.
	///
	/// # Original
	///
	/// [`Vec::shrink_to_fit`](alloc::vec::Vec::shrink_to_fit)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::with_capacity(100);
	/// bv.extend([false, true, false].iter().copied());
	/// assert!(bv.capacity() >= 100);
	/// bv.shrink_to_fit();
	/// assert!(bv.capacity() >= 3);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		self.with_vec(|v| v.shrink_to_fit());
	}

	/// Converts the vector into [`Box<[T]>`].
	///
	/// Note that this will drop any excess capacity.
	///
	/// # Original
	///
	/// [`Vec::into_boxed_slice`](alloc::vec::Vec::into_boxed_slice)
	///
	/// # Analogue
	///
	/// See [`.into_boxed_bitslice()`] for a `BitVec -> BitBox` transform.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 0];
	///
	/// let slice = bv.into_boxed_slice();
	/// assert_eq!(slice.len(), 1);
	/// ```
	///
	/// Any excess capacity is removed:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::with_capacity(100);
	/// bv.extend([false, true, false].iter().copied());
	///
	/// assert!(bv.capacity() >= 100);
	/// let slice = bv.into_boxed_slice();
	/// assert_eq!(slice.into_vec().capacity(), 1);
	/// ```
	///
	/// [`Box<[T]>`]: alloc::boxed::Box
	/// [`.into_boxed_bitslice()`]: Self::into_boxed_bitslice
	pub fn into_boxed_slice(self) -> Box<[T]> {
		self.into_vec().into_boxed_slice()
	}

	/// Shortens the vector, keeping the first `len` bits and dropping the rest.
	///
	/// If `len` is greater than the vector’s current length, this has no
	/// effect.
	///
	/// The [`.drain()`] method can emulate `truncate`, but causes the excess
	/// bits to be returned instead of dropped.
	///
	/// Note that this method has no effect on the allocated capacity of the
	/// vector, **nor does it erase truncated memory**. Bits in the allocated
	/// memory that are outside of the [`.as_bitslice()`] view always have
	/// **unspecified** values, and cannot be relied upon to be zero.
	///
	/// # Original
	///
	/// [`Vec::truncate`](alloc::vec::Vec::truncate)
	///
	/// # Examples
	///
	/// Truncating a five-bit vector to two bits:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 5];
	/// bv.truncate(2);
	/// assert_eq!(bv.len(), 2);
	/// assert!(bv.as_slice()[0].count_ones() >= 5);
	/// ```
	///
	/// No truncation occurs when `len` is greater than the vector’s current
	/// length:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 3];
	/// bv.truncate(8);
	/// assert_eq!(bv.len(), 3);
	/// ```
	///
	/// Truncating when `len == 0` is equivalent to calling the [`.clear()`]
	/// method.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0; 3];
	/// bv.truncate(0);
	/// assert!(bv.is_empty());
	/// ```
	///
	/// [`.as_bitslice()`]: Self::as_bitslice
	/// [`.clear()`]: Self::clear
	/// [`.drain()`]: Self::drain
	pub fn truncate(&mut self, len: usize) {
		if len < self.len() {
			unsafe { self.set_len_unchecked(len) }
		}
	}

	/// Extracts an element slice containing the entire vector.
	///
	/// # Original
	///
	/// [`Vec::as_slice`](alloc::vec::Vec::as_slice)
	///
	/// # Analogue
	///
	/// See [`.as_bitslice()`] for a `&BitVec -> &BitSlice` transform.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "std")] {
	/// use bitvec::prelude::*;
	/// use std::io::{self, Write};
	///
	/// let buffer = bitvec![Msb0, u8; 0, 1, 0, 1, 1, 0, 0, 0];
	/// io::sink().write(buffer.as_slice()).unwrap();
	/// # }
	/// ```
	///
	/// [`.as_bitslice()`]: Self::as_bitslice
	pub fn as_slice(&self) -> &[T] {
		let bitspan = self.bitspan;
		let (base, elts) = (bitspan.address().to_const(), bitspan.elements());
		unsafe { slice::from_raw_parts(base, elts) }
	}

	/// Extracts a mutable slice of the entire vector.
	///
	/// # Original
	///
	/// [`Vec::as_mut_slice`](alloc::vec::Vec::as_mut_slice)
	///
	/// # Analogue
	///
	/// See [`.as_mut_bitslice()`] for a `&mut BitVec -> &mut BitSlice`
	/// transform.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "std")] {
	/// use bitvec::prelude::*;
	/// use std::io::{self, Read};
	///
	/// let mut buffer = bitvec![Msb0, u8; 0; 24];
	/// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
	/// # }
	/// ```
	///
	/// [`.as_mut_bitslice()`]: Self::as_mut_bitslice
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		let bitspan = self.bitspan;
		let (base, elts) = (bitspan.address().to_mut(), bitspan.elements());
		unsafe { slice::from_raw_parts_mut(base, elts) }
	}

	/// Returns a raw pointer to the vector’s buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this
	/// function returns, or else it will end up pointing to garbage. Modifying
	/// the vector may cause its buffer to be reällocated, which would also make
	/// any pointers to it invalid.
	///
	/// The caller must also ensure that the memory the pointer
	/// (non-transitively) points to is never written to (except inside an
	/// [`UnsafeCell`]) using this pointer or any pointer derived from it. If
	/// you need to mutate the contents of the slice, use [`.as_mut_ptr()`].
	///
	/// # Original
	///
	/// [`Vec::as_ptr`](alloc::vec::Vec::as_ptr)
	///
	/// # Analogue
	///
	/// See [`.as_bitslice_ptr()`] for a `&BitVec -> *const BitSlice` transform.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Lsb0; 0, 1, 0, 1];
	/// let bv_ptr = bv.as_ptr();
	///
	/// unsafe {
	///   assert_eq!(*bv_ptr, 0b1010);
	/// }
	/// ```
	///
	/// [`UnsafeCell`]: core::cell::UnsafeCell
	/// [`.as_bitslice_ptr()`]: Self::as_bitslice_ptr
	/// [`.as_mut_ptr()`]: Self::as_mut_ptr
	pub fn as_ptr(&self) -> *const T {
		self.bitspan.address().to_const()
	}

	/// Returns an unsafe mutable pointer to the vector’s buffer.
	///
	/// The caller must ensure that the vector outlives the pointer this
	/// function returns, or else it will end up pointing to garbage. Modifying
	/// the vector may cause its buffer to be reällocated, which would also make
	/// any pointers to it invalid.
	///
	/// # Original
	///
	/// [`Vec::as_mut_ptr`](alloc::vec::Vec::as_mut_ptr)
	///
	/// # Analogue
	///
	/// See [`.as_mut_bitslice_ptr()`] for a `&mut BitVec -> *mut BitSlice`
	/// transform.
	///
	/// # Eaxmples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let size = 4;
	/// let mut bv: BitVec<Msb0, usize> = BitVec::with_capacity(size);
	/// let bv_ptr = bv.as_mut_ptr();
	///
	/// unsafe {
	///   *bv_ptr = !0;
	///   bv.set_len(size);
	/// }
	/// assert_eq!(bv.len(), 4);
	/// assert!(bv.all());
	/// ```
	///
	/// [`.as_mut_bitslice_ptr()`]: Self::as_mut_bitslice_ptr
	pub fn as_mut_ptr(&mut self) -> *mut T {
		self.bitspan.address().to_mut()
	}

	/// Forces the length of the vector to `new_len`.
	///
	/// This is a low-level operation that maintains none of the normal
	/// invariants of the type. Normally changing the length of a vector is done
	/// using one of the safe operations instead, such as [`.truncate()`],
	/// [`.resize()`], [`.extend()`], or [`.clear()`].
	///
	/// # Original
	///
	/// [`Vec::set_len`](alloc::vec::Vec::set_len)
	///
	/// # Safety
	///
	/// - `new_len` must be less than or equal to [`.capacity()`].
	///
	/// # Examples
	///
	/// This method can be useful for situations in which the vector is serving
	/// as a buffer for other code, particularly over FFI:
	///
	/// ```rust
	/// # #![allow(dead_code)]
	/// # #![allow(improper_ctypes)]
	/// # const ERL_OK: i32 = 0;
	/// # extern "C" {
	/// #   fn erl_read_bits(
	/// #     bv: *mut BitVec<Msb0, u8>,
	/// #     bits_reqd: usize,
	/// #     bits_read: *mut usize,
	/// #   ) -> i32;
	/// # }
	/// use bitvec::prelude::*;
	///
	/// // `bitvec` could pair with `rustler` for a better bitstream
	/// type ErlBitstring = BitVec<Msb0, u8>;
	/// # pub fn _test() {
	/// let mut bits_read = 0;
	/// // An imaginary Erlang function wants a large bit buffer.
	/// let mut buf = ErlBitstring::with_capacity(32_768);
	/// // SAFETY: When `erl_read_bits` returns `ERL_OK`, it holds that:
	/// // 1. `bits_read` bits were initialized.
	/// // 2. `bits_read` <= the capacity (32_768)
	/// // which makes `set_len` safe to call.
	/// unsafe {
	///   // Make the FFI call...
	///   let status = erl_read_bits(&mut buf, 10, &mut bits_read);
	///   if status == ERL_OK {
	///     // ...and update the length to what was read in.
	///     buf.set_len(bits_read);
	///   }
	/// }
	/// # }
	/// ```
	///
	/// [`.capacity()`]: Self::capacity
	/// [`.clear()`]: Self::clear
	/// [`.extend()`]: Self::extend
	/// [`.resize()`]: Self::resize
	/// [`.truncate()`]: Self::truncate
	pub unsafe fn set_len(&mut self, new_len: usize) {
		assert!(
			new_len <= BitSlice::<O, T>::MAX_BITS,
			"Capacity exceeded: {} exceeds maximum length {}",
			new_len,
			BitSlice::<O, T>::MAX_BITS,
		);
		let cap = self.capacity();
		assert!(
			new_len <= cap,
			"Capacity exceeded: {} exceeds allocation size {}",
			new_len,
			cap,
		);
		self.set_len_unchecked(new_len);
	}

	/// Removes a bit from the vector and returns it.
	///
	/// The removed bit is replaced by the last bit of the vector.
	///
	/// This does not preserve ordering, but is O(1).
	///
	/// # Original
	///
	/// [`Vec::swap_remove`](alloc::vec::Vec::swap_remove)
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 1, 0, 1];
	/// assert!(!bv.swap_remove(1));
	/// assert_eq!(bv, bits![0, 1, 1, 0]);
	///
	/// assert!(!bv.swap_remove(0));
	/// assert_eq!(bv, bits![0, 1, 1]);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> bool {
		self.assert_in_bounds(index);
		let last = self.len() - 1;
		unsafe {
			self.swap_unchecked(index, last);
			self.set_len(last);
			*self.get_unchecked(last)
		}
	}

	/// Inserts a bit at position `index` within the vector, shifting all bits
	/// after it to the right.
	///
	/// # Original
	///
	/// [`Vec::insert`](alloc::vec::Vec::insert)
	///
	/// # Panics
	///
	/// Panics if `index > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0; 5];
	/// bv.insert(4, true);
	/// assert_eq!(bv, bits![0, 0, 0, 0, 1, 0]);
	/// bv.insert(2, true);
	/// assert_eq!(bv, bits![0, 0, 1, 0, 0, 1, 0]);
	/// ```
	pub fn insert(&mut self, index: usize, value: bool) {
		let len = self.len();
		assert!(index <= len, "Index {} out of bounds: {}", index, len);
		self.push(value);
		unsafe { self.get_unchecked_mut(index ..) }.rotate_right(1);
	}

	/// Removes and returns the bit at position `index` within the vector,
	/// shifting all bits after it to the left.
	///
	/// # Original
	///
	/// [`Vec::remove`](alloc::vec::Vec::remove)
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 0];
	/// assert!(bv.remove(1));
	/// assert_eq!(bv, bits![0, 0]);
	/// ```
	pub fn remove(&mut self, index: usize) -> bool {
		self.assert_in_bounds(index);
		let last = self.len() - 1;
		unsafe {
			self.get_unchecked_mut(index ..).rotate_left(1);
			self.set_len(last);
			*self.get_unchecked(last)
		}
	}

	/// Retains only the bits specified by the predicate.
	///
	/// In other words, remove all bits `b` such that `func(idx(b), &b)` returns
	/// `false`. This method operates in place, visiting each bit exactly once
	/// in the original order, and preserves the order of the retained bits.
	///
	/// # Original
	///
	/// [`Vec::retain`](alloc::vec::Vec::retain)
	///
	/// # API Differences
	///
	/// In order to allow more than one bit of information for the retention
	/// decision, the predicate receives the index of each bit, as well as its
	/// value.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 1, 0, 0, 1];
	/// bv.retain(|i, b| (i % 2 == 0) ^ b);
	/// assert_eq!(bv, bits![0, 1, 0, 1]);
	/// ```
	pub fn retain<F>(&mut self, mut func: F)
	where F: FnMut(usize, &bool) -> bool {
		for n in (0 .. self.len()).rev() {
			if !func(n, &*unsafe { self.get_unchecked(n) }) {
				self.remove(n);
			}
		}
	}

	/// Appends a bit to the back of a collection.
	///
	/// # Original
	///
	/// [`Vec::push`](alloc::vec::Vec::push)
	///
	/// # Panics
	///
	/// Panics if the number of bits in the vector exceeds the maximum vector
	/// capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0];
	/// bv.push(true);
	/// assert_eq!(bv.count_ones(), 1);
	/// ```
	pub fn push(&mut self, value: bool) {
		let len = self.len();
		assert!(
			len <= BitSlice::<O, T>::MAX_BITS,
			"Exceeded capacity: {} >= {}",
			len,
			BitSlice::<O, T>::MAX_BITS,
		);
		if self.is_empty() || self.bitspan.tail().value() == T::Mem::BITS {
			self.with_vec(|v| v.push(unsafe { mem::zeroed() }));
		}
		unsafe {
			self.set_len_unchecked(len + 1);
			self.set_unchecked(len, value);
		}
	}

	/// Removes the last bit from a vector and returns it, or [`None`] if it is
	/// empty.
	///
	/// # Original
	///
	/// [`Vec::pop`](alloc::vec::Vec::pop)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 1];
	/// assert_eq!(bv.pop(), Some(true));
	/// assert!(bv.not_any());
	/// ```
	///
	/// [`None`]: core::option::Option::None
	pub fn pop(&mut self) -> Option<bool> {
		match self.len() {
			0 => None,
			n => unsafe {
				let new_len = n - 1;
				self.set_len_unchecked(new_len);
				Some(*self.get_unchecked(new_len))
			},
		}
	}

	/// Moves all the bits of `other` into `self`, leaving `other` empty.
	///
	/// # Original
	///
	/// [`Vec::append`](alloc::vec::Vec::append)
	///
	/// # Panics
	///
	/// Panics if the number of bits overflows the maximum vector capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv1 = bitvec![0; 10];
	/// let mut bv2 = bitvec![1; 10];
	///
	/// bv1.append(&mut bv2);
	///
	/// assert_eq!(bv1.count_ones(), 10);
	/// assert!(bv2.is_empty());
	/// ```
	pub fn append<O2, T2>(&mut self, other: &mut BitVec<O2, T2>)
	where
		O2: BitOrder,
		T2: BitStore,
	{
		let this_len = self.len();
		let new_len = this_len + other.len();
		self.resize(new_len, false);
		unsafe { self.get_unchecked_mut(this_len .. new_len) }
			.clone_from_bitslice(other.as_bitslice());
		other.clear();
	}

	/// Creates a draining iterator that removes the specified range in the
	/// vector and yields the removed items.
	///
	/// When the iterator **is** dropped, all bits in the range are removed from
	/// the vector, even if the iterator was not fully consumed. If the iterator
	/// **is not** dropped (with [`mem::forget`] for example), it is unspecified
	/// how many bits are removed.
	///
	/// # Original
	///
	/// [`Vec::drain`](alloc::vec::Vec::drain)
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end
	/// point is greater than the length of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 1];
	/// let bv2: BitVec = bv.drain(1 ..).collect();
	/// assert_eq!(bv, bits![0]);
	/// assert_eq!(bv2, bits![1, 1]);
	///
	/// // A full range clears the vector
	/// bv.drain(..);
	/// assert_eq!(bv, bits![]);
	/// ```
	///
	/// [`mem::forget`]: core::mem::forget
	pub fn drain<R>(&mut self, range: R) -> Drain<O, T>
	where R: RangeBounds<usize> {
		Drain::new(self, range)
	}

	/// Clears the vector, removing all values.
	///
	/// Note that this method has no effect on the contents or allocated
	/// capacity of the vector.
	///
	/// # Original
	///
	/// [`Vec::clear`](alloc::vec::Vec::clear)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 0, 1];
	///
	/// bv.clear();
	///
	/// assert!(bv.is_empty());
	/// ```
	pub fn clear(&mut self) {
		self.bitspan = self.bitspan.address().pipe(BitSpan::uninhabited);
	}

	/// Returns the number of bits in the vector, also referred to as its
	/// ‘length’.
	///
	/// # Original
	///
	/// [`Vec::len`](alloc::vec::Vec::len)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 0];
	/// assert_eq!(a.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		self.bitspan.len()
	}

	/// Returns `true` if the vector contains no bits.
	///
	/// # Original
	///
	/// [`Vec::is_empty`](alloc::vec::Vec::is_empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![];
	/// assert!(bv.is_empty());
	///
	/// bv.push(true);
	/// assert!(!bv.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.bitspan.len() == 0
	}

	/// Splits the collection into two at the given index.
	///
	/// Returns a newly allocated vector containing the elements in range `[at,
	/// len)`. After the call, the original vector will be left containing the
	/// bits `[0, at)` with its previous capacity unchanged.
	///
	/// # Original
	///
	/// [`Vec::split_off`](alloc::vec::Vec::split_off)
	///
	/// # Panics
	///
	/// Panics if `at > len`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 1];
	/// let bv2 = bv.split_off(1);
	/// assert_eq!(bv, bits![0]);
	/// assert_eq!(bv2, bits![0, 1]);
	/// ```
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> Self {
		let len = self.len();
		assert!(at <= len, "Index {} out of bounds: {}", at, len);
		match at {
			0 => mem::replace(self, Self::new()),
			n if n == len => Self::new(),
			_ => unsafe {
				self.set_len(at);
				self.get_unchecked(at .. len)
					.to_bitvec()
					.pipe(Self::strip_unalias)
			},
		}
	}

	/// Resizes the `BitVec` in-place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the `BitVec` is extended by the
	/// difference, with each additional slot filled with the result of calling
	/// the closure `func`. The return values from `func` will end up in the
	/// `BitVec` in the order they have been generated.
	///
	/// If `new_len` is less than `len`, the `BitVec` is simply truncated.
	///
	/// This method uses a closure to create new values on every push. If you’d
	/// rather copy a given bit, use [`.resize()`].
	///
	/// # Original
	///
	/// [`Vec::resize_with`](alloc::vec::Vec::resize_with)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 3];
	/// bv.resize_with(5, Default::default);
	/// assert_eq!(bv, bits![1, 1, 1, 0, 0]);
	///
	/// let mut bv = bitvec![];
	/// let mut p = 0;
	/// bv.resize_with(4, || { p += 1; p % 2 == 0 });
	/// assert_eq!(bv, bits![0, 1, 0, 1]);
	/// ```
	///
	/// [`.resize()`]: Self::resize
	pub fn resize_with<F>(&mut self, new_len: usize, mut func: F)
	where F: FnMut() -> bool {
		let len = self.len();
		if new_len > len {
			let ext = new_len - len;
			self.reserve(ext);
			unsafe {
				self.get_unchecked_mut(len .. new_len)
					.for_each(|_, _| func());
			}
		}
		unsafe {
			self.set_len(new_len);
		}
	}

	/// Consumes and leaks the `BitVec`, returning a mutable reference to the
	/// contents, `&'a mut BitSlice<O, T>`. This lifetime may be chosen to be
	/// `'static`.
	///
	/// This function is similar to the [`leak`] function on [`BitBox`].
	///
	/// This function is mainly useful for data that lives for the remainder of
	/// the program’s life. Dropping the returned reference will cause a memory
	/// leak.
	///
	/// # Original
	///
	/// [`Vec::leak`](alloc::vec::Vec::leak)
	///
	/// # Examples
	///
	/// Simple usage:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let x = bitvec![0, 0, 1];
	/// let static_ref: &'static mut BitSlice = x.leak();
	/// static_ref.set(0, true);
	/// assert_eq!(static_ref, bits![1, 0, 1]);
	/// ```
	///
	/// [`BitBox`]: crate::boxed::BitBox
	/// [`leak`]: crate::boxed::BitBox::leak
	pub fn leak<'a>(self) -> &'a mut BitSlice<O, T> {
		self.pipe(ManuallyDrop::new).bitspan.to_bitslice_mut()
	}

	/// Resizes the `BitVec` in-place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the `BitVec` is extended by the
	/// difference, with each additional slot filled with `value`. If `new_len`
	/// is less than `len`, the `BitVec` is simply truncated.
	///
	/// This method requires a single `bool` value. If you need more
	/// flexibility, use [`.resize_with()`].
	///
	/// # Original
	///
	/// [`Vec::resize`](alloc::vec::Vec::resize)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1];
	/// bv.resize(3, false);
	/// assert_eq!(bv, bits![1, 0, 0]);
	///
	/// let mut bv = bitvec![1; 4];
	/// bv.resize(2, false);
	/// assert_eq!(bv, bits![1; 2]);
	/// ```
	///
	/// [`.resize_with()`]: Self::resize_with
	pub fn resize(&mut self, new_len: usize, value: bool) {
		let len = self.len();
		if new_len > len {
			let ext = new_len - len;
			self.reserve(ext);
			unsafe {
				self.get_unchecked_mut(len .. new_len).set_all(value);
			}
		}
		unsafe {
			self.set_len(new_len);
		}
	}

	/// The name is preserved for API compatibility. See
	/// [`.extend_from_bitslice()`].
	///
	/// [`.extend_from_bitslice()]: Self::extend_from_bitslice
	#[deprecated = "Prefer `.extend()`, or converting your `[bool]` into a \
	                `BitSlice`"]
	pub fn extend_from_slice(&mut self, other: &[bool]) {
		self.extend(other.iter().copied());
	}

	/// Creates a splicing iterator that replaces the specified range in the
	/// vector with the given `replace_with` iterator and yields the removed
	/// items. `replace_with` does not need to be the same length as `range`.
	///
	/// `range` is removed even if the iterator is not consumed until the end.
	///
	/// It is unspecified how many bits are removed from the vector if the
	/// [`Splice`] value is leaked.
	///
	/// The input iterator `replace_with` is only consumed when the [`Splice`]
	/// value is dropped.
	///
	/// This is optimal if:
	///
	/// - the tail (bits in the vector after `range`) is empty
	/// - or `replace_with` yields fewer bits than `range`’s length
	/// - or the lower bound of its [`.size_hint()`] is exact.
	///
	/// Otherwise, a temporary vector is allocated and the tail is moved twice.
	///
	/// # Original
	///
	/// [`Vec::splice`](alloc::vec::Vec::splice)
	///
	/// # Panics
	///
	/// Panics if the starting point is greater than the end point or if the end
	/// point is greater than the length of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 0];
	/// let new = bits![1, 0];
	/// let old: BitVec = bv.splice(.. 2, new.iter().copied()).collect();
	/// assert_eq!(bv, bits![1, 0, 0]);
	/// assert_eq!(old, bits![0, 1]);
	/// ```
	///
	/// [`Splice`]: crate::vec::Splice
	/// [`.size_hint()`]: core::iter::Iterator::size_hint
	pub fn splice<R, I>(
		&mut self,
		range: R,
		replace_with: I,
	) -> Splice<O, T, I::IntoIter>
	where
		R: RangeBounds<usize>,
		I: IntoIterator<Item = bool>,
	{
		Splice::new(self.drain(range), replace_with)
	}
}
