/*! Raw Pointer Representation

This module defines the binary representation of the handle to a `BitSlice`
region. This structure is crate-internal, and defines the methods required to
store a `BitSlice` pointer in memory and retrieve values from it suitable for
work.
!*/

use crate::{
	domain::*,
	indices::{
		BitIdx,
		Indexable,
	},
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	marker::PhantomData,
	mem::size_of,
	ptr::NonNull,
	slice,
};

#[cfg(any(test, feature = "alloc"))]
use crate::indices::BitTail;

/// Width in bits of a pointer on the target machine.
const PTR_BITS: usize = size_of::<*const u8>() * 8;

/** Union to permit reinterpreting a pointer-shaped value as a read pointer,
write pointer, or bare numeric address.

# Safety

Absolutely none whatsoever. This is probably flirting with undefined
behavior, and should be presumed to be the origin site of failure if the
crate ever breaks in the future.

# Type Parameters

- `T`: The referent data type.
**/
#[derive(Clone, Copy)]
#[doc(hidden)]
pub(crate) union Pointer<T>
where T: BitStore {
	/// A shareable pointer to some contended mutable data.
	a: *const <T as BitStore>::Access,
	/// A read pointer to some data.
	r: *const T,
	/// A write pointer to some data.
	w: *mut T,
	/// The pointer address as a bare integer.
	u: usize,
}

impl<T> Pointer<T>
where T: BitStore {
	/// Accesses the address as a shared mutable pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The stored address, interpreted as a shared pointer to a mutable memory
	/// location.
	#[inline]
	pub(crate) fn a(self) -> *const <T as BitStore>::Access {
		unsafe { self.a }
	}

	/// Accesses the address as a read pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The stored address, as a read pointer.
	#[inline]
	pub(crate) fn r(self) -> *const T {
		unsafe { self.r }
	}

	/// Accesses the address as a write pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The stored address, as a write pointer.
	#[inline]
	pub(crate) fn w(self) -> *mut T {
		unsafe { self.w }
	}

	/// Accesses the address as a bare integral value.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The stored address, as a bare integer.
	#[inline]
	pub(crate) fn u(self) -> usize {
		unsafe { self.u }
	}
}

impl<T> From<&T> for Pointer<T>
where T: BitStore {
	fn from(r: &T) -> Self {
		Self { r }
	}
}

impl<T> From<*const T> for Pointer<T>
where T: BitStore {
	fn from(r: *const T) -> Self {
		Self { r }
	}
}

impl<T> From<&mut T> for Pointer<T>
where T: BitStore {
	fn from(w: &mut T) -> Self {
		Self { w }
	}
}

impl<T> From<*mut T> for Pointer<T>
where T: BitStore {
	fn from(w: *mut T) -> Self {
		Self { w }
	}
}

impl<T> From<usize> for Pointer<T>
where T: BitStore {
	fn from(u: usize) -> Self {
		Self { u }
	}
}

/** In-memory representation of `&BitSlice` handles.

# Layout

This structure is a more complex version of the `*const T`/`usize` tuple that
Rust uses to represent slices throughout the language. It breaks the pointer and
counter fundamentals into sub-field components. Rust does not have bitfield
syntax, so the below description of the element layout is in C++.

```cpp
template <typename T>
struct BitPtr {
  size_t ptr_head : __builtin_ctzll(alignof(T));
  size_t ptr_data : sizeof(uintptr_t) * 8
                  - __builtin_ctzll(alignof(T));

  size_t len_head : 3;
  size_t len_bits : sizeof(size_t) * 8 - 3;
};
```

This means that the `BitPtr<T>` structure has three *logical* fields, stored in
four segments across the two *structural* fields of the type. The widths and
placements of each segment are functions of the size of `*const T` and `usize`,
and the alignment of `T`.

# Fields

This section describes the purpose, meaning, and layout of the four logical
fields.

## Data Pointer

Aligned pointers to `T` always have low bits available for use to refine the
address of a `T` to the address of a `u8`. It is stored in the high bits of the
`ptr` field, running from MSb down to (inclusive)
`core::mem::align_of::<T>().trailing_zeros()`.

## Bit Counter

The memory representation stores a counter of the live bits contained in the
slice, starting at the head index. This counter occupies all but the lowest
three bits of the `len` structural field.

## Head Bit Index

For any fundamental type `T`, `core::mem::align_of::<T>().trailing_zeros() + 3`
bits are required to count the bit positions inside it.

|Type |Alignment|Trailing Zeros|Count Bits|
|:----|--------:|-------------:|---------:|
|`u8` |        1|             0|         3|
|`u16`|        2|             1|         4|
|`u32`|        4|             2|         5|
|`u64`|        8|             3|         6|

The head bit counter is split such that its bottom three bits are stored in the
low bits of the `len` field and the remaining high bits are stored in the low
bits of `ptr`.

The counter is a value in the range `0 .. (1 << Count)` that serves as a cursor
into the zeroth storage element to find the first live bit.

# Edge Cases

The following value sets are edge cases of valid `BitPtr` structures.

## Null Slice

The fully zeroed slot is not a valid member of the `BitPtr<T>` type; it is the
sentinel for `Option::<BitPtr<T>>::None`.

## Empty Slice

All empty slices have `0` in their `bits` logical field, and do not constrain
their `data` or `head` logical fields. The canonical empty slice structure uses
`NonNull::<T>::dangling()` as its `data` pointer, and `0` as its `head` index,
but any slice structure with `0` as `bits` is considered to be empty, and all
empty slices are equivalent to each other.

## Uninhabited Slice

The subset of empty slices with non-dangling pointers are considered
uninhabited. All `BitPtr` structures preserve their pointer information, even
when empty, because they may be the owners of the memory region at the pointer.
Uninhabited slices are also unconstrained in their `head` index value.

# Type Parameters

- `T: BitStore` is the storage type over which the pointer governs.

# Safety

A `BitPtr` must never be constructed such that the element addressed by
`self.pointer().offset(self.elements())` causes an addition overflow. This will
be checked in `new()`.

# Undefined Behavior

Using values of this type directly as pointers or counters will result in
undefined behavior. The pointer value will be invalid for the type, and both the
pointer and length values will be invalid for the memory model and allocation
regime.
**/
#[repr(C)]
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct BitPtr<T = u8>
where T: BitStore {
	_ty: PhantomData<T>,
	/// Two-element bitfield structure, holding pointer and head information.
	///
	/// This stores a pointer to the zeroth element of the slice, and the high
	/// bits of the head bit cursor. It is typed as a `NonNull<u8>` in order to
	/// provide null-value optimizations to `Option<BitPtr<T>>`, and because the
	/// presence of head-bit cursor information in the lowest bits means the
	/// bit pattern will not uphold alignment properties assumed by
	/// `NonNull<T>`.
	///
	/// This field cannot be treated as an address of the zeroth byte of the
	/// slice domain, because the owning handle’s [`BitOrder`] implementation
	/// governs the bit pattern of the head cursor.
	///
	/// [`BitOrder`]: ../order/trait.BitOrder.html
	ptr: NonNull<u8>,
	/// Two-element bitfield structure, holding bit-count and head-index
	/// information.
	///
	/// This stores the bit count in its highest bits and the low three bits of
	/// the head `BitIdx` in the lowest three bits.
	///
	/// [`BitIdx`]: ../struct.BitIdx.html
	len: usize,
}

impl<T> BitPtr<T>
where T: BitStore {
	/// Marks the bits of `self.ptr` that are the `data` section.
	pub const PTR_DATA_MASK: usize = !Self::PTR_HEAD_MASK;

	/// The number of low bits in `self.ptr` that are the high bits of the head
	/// `BitIdx` cursor.
	pub const PTR_HEAD_BITS: usize = T::INDX as usize - Self::LEN_HEAD_BITS;

	/// Marks the bits of `self.ptr` that are the `head` section.
	pub const PTR_HEAD_MASK: usize = T::MASK as usize >> Self::LEN_HEAD_BITS;

	/// The number of low bits in `self.len` that are the low bits of the head
	/// `BitIdx` cursor.
	///
	/// This is always `3`, until Rust tries to target a machine whose bytes are
	/// not eight bits wide.
	pub const LEN_HEAD_BITS: usize = 3;

	/// Marks the bits of `self.len` that are the `head` section.
	pub const LEN_HEAD_MASK: usize = 0b0111;

	/// The inclusive maximum number of elements that can be stored in a
	/// `BitPtr` domain.
	pub const MAX_ELTS: usize = (Self::MAX_BITS >> 3) + 1;

	/// The inclusive maximum bit index.
	pub const MAX_BITS: usize = !0 >> Self::LEN_HEAD_BITS;

	/// Produces an empty-slice representation.
	///
	/// This has no live bits, and has a dangling pointer. It is useful as a
	/// default value (and is the function used by `Default`) to indicate
	/// arbitrary empty slices.
	///
	/// # Returns
	///
	/// An uninhabited, uninhabitable, empty slice.
	///
	/// # Safety
	///
	/// The `BitPtr` returned by this function must never be dereferenced.
	pub fn empty() -> Self {
		Self {
			_ty: PhantomData,
			ptr: NonNull::dangling(),
			len: 0,
		}
	}

	/// Produces an uninhabited slice from a bare pointer.
	///
	/// # Parameters
	///
	/// - `ptr`: Some kind of pointer to `T`.
	///
	/// # Returns
	///
	/// If `ptr` is null, then this returns the empty slice; otherwise, the
	/// returned slice is uninhabited and points to the given address.
	///
	/// # Panics
	///
	/// This function panics if the given pointer is not well aligned to its
	/// type.
	///
	/// # Safety
	///
	/// The provided pointer must be either null, or valid in the caller’s
	/// memory model and allocation regime.
	#[cfg(feature = "alloc")]
	pub(crate) fn uninhabited(ptr: impl Into<Pointer<T>>) -> Self {
		let ptr = ptr.into();
		//  Check that the pointer is properly aligned for the storage type.
		//  Null pointers are always well aligned.
		assert!(
			(ptr.u()).trailing_zeros() as usize >= Self::PTR_HEAD_BITS,
			"Pointer {:p} does not satisfy minimum alignment requirements {}",
			ptr.r(),
			Self::PTR_HEAD_BITS,
		);
		Self {
			_ty: PhantomData,
			ptr: NonNull::new(ptr.w() as *mut u8)
				.unwrap_or_else(NonNull::dangling),
			len: 0,
		}
	}

	/// Creates a new `BitPtr` from its components.
	///
	/// # Parameters
	///
	/// - `data`: A well-aligned pointer to a storage element.
	/// - `head`: The bit index of the first live bit in the element under
	///   `*data`.
	/// - `bits`: The number of live bits in the region the produced `BitPtr<T>`
	///   describes.
	///
	/// # Returns
	///
	/// If `data` is the null pointer, then this function produces the canonical
	/// empty slice. If `bits` is `0`, then this function produces an
	/// uninhabited slice at `data`. Otherwise, this produces a `BitPtr<T>`
	/// structure of the region described by the arguments.
	///
	/// # Panics
	///
	/// This function panics in the following events:
	///
	/// - `data` is not well aligned to `T`’s requirements.
	/// - `bits` is larger than `Self::MAX_BITS`.
	/// - `data` and `bits` describe a `[T]` slice which wraps around the edge
	///   of the memory space.
	///
	/// # Safety
	///
	/// The caller must provide a `data` pointer and a `bits` counter which
	/// describe a `[T]` region which is correctly aligned and validly allocated
	/// in the caller’s memory space. The caller is responsible for ensuring
	/// that the slice of memory the produced `BitPtr<T>` describes is all
	/// governable in the caller’s context.
	pub(crate) fn new(
		data: impl Into<Pointer<T>>,
		head: BitIdx<T>,
		bits: usize,
	) -> Self {
		let data = data.into();

		//  Null pointers become the empty slice.
		if data.r().is_null() {
			return Self::empty();
		}

		assert!(
			data.u().trailing_zeros() as usize >= Self::PTR_HEAD_BITS,
			"BitPtr domain pointer ({:p}) to {} must be aligned to at least {}",
			data.r(),
			T::TYPENAME,
			Self::PTR_HEAD_BITS,
		);

		assert!(
			bits <= Self::MAX_BITS,
			"BitPtr cannot address {} bits; the maximum is {}",
			bits,
			Self::MAX_BITS,
		);

		let elts = head.span(bits).0;
		let tail = data.r().wrapping_add(elts);
		assert!(
			tail >= data.r(),
			"BitPtr region cannot wrap the address space: {:p} + {:02X} = {:p}",
			data.r(),
			elts,
			tail,
		);

		unsafe { Self::new_unchecked(data, head, bits) }
	}

	/// Creates a new `BitPtr<T>` from its components, without any validity
	/// checks.
	///
	/// # Safety
	///
	/// ***ABSOLUTELY NONE.*** This function *only* packs its arguments into the
	/// bit pattern of the `BitPtr<T>` type. It should only be used in contexts
	/// where a previously extant `BitPTR<T>` was constructed with ancestry
	/// known to have survived [`::new`], and any manipulations of its raw
	/// components are known to be valid for reconstruction.
	///
	/// # Parameters
	///
	/// See [`::new`].
	///
	/// # Returns
	///
	/// See [`::new`].
	///
	/// [`::new`]: #method.new
	pub(crate) unsafe fn new_unchecked(
		data: impl Into<Pointer<T>>,
		head: BitIdx<T>,
		bits: usize,
	) -> Self {
		let (data, head) = (data.into(), *head as usize);

		let ptr_data = data.u() & Self::PTR_DATA_MASK;
		let ptr_head = head >> Self::LEN_HEAD_BITS;

		let len_head = head & Self::LEN_HEAD_MASK;
		let len_bits = bits << Self::LEN_HEAD_BITS;

		let ptr: Pointer<u8> = (ptr_data | ptr_head).into();

		Self {
			_ty: PhantomData,
			ptr: NonNull::new_unchecked(ptr.w()),
			len: len_bits | len_head,
		}
	}

	/// Extracts the pointer to the first storage element.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A pointer to the first storage element in the slice domain. The concrete
	/// type returned is opaque, and unusable outside this library.
	///
	/// # Safety
	///
	/// This pointer must be valid in the user’s memory model and allocation
	/// regime in order for the caller to dereference it.
	#[inline]
	pub(crate) fn pointer(&self) -> Pointer<T> {
		(self.ptr.as_ptr() as usize & Self::PTR_DATA_MASK).into()
	}

	/// Overwrites the data pointer with a new address. This method does not
	/// perform safety checks on the new pointer.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `ptr: impl Into<Pointer<T>>`: The new address of the `BitPtr<T>`’s
	///   domain.
	///
	/// # Safety
	///
	/// None. The invariants of `::new` must be checked at the caller.
	#[inline]
	#[cfg(feature = "alloc")]
	pub(crate) unsafe fn set_pointer(&mut self, ptr: impl Into<Pointer<T>>) {
		let mut data = ptr.into();
		if data.r().is_null() {
			*self = Self::empty();
			return;
		}
		data.u &= Self::PTR_DATA_MASK;
		data.u |= self.ptr.as_ptr() as usize & Self::PTR_HEAD_MASK;
		self.ptr = NonNull::new_unchecked(data.w() as *mut u8);
	}

	/// Extracts the element cursor of the head bit.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitIdx` that is the index of the first live bit in the first element.
	/// This will be in the domain `0 .. T::BITS`.
	#[inline]
	pub fn head(&self) -> BitIdx<T> {
		let ptr = self.ptr.as_ptr() as usize;
		let ptr_head = (ptr & Self::PTR_HEAD_MASK) << Self::LEN_HEAD_BITS;
		let len_head = self.len & Self::LEN_HEAD_MASK;
		((ptr_head | len_head) as u8).idx()
	}

	#[cfg(feature = "alloc")]
	pub unsafe fn set_head(&mut self, head: BitIdx<T>) {
		let head = *head as usize;
		let mut ptr = self.ptr.as_ptr() as usize;

		//  Erase the head section of the pointer value.
		ptr &= !Self::PTR_HEAD_MASK;
		//  Write the pointer section of the head value into the head section.
		ptr |= head >> Self::LEN_HEAD_BITS;
		self.ptr = NonNull::new_unchecked(ptr as *mut u8);

		//  Erase the head section of the length value.
		self.len &= !Self::LEN_HEAD_MASK;
		//  Write the length section of the head value into the head section.
		self.len |= head & Self::LEN_HEAD_MASK;
	}

	/// Counts how many bits are in the domain of a `BitPtr` slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A count of the live bits in the slice.
	#[inline]
	pub fn len(&self) -> usize {
		self.len >> Self::LEN_HEAD_BITS
	}

	/// Overwrites the bit count with a new counter. This does not perform any
	/// safety checks.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `len: usize`: A new bit length for the `BitPtr<T>`’s domain.
	///
	/// # Safety
	///
	/// None. The caller must ensure that the invariants of `::new` are upheld.
	#[inline]
	pub unsafe fn set_len(&mut self, len: usize) {
		let n = (len << Self::LEN_HEAD_BITS) | (self.len & Self::LEN_HEAD_MASK);
		self.len = n;
	}

	/// Produces the raw components of the pointer structure.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `.0: Pointer<T>`: An opaque pointer to the `BitPtr<T>`’s memory
	///   region.
	/// - `.1: BitIdx`: The index of the first live bit in the bit region.
	/// - `.2: usize`: The number of live bits in the bit region.
	#[inline]
	pub(crate) fn raw_parts(&self) -> (Pointer<T>, BitIdx<T>, usize) {
		(self.pointer(), self.head(), self.len())
	}

	/// Produces the count of all elements in the slice domain.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of `T` elements in the slice domain.
	///
	/// # Safety
	///
	/// This size must be valid in the user’s memory model and allocation
	/// regime.
	pub fn elements(&self) -> usize {
		self.head().span(self.len()).0
	}

	/// Extracts the element cursor of the first dead bit *after* the tail bit.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitTail` that is the index of the first dead bit after the last live
	/// bit in the last element. This will almost always be in the domain
	/// `1 ..= T::BITS`.
	#[cfg(any(test, feature = "alloc"))]
	#[inline]
	pub(crate) fn tail(&self) -> BitTail<T> {
		let (head, len) = (self.head(), self.len());

		if *head == 0 && len == 0 {
			return 0u8.tail();
		}

		//  Compute the in-element tail index as the head plus the length,
		//  modulated to the element width.
		let tail = (*self.head() as usize + len) & T::MASK as usize;
		//  If the tail is zero, wrap it to `T::BITS` as the maximal. This
		//  upshifts `1` (tail is zero) or `0` (tail is not), then sets the
		//  upshift on the rest of the tail, producing something in the range
		//  `1 ..= T::BITS`.
		((((tail == 0) as u8) << T::INDX) | tail as u8).tail()
	}

	/// Accesses the element slice behind the pointer as a Rust slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Standard Rust slice handle over the data governed by this pointer.
	///
	/// # Lifetimes
	///
	/// - `'a`: Lifetime for which the data behind the pointer is live.
	#[inline]
	pub fn as_slice<'a>(&self) -> &'a [T] {
		unsafe { slice::from_raw_parts(self.pointer().r, self.elements()) }
	}

	/// Accesses the element slice behind the pointer as a Rust mutable slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Standard Rust slice handle over the data governed by this pointer.
	///
	/// # Lifetimes
	///
	/// - `'a`: Lifetime for which the data behind the pointer is live.
	#[inline]
	pub fn as_mut_slice<'a>(&self) -> &'a mut [T] {
		unsafe { slice::from_raw_parts_mut(self.pointer().w, self.elements()) }
	}

	/// Accesses the element slice behind the pointer as a shared-mutable slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Standard Rust slice handle over the data governed by this pointer.
	///
	/// # Lifetimes
	///
	/// - `'a`: Lifetime for which the data behind the pointer is live.
	#[inline]
	pub fn as_access_slice<'a>(&self) -> &'a [T::Access] {
		unsafe { slice::from_raw_parts(self.pointer().a, self.elements()) }
	}

	/// Gets the domain for the region the pointer describes.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An enum containing the logical components of the domain governed by
	/// `self`.
	#[inline]
	pub(crate) fn domain<'a>(self) -> BitDomain<'a, T> {
		self.into()
	}

	/// Converts a `BitSlice` handle into its `BitPtr` representation.
	///
	/// # Parameters
	///
	/// - `bs: &BitSlice<O, T>`: a `BitSlice` handle
	///
	/// # Returns
	///
	/// The `BitPtr<T>` structure composing the handle.
	pub(crate) fn from_bitslice<O>(bs: &BitSlice<O, T>) -> Self
	where O: BitOrder {
		let src = unsafe { &*(bs as *const BitSlice<O, T> as *const [()]) };
		let ptr = Pointer::from(src.as_ptr() as *const u8);
		let (ptr, len) = match (ptr.w(), src.len()) {
			(_, 0) => (NonNull::dangling(), 0),
			(p, _) if p.is_null() => unreachable!("Rust forbids null refs"),
			(p, l) => (unsafe { NonNull::new_unchecked(p) }, l),
		};
		Self { ptr, len, _ty: PhantomData }
	}

	/// Converts a `BitPtr` structure into an immutable `BitSlice` handle.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle composed of the `BitPtr` structure.
	pub(crate) fn into_bitslice<'a, O>(self) -> &'a BitSlice<O, T>
	where O: BitOrder {
		unsafe {
			&*(slice::from_raw_parts(
				Pointer::from(self.ptr.as_ptr()).r() as *const (),
				self.len,
			) as *const [()] as *const BitSlice<O, T>)
		}
	}

	/// Converts a `BitPtr` structure into a mutable `BitSlice` handle.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle composed of the `BitPtr` structure.
	pub(crate) fn into_bitslice_mut<'a, O>(self) -> &'a mut BitSlice<O, T>
	where O: BitOrder {
		unsafe {
			&mut *(slice::from_raw_parts_mut(
				Pointer::from(self.ptr.as_ptr()).w() as *mut (),
				self.len,
			) as *mut [()] as *mut BitSlice<O, T>)
		}
	}

	/// Cast a `BitPtr<T>` into an equivalent `*mut BitSlice<O, T>`.
	#[cfg(feature = "alloc")]
	pub(crate) fn as_mut_ptr<O>(self) -> *mut BitSlice<O, T>
	where O: BitOrder {
		self.into_bitslice_mut() as *mut BitSlice<O, T>
	}

	/// Cast a `*mut BitSlice<O, T>` raw pointer into an equivalent `BitPtr<T>`.
	#[cfg(feature = "alloc")]
	pub(crate) fn from_mut_ptr<O>(ptr: *mut BitSlice<O, T>) -> Self
	where O: BitOrder {
		unsafe { &*ptr }.bitptr()
	}
}

/** Gets write access to all elements in the underlying storage, including the
partial head and tail elements.

# Safety

This is *unsafe* to use except from known mutable `BitSlice` structures.
Mutability is not encoded in the `BitPtr` type system at this time, and thus is
not enforced by the compiler yet.
**/
impl<T> AsMut<[T]> for BitPtr<T>
where T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Gets read access to all elements in the underlying storage, including the
/// partial head and tail elements.
impl<T> AsRef<[T]> for BitPtr<T>
where T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<'a, O, T> From<&'a BitSlice<O, T>> for BitPtr<T>
where O: BitOrder, T: 'a + BitStore {
	fn from(src: &'a BitSlice<O, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<'a, O, T> From<&'a mut BitSlice<O, T>> for BitPtr<T>
where O: BitOrder, T: 'a + BitStore {
	fn from(src: &'a mut BitSlice<O, T>) -> Self {
		Self::from_bitslice(src)
	}
}

/// Produces the empty-slice representation.
impl<T> Default for BitPtr<T>
where T: BitStore {
	/// Produces an empty-slice representation.
	///
	/// The empty slice has no size or cursors, and its pointer is the alignment
	/// of the type. The non-null pointer allows this structure to be null-value
	/// optimized.
	fn default() -> Self {
		Self::empty()
	}
}

/// Prints the `BitPtr` data structure for debugging.
impl<T> Debug for BitPtr<T>
where T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		struct HexPtr<T: BitStore>(*const T);
		impl<T: BitStore> Debug for HexPtr<T> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				write!(f, "0x{:0>1$X}", self.0 as usize, PTR_BITS >> 2)
			}
		}

		struct BinAddr<T: BitStore>(BitIdx<T>);
		impl<T: BitStore> Debug for BinAddr<T> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				write!(f, "0b{:0>1$b}", *self.0, T::INDX as usize)
			}
		}

		write!(f, "BitPtr<{}>", T::TYPENAME)?;
		f.debug_struct("")
			.field("data", &HexPtr::<T>(self.pointer().r()))
			.field("head", &BinAddr::<T>(self.head()))
			.field("bits", &self.len())
			.finish()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn associated_consts_u8() {
		assert_eq!(BitPtr::<u8>::PTR_HEAD_BITS, 0);

		assert_eq!(BitPtr::<u8>::PTR_DATA_MASK, !0);
		assert_eq!(BitPtr::<u8>::PTR_HEAD_MASK, 0);
	}

	#[test]
	fn associated_consts_u16() {
		assert_eq!(BitPtr::<u16>::PTR_HEAD_BITS, 1);

		assert_eq!(BitPtr::<u16>::PTR_DATA_MASK, !0 << 1);
		assert_eq!(BitPtr::<u16>::PTR_HEAD_MASK, 1);
	}

	#[test]
	fn associated_consts_u32() {
		assert_eq!(BitPtr::<u32>::PTR_HEAD_BITS, 2);

		assert_eq!(BitPtr::<u32>::PTR_DATA_MASK, !0 << 2);
		assert_eq!(BitPtr::<u32>::PTR_HEAD_MASK, 3);
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn associated_consts_u64() {
		assert_eq!(BitPtr::<u64>::PTR_HEAD_BITS, 3);

		assert_eq!(BitPtr::<u64>::PTR_DATA_MASK, !0 << 3);
		assert_eq!(BitPtr::<u64>::PTR_HEAD_MASK, 7);
	}

	#[test]
	fn ctors() {
		let data: [u32; 4] = [0; 4];
		let bp = BitPtr::<u32>::new(&data as *const u32, 0u8.idx(), 32 * 4);
		assert_eq!(bp.pointer().r(), &data as *const u32);
		assert_eq!(bp.elements(), 4);
		assert_eq!(*bp.head(), 0);
		assert_eq!(*bp.tail(), 32);
	}

	#[test]
	fn empty() {
		let data = [0u8; 4];
		//  anything with 0 bits is unconditionally empty
		let bp = BitPtr::<u8>::new(&data as *const u8, 2u8.idx(), 0);

		assert_eq!(bp.len(), 0);
		assert_eq!(*bp.head(), 2);
		assert_eq!(*bp.tail(), 2);
	}

	#[cfg(not(miri))]
	#[test]
	#[should_panic]
	fn overfull() {
		BitPtr::<u32>::new(8 as *const u32, 1u8.idx(), BitPtr::<u32>::MAX_BITS + 1);
	}
}
