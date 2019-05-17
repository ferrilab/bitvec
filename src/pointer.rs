/*! Raw Pointer Representation

This module defines the binary representation of the handle to a `BitSlice`
region. This structure is crate-internal, and defines the methods required to
store a `BitSlice` pointer in memory and retrieve values from it suitable for
work.
!*/

use crate::{
	bits::{
		BitIdx,
		Bits,
	},
	cursor::Cursor,
	domain::*,
	slice::BitSlice,
};

use core::{
	convert::{
		AsMut,
		AsRef,
		From,
	},
	default::Default,
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

/// Width in bits of a pointer on the target machine.
const PTR_BITS: usize = size_of::<*const u8>() * 8;

/// Width in bits of a processor word on the target machine.
const USZ_BITS: usize = size_of::<usize>() * 8;

/// Union to permit reinterpreting a pointer-shaped value as a read pointer,
/// write pointer, or bare numeric address.
///
/// # Safety
///
/// Absolutely none whatsoever. This is probably flirting with undefined
/// behavior, and should be presumed to be the origin site of failure if the
/// crate ever breaks in the future.
///
/// # Type Parameters
///
/// - `T`: The referent data type.
///
/// # Usage
///
/// Don’t.
#[doc(hidden)]
pub union Pointer<T> {
	/// A read pointer to some data.
	r: *const T,
	/// A write pointer to some data.
	w: *mut T,
	/// The pointer address as a bare integer.
	u: usize,
}

impl<T> Pointer<T> {
	/// Accesses the address as a read pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The stored address, as a read pointer.
	pub(crate) fn r(&self) -> *const T {
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
	pub(crate) fn w(&self) -> *mut T {
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
	pub(crate) fn u(&self) -> usize {
		unsafe { self.u }
	}
}

impl<T> From<&T> for Pointer<T> {
	fn from(r: &T) -> Self {
		Self { r }
	}
}

impl<T> From<*const T> for Pointer<T> {
	fn from(r: *const T) -> Self {
		Self { r }
	}
}

impl<T> From<&mut T> for Pointer<T> {
	fn from(w: &mut T) -> Self {
		Self { w }
	}
}

impl<T> From<*mut T> for Pointer<T> {
	fn from(w: *mut T) -> Self {
		Self { w }
	}
}

impl<T> From<usize> for Pointer<T> {
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
  size_t ptr_data : sizeof(T*) * 8
                  - __builtin_ctzll(alignof(T));

  size_t len_head : 3;
  size_t len_tail : 3
                  + __builtin_ctzll(alignof(T));
  size_t len_elts : sizeof(size_t) * 8
                  - 6
                  - __builtin_ctzll(alignof(T));
};
```

This means that the `BitPtr<T>` structure has four *logical* fields, stored in
five segments across the two *structural* fields of the type. The widths and
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

## Element Counter

The memory representation stores counters that run from
`1 ... (Self::MAX_ELTS)`, where the bit pattern is `n - 1` when `n` is the true
number of elements in the slice’s domain. It is stored in the high bits of the
`len` field, running from `MSb` down to (inclusive)
`core::mem::align_of::<T>().trailing_zeros() + 6`.

## Head Bit Counter

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

## Tail Bit Counter

This counter is the same bit width as the head bit counter. It is stored
contiguously in the middle section of the `len` field, running from (exclusive)
`core::mem::align_of::<T>().trailing_zeros() + 6` down to (inclusive) `3`. The
value in it is a cursor to the next bit *after* the last live bit of the slice.

The tail bit counter and the element counter operate together; when the tail bit
counter is `0`, then the element counter is also incremented to cover the next
element *after* the last live element in the slice domain.

# Edge Cases

The following value sets are edge cases of valid `BitPtr` structures.

## Empty Slice

The empty slice has all its fields zeroed except for the data pointer, which is
any non-null pointer. The null pointer value is used to indicate
`Option::<BitPtr<T>::None`.

## Allocated, Uninhabited, Slice

An allocated, owned, region of memory that is uninhabited. This is functionally
the empty slice, but it must retain its pointer information. All other fields in
the slot are zeroed.

- `data`: (any valid `*const T` other than `NonNull::<T>::dangling()`)
- `elts`: `0usize`
- `head`: `0u8`
- `tail`: `0u8`
- `ptr`: (any valid `*const u8`)
- `len`: `0usize`

## Maximum Elements, Maximum Tail

This, unfortunately, cannot be represented. The largest domain that can be
represented has `elts` and `tail` of `!0`, which leaves the last bit in the
element unavailable.

# Type Parameters

- `T: Bits` is the storage type over which the pointer governs.

# Safety

A `BitPtr` must never be constructed such that the element addressed by
`self.pointer().offset(self.elements())` causes an addition overflow. This will
be checked in `new()`.

A `BitPtr` must never be constructed such that the tail bit is lower in memory
than the head bit. This will be checked in `new()`.

# Undefined Behavior

Using values of this type directly as pointers or counters will result in
undefined behavior. The pointer value will be invalid for the type, and both the
pointer and length values will be invalid for the memory model and allocation
regime.
**/
#[repr(C)]
#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct BitPtr<T = u8>
where T: Bits {
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
	/// slice domain, because the owning handle’s [`Cursor`] implementation
	/// governs the bit pattern of the head cursor.
	///
	/// [`Cursor`]: ../trait.Cursor.html
	ptr: NonNull<u8>,
	/// Three-element bitfield structure, holding length and place information.
	///
	/// This stores the element count in its highest bits, the tail [`BitIdx`]
	/// cursor in the middle segment, and the low three bits of the head
	/// `BitIdx` in the lowest three bits.
	///
	/// [`BitIdx`]: ../struct.BitIdx.html
	len: usize,
}

impl<T> BitPtr<T>
where T: Bits {
	/// The number of high bits in `self.ptr` that are actually the address of
	/// the zeroth `T`.
	pub const PTR_DATA_BITS: usize = PTR_BITS - Self::PTR_HEAD_BITS;

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

	/// The number of middle bits in `self.len` that are the tail `BitIdx`
	/// cursor.
	pub const LEN_TAIL_BITS: usize = T::INDX as usize;

	/// Marks the bits of `self.len` that are the `tail` section.
	pub const LEN_TAIL_MASK: usize = (T::MASK as usize) << Self::LEN_HEAD_BITS;

	/// The number of high bits in `self.len` that are used to count `T`
	/// elements in the slice.
	pub const LEN_ELTS_BITS: usize = USZ_BITS - Self::LEN_INDX_BITS;

	/// Marks the bits of `self.len` that are the `data` section.
	pub const LEN_ELTS_MASK: usize = !Self::LEN_INDX_MASK;

	/// The number of bits occupied by the `tail` `BitIdx` and the low 3 bits of
	/// `head`.
	pub const LEN_INDX_BITS: usize = Self::LEN_TAIL_BITS + Self::LEN_HEAD_BITS;

	/// Marks the bits of `self.len` that are either `tail` or `head`.
	pub const LEN_INDX_MASK: usize = Self::LEN_TAIL_MASK | Self::LEN_HEAD_MASK;

	/// The inclusive maximum number of elements that can be stored in a
	/// `BitPtr` domain.
	pub const MAX_ELTS: usize = 1 << Self::LEN_ELTS_BITS;

	/// The inclusive maximum number of bits that can be stored in a `BitPtr`
	/// domain.
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
	pub fn uninhabited(ptr: impl Into<Pointer<T>>) -> Self {
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
	/// - `data`: A well-aligned pointer to a storage element. If this is null,
	///   then the empty-slice representation is returned, regardless of other
	///   argument values.
	/// - `elts`: A number of storage elements in the domain of the new
	///   `BitPtr`. This number must be in `0 ..= Self::MAX_ELTS`. If it is
	///   zero, then the empty-slice representation is returned, regardless of
	///   other argument values.
	/// - `head`: The bit index of the first live bit in the domain. This must
	///   be in the domain `0 .. T::BITS`.
	/// - `tail`: The bit index of the first dead bit after the domain. This
	///   must be:
	///   - zero, when and only when `elts` and `head` are also zero.
	///   - equal to `head` when `elts` is `1`, to create an empty slice.
	///   - in `head + 1 ..= T::BITS` when `elts` is `1` to create a
	///     single-element slice.
	///   - in `1 ..= T::BITS` when `elts` is greater than `1`.
	///   - in `1 .. T::BITS` when `elts` is `Self::MAX_ELTS`.
	///
	/// # Returns
	///
	/// If any of the following conditions are true, then an empty slice is
	/// returned:
	///
	/// - `data` is the null pointer,
	/// - `elts` is `0`,
	/// - `elts` is `1` **and** `head` is equal to `tail`.
	///
	/// Otherwise, a `BitPtr` structure representing the given domain is
	/// returned.
	///
	/// # Panics
	///
	/// This function happily panics at the slightest whiff of impropriety.
	///
	/// - If the `data` pointer is not aligned to at least the type `T`,
	/// - If the `elts` counter is not within the countable elements domain,
	///   `0 ..= Self::MAX_ELTS`,
	/// - If the `data` pointer is so high in the address space that addressing
	///   the last element would cause the pointer to wrap,
	/// - If `head` or `tail` are too large for indexing bits within `T`,
	/// - If `tail` is not correctly placed relative to `head`.
	///
	/// # Safety
	///
	/// The `data` pointer and `elts` counter must describe a correctly aligned,
	/// validly allocated, region of memory, or the canonical dangling pointer
	/// and empty slice. The caller is responsible for ensuring that the slice
	/// of memory that the new `BitPtr` will govern is all governable.
	pub fn new(
		data: impl Into<Pointer<T>>,
		elts: usize,
		head: impl Into<BitIdx>,
		tail: impl Into<BitIdx>,
	) -> Self {
		let (data, head, tail) = (data.into(), head.into(), tail.into());

		//  null pointers, and pointers to empty regions, are run through the
		//  uninhabited constructor instead
		if data.r().is_null() || elts == 0 || (elts == 1 && head == tail) {
			return Self::uninhabited(data);
		}

		//  Check that the pointer is properly aligned for the storage type.
		assert!(
			(data.u()).trailing_zeros() as usize >= Self::PTR_HEAD_BITS,
			"BitPtr domain pointers must be well aligned",
		);

		//  Check that the slice domain is below the ceiling.
		assert!(
			elts <= Self::MAX_ELTS,
			"{} is outside the element count domain 1 ..= {}",
			elts,
			Self::MAX_ELTS,
		);

		//  Check that the head cursor index is within the storage element.
		assert!(
			head.is_valid::<T>(),
			"{} is outside the head domain 0 .. {}",
			head,
			T::BITS,
		);

		//  Check that the tail cursor index is in the appropriate domain.
		assert!(
			tail.is_valid_tail::<T>(),
			"{} is outside the tail domain 1 ..= {}",
			tail,
			T::BITS,
		);

		//  For single-element slices, check that the tail cursor is after the
		//  head cursor (single-element, head == tail, is checked above).
		if elts == 1 {
			assert!(
				tail > head,
				"BitPtr domains with one element must have the tail cursor \
				beyond the head cursor",
			);
		}
		else if elts == Self::MAX_ELTS {
			assert!(
				tail.is_valid::<T>(),
				"BitPtr domains with maximum elements must have the tail ({}) \
				cursor in 1 .. {}",
				tail,
				T::BITS,
			);
		}

		unsafe { Self::new_unchecked(data, elts, head, tail) }
	}

	/// Creates a new `BitPtr<T>` from its components, without validity checks.
	///
	/// # Safety
	///
	/// ***NONE.*** This function *only* packs its parameters into the bit
	/// pattern of the `BitPtr<T>` type. It should only be used in contexts
	/// where a previously extant `BitPtr<T>` was constructed via `new`, and
	/// its `raw_parts()` components are known to be valid for reconstruction.
	///
	/// This is a bypass for the validity checks, and can only be used when
	/// the checks are statically known to still be in force.
	///
	/// # Parameters
	///
	/// Same as [`::new`], except `head` and `tail` are concretely `BitIdx`.
	///
	/// # Returns
	///
	/// See `::new`.
	///
	/// [`::new`]: #method.new
	pub(crate) unsafe fn new_unchecked(
		data: impl Into<Pointer<T>>,
		elts: usize,
		head: BitIdx,
		tail: BitIdx,
	) -> Self {
		let data = data.into();
		let sum = data.r().wrapping_add(elts);
		//  This check cannot ever be elided. Check that the pointer is not so
		//  high in the address space that the slice domain wraps.
		assert!(
			sum >= data.r(),
			"The region overflows the address space: {:p} + {:02X} is {:p}",
			data.r(),
			elts,
			sum,
		);

		let ptr_data = data.u & Self::PTR_DATA_MASK;
		let ptr_head = *head as usize >> Self::LEN_HEAD_BITS;

		//  If `tail` is not maximal, it will be wrapped to zero, and `elts`
		//  will be incremented. Since `elts` is about to be unconditionally
		//  decremented, the equivalent behavior is to not increment, and
		//  decrement only if `tail` is not maximal.
		let len_elts = elts.saturating_sub((*tail < T::BITS) as usize)
			<< Self::LEN_INDX_BITS;

		//  Store tail. Note that this wraps `T::BITS` to 0. This must be
		//  reconstructed during retrieval.
		let len_tail
			= ((*tail as usize) << Self::LEN_HEAD_BITS)
			& Self::LEN_TAIL_MASK;
		let len_head = *head as usize & Self::LEN_HEAD_MASK;

		Self {
			_ty: PhantomData,
			ptr: NonNull::new_unchecked((ptr_data | ptr_head) as *mut u8),
			len: len_elts | len_tail | len_head,
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
	pub fn pointer(&self) -> Pointer<T> {
		(self.ptr.as_ptr() as usize & Self::PTR_DATA_MASK).into()
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
		//  Count the elements as marked in the elts field, adding one unless
		//  the tail is `T::BITS` or `0`.
		let tail_bits = self.len & Self::LEN_TAIL_MASK;
		let incr = tail_bits != 0;
		(self.len >> Self::LEN_INDX_BITS) + incr as usize
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
	pub fn head(&self) -> BitIdx {
		let ptr = self.ptr.as_ptr() as usize & Self::PTR_HEAD_MASK;
		let ptr = ptr << Self::LEN_HEAD_BITS;
		let len = self.len & Self::LEN_HEAD_MASK;
		((ptr | len) as u8).into()
	}

	/// Extracts the element cursor of the first dead bit *after* the tail bit.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitIdx` that is the index of the first dead bit after the last live
	/// bit in the last element. This will be in the domain `1 ..= T::BITS`.
	pub fn tail(&self) -> BitIdx {
		/* This function is one of the most-used in the library. As such, its
		 * implementation is written in a straight linear style. The compiler is
		 * free to rearrange the code as it sees fit, and may not reflect the
		 * code below. The equivalent, user-friendly function body is:

		if self.is_empty() {
			return 0.into();
		}
		let bits = (self.len & Self::LEN_TAIL_MASK) >> Self::LEN_HEAD_BITS;
		if bits == 0 { T::BITS } else { bits as u8 }.into()
		 */

		//  The tail is stored in the LEN_TAIL_MASK region.
		let bits = (self.len & Self::LEN_TAIL_MASK) >> Self::LEN_HEAD_BITS;
		(
			//  Becomes 0 when the slice is empty, and !0 when not. This clamps
			//  the tail to 0 on the empty slice, or itself on non-empty.
			//  `0 & rhs` is always `0`, `!0 & rhs` is always `rhs`.
			(self.is_empty() as u8).wrapping_sub(1) &
			//  If the tail’s bit pattern is zero, wrap it to the maximal. This
			//  upshifts `1` (pattern is zero) or `0` (pattern is not), then
			//  sets the upshift bit on the pattern.
			((((bits == 0) as u8) << T::INDX) | bits as u8)
		).into()
	}

	/// Decomposes the pointer into raw components.
	///
	/// The values returned from this can be immediately passed into `::new` or
	/// `::new_unchecked` in order to rebuild the pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `Pointer<T>`: A well aligned pointer to the first element of the slice.
	/// - `usize`: The number of elements in the slice.
	/// - `BitIdx`: The index of the first live bit in the first element.
	/// - `BitIdx`: The index of the first dead bit in the last element.
	pub fn raw_parts(&self) -> (Pointer<T>, usize, BitIdx, BitIdx) {
		(self.pointer(), self.elements(), self.head(), self.tail())
	}

	/// Produces the element count, head index, and tail index, which describe
	/// the region.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The number of elements in the slice.
	/// - `BitIdx`: The index of the first live bit in the first element.
	/// - `BitIdx`: The index of the first dead bit in the last element.
	pub fn region_data(&self) -> (usize, BitIdx, BitIdx) {
		(self.elements(), self.head(), self.tail())
	}

	/// Produces the head and tail indices for the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `BitIdx`: The index of the first live bit in the first element.
	/// - `BitIdx`: The index of the first dead bit in the last element.
	pub fn cursors(&self) -> (BitIdx, BitIdx) {
		(self.head(), self.tail())
	}

	/// Checks if the pointer represents the empty slice.
	///
	/// The empty slice has a dangling `data` pointer and zeroed `elts`, `head`,
	/// and `tail` elements.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether the slice is empty or inhabited.
	pub fn is_empty(&self) -> bool {
		self.len == 0 && self.ptr.as_ptr() as usize & Self::PTR_HEAD_MASK == 0
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
	pub fn len(&self) -> usize {
		let (elts, head, tail) = self.region_data();
		match elts {
			0 => 0,
			1 => (*tail - *head) as usize,
			//  The number of bits in a domain is calculated by decrementing
			//  `elts`, multiplying it by the number of bits per element, then
			//  subtracting `head` (which is the number of dead bits in the
			//  front of the first element), and adding `tail` (which is the
			//  number of live bits in the front of the last element).
			e => ((e - 1) << T::INDX) + (*tail as usize) - (*head as usize),
		}
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
	pub fn as_mut_slice<'a>(&self) -> &'a mut [T] {
		unsafe { slice::from_raw_parts_mut(self.pointer().w, self.elements()) }
	}

	/// Gets the domain kind for the region the pointer describes.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An enum describing the live bits in the region the pointer covers.
	pub fn domain_kind(&self) -> BitDomainKind {
		self.into()
	}

	/// Gets the domain for the region the pointer describes.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An enum containing the logical components of the domain governed by
	/// `self`.
	pub fn domain(&self) -> BitDomain<T> {
		(*self).into()
	}

	/// Gets the domain for the region the pointer describes.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An enum containing the logical components of the domain governed by
	/// `self`.
	pub fn domain_mut(&self) -> BitDomainMut<T> {
		(*self).into()
	}

	/// Moves the `head` cursor upwards by one.
	///
	/// If `head` is at the back edge of the first element, then it will be set
	/// to the front edge of the second element, and the pointer will be moved
	/// upwards.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Safety
	///
	/// This method is unsafe when `self` is directly, solely, managing owned
	/// memory. It mutates the pointer and element count, so if this pointer is
	/// solely responsible for owned memory, its conception of the allocation
	/// will differ from the allocator’s.
	pub unsafe fn incr_head(&mut self) {
		match self.len() {
			//  Do nothing when empty
			0 => {},
			//  Become the uninhabited slice when the last bit is removed
			1 => *self = Self::uninhabited(self.pointer()),
			_ => {
				let (data, elts, head, tail) = self.raw_parts();
				let (h, wrap) = head.incr::<T>();
				if wrap {
					*self = Self::new_unchecked(
						data.r().offset(1),
						elts.saturating_sub(1),
						h,
						tail,
					);
				}
				else {
					*self = Self::new_unchecked(data, elts, h, tail);
				}
			},
		}
	}

	/// Moves the `head` cursor downwards by one.
	///
	/// If `head` is at the front edge of the first element, then it will be set
	/// to the back edge of the zeroth element, and the pointer will be moved
	/// downwards.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Safety
	///
	/// This function is unsafe when `self` is directly, solely, managing owned
	/// memory. It mutates the pointer and element count, so if this pointer is
	/// solely responsible for owned memory, its conception of the allocation
	/// will differ from the allocator’s.
	pub unsafe fn decr_head(&mut self) {
		//  Empty slices cannot be modified in this way
		if self.is_empty() {
			return;
		}
		let (data, elts, head, tail) = self.raw_parts();
		let (h, wrap) = head.decr::<T>();
		if wrap {
			*self = Self::new_unchecked(
				data.r().offset(-1),
				elts.saturating_add(1),
				h,
				tail,
			);
		}
		else {
			*self = Self::new_unchecked(data, elts, h, tail);
		}
	}

	/// Moves the `tail` cursor upwards by one.
	///
	/// If `tail` is at the back edge of the last element, then it will be set
	/// to the front edge of the next element beyond, and the element count will
	/// be increased.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Safety
	///
	/// This function is unsafe when `self` is directly, solely, managing owned
	/// memory. It mutates the element count, so if this pointer is solely
	/// responsible for owned memory, its conception of the allocation will
	/// differ from the allocator’s.
	pub unsafe fn incr_tail(&mut self) {
		//  Fully extended slices cannot have their tail increased.
		if self.len | Self::LEN_HEAD_MASK == !0 {
			return;
		}
		let (data, elts, head, tail) = self.raw_parts();
		let (t, wrap) = tail.incr_tail::<T>();
		*self = Self::new_unchecked(
			data,
			elts.saturating_add(wrap as usize),
			head,
			t,
		);
	}

	/// Moves the `tail` cursor downwards by one.
	///
	/// If `tail` is at the front edge of the back element, then it will be set
	/// to the back edge of the next element forward, and the element count will
	/// be decreased.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Safety
	///
	/// This function is unsafe when `self` is directly, solely, managing owned
	/// memory. It mutates the element count, so if this pointer is solely
	/// responsible for owned memory, its conception of the allocation will
	/// differ from the allocator’s.
	pub unsafe fn decr_tail(&mut self) {
		match self.len() {
			//  Empty slices cannot have their tail decremented
			0 => return,
			//  One-bit slices become uninhabited
			1 => *self = Self::uninhabited(self.pointer()),
			_ => {
				let (data, elts, head, tail) = self.raw_parts();
				let (t, wrap) = tail.decr_tail::<T>();
				*self = Self::new_unchecked(
					data,
					elts.saturating_sub(wrap as usize),
					head,
					t,
				);
			},
		}
	}

	/// Converts a `BitSlice` handle into its `BitPtr` representation.
	///
	/// # Parameters
	///
	/// - `bs: &BitSlice<C, T>`: a `BitSlice` handle
	///
	/// # Returns
	///
	/// The `BitPtr<T>` structure composing the handle.
	pub(crate) fn from_bitslice<C>(bs: &BitSlice<C, T>) -> Self
	where C: Cursor {
		let src = unsafe { &*(bs as *const BitSlice<C, T> as *const [()]) };
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
	pub(crate) fn into_bitslice<'a, C>(self) -> &'a BitSlice<C, T>
	where C: Cursor {
		unsafe {
			&*(slice::from_raw_parts(
				self.ptr.as_ptr() as *const u8 as *const (),
				self.len,
			) as *const [()] as *const BitSlice<C, T>)
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
	pub(crate) fn into_bitslice_mut<'a, C>(self) -> &'a mut BitSlice<C, T>
	where C: Cursor {
		unsafe {
			&mut *(slice::from_raw_parts_mut(
				Pointer::from(self.ptr.as_ptr()).w() as *mut (),
				self.len,
			) as *mut [()] as *mut BitSlice<C, T>)
		}
	}
}

/// Gets write access to all elements in the underlying storage, including the
/// partial head and tail elements.
///
/// # Safety
///
/// This is *unsafe* to use except from known mutable `BitSlice` structures.
/// Mutability is not encoded in the `BitPtr` type system at this time, and thus
/// is not enforced by the compiler yet.
impl<T> AsMut<[T]> for BitPtr<T>
where T: Bits {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Gets read access to all elements in the underlying storage, including the
/// partial head and tail elements.
impl<T> AsRef<[T]> for BitPtr<T>
where T: Bits {
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<'a, C, T> From<&'a BitSlice<C, T>> for BitPtr<T>
where C: Cursor, T: 'a + Bits {
	fn from(src: &'a BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<'a, C, T> From<&'a mut BitSlice<C, T>> for BitPtr<T>
where C: Cursor, T: 'a + Bits {
	fn from(src: &'a mut BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

/// Produces the empty-slice representation.
impl<T> Default for BitPtr<T>
where T: Bits {
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
where T: Bits {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		struct HexPtr<T: Bits>(*const T);
		impl<T: Bits> Debug for HexPtr<T> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.write_fmt(format_args!("0x{:0>1$X}", self.0 as usize, PTR_BITS >> 2))
			}
		}
		struct HexAddr(usize);
		impl Debug for HexAddr {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.write_fmt(format_args!("{:#X}", self.0))
			}
		}
		struct BinAddr<T: Bits>(BitIdx, PhantomData<T>);
		impl<T: Bits>  Debug for BinAddr<T> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.write_fmt(format_args!("0b{:0>1$b}", *self.0, T::INDX as usize))
			}
		}
		write!(f, "BitPtr<{}>", T::TYPENAME)?;
		f.debug_struct("")
			.field("data", &HexPtr::<T>(self.pointer().r()))
			.field("elts", &HexAddr(self.elements()))
			.field("head", &BinAddr::<T>(self.head(), PhantomData))
			.field("tail", &BinAddr::<T>(self.tail(), PhantomData))
			.finish()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn associated_consts_u8() {
		assert_eq!(BitPtr::<u8>::PTR_DATA_BITS, PTR_BITS);
		assert_eq!(BitPtr::<u8>::PTR_HEAD_BITS, 0);
		assert_eq!(BitPtr::<u8>::LEN_ELTS_BITS, USZ_BITS - 6);
		assert_eq!(BitPtr::<u8>::LEN_TAIL_BITS, 3);

		assert_eq!(BitPtr::<u8>::PTR_DATA_MASK, !0);
		assert_eq!(BitPtr::<u8>::PTR_HEAD_MASK, 0);
		assert_eq!(BitPtr::<u8>::LEN_ELTS_MASK, !0 << 6);
		assert_eq!(BitPtr::<u8>::LEN_TAIL_MASK, 7 << 3);
		assert_eq!(BitPtr::<u8>::LEN_INDX_MASK, 63);
	}

	#[test]
	fn associated_consts_u16() {
		assert_eq!(BitPtr::<u16>::PTR_DATA_BITS, PTR_BITS - 1);
		assert_eq!(BitPtr::<u16>::PTR_HEAD_BITS, 1);
		assert_eq!(BitPtr::<u16>::LEN_ELTS_BITS, USZ_BITS - 7);
		assert_eq!(BitPtr::<u16>::LEN_TAIL_BITS, 4);

		assert_eq!(BitPtr::<u16>::PTR_DATA_MASK, !0 << 1);
		assert_eq!(BitPtr::<u16>::PTR_HEAD_MASK, 1);
		assert_eq!(BitPtr::<u16>::LEN_ELTS_MASK, !0 << 7);
		assert_eq!(BitPtr::<u16>::LEN_TAIL_MASK, 15 << 3);
		assert_eq!(BitPtr::<u16>::LEN_INDX_MASK, 127);
	}

	#[test]
	fn associated_consts_u32() {
		assert_eq!(BitPtr::<u32>::PTR_DATA_BITS, PTR_BITS - 2);
		assert_eq!(BitPtr::<u32>::PTR_HEAD_BITS, 2);
		assert_eq!(BitPtr::<u32>::LEN_ELTS_BITS, USZ_BITS - 8);
		assert_eq!(BitPtr::<u32>::LEN_TAIL_BITS, 5);

		assert_eq!(BitPtr::<u32>::PTR_DATA_MASK, !0 << 2);
		assert_eq!(BitPtr::<u32>::PTR_HEAD_MASK, 3);
		assert_eq!(BitPtr::<u32>::LEN_ELTS_MASK, !0 << 8);
		assert_eq!(BitPtr::<u32>::LEN_TAIL_MASK, 31 << 3);
		assert_eq!(BitPtr::<u32>::LEN_INDX_MASK, 255);
	}

	#[test]
	fn associated_consts_u64() {
		assert_eq!(BitPtr::<u64>::PTR_DATA_BITS, PTR_BITS - 3);
		assert_eq!(BitPtr::<u64>::PTR_HEAD_BITS, 3);
		assert_eq!(BitPtr::<u64>::LEN_ELTS_BITS, USZ_BITS - 9);
		assert_eq!(BitPtr::<u64>::LEN_TAIL_BITS, 6);

		assert_eq!(BitPtr::<u64>::PTR_DATA_MASK, !0 << 3);
		assert_eq!(BitPtr::<u64>::PTR_HEAD_MASK, 7);
		assert_eq!(BitPtr::<u64>::LEN_ELTS_MASK, !0 << 9);
		assert_eq!(BitPtr::<u64>::LEN_TAIL_MASK, 63 << 3);
		assert_eq!(BitPtr::<u64>::LEN_INDX_MASK, 511);
	}

	#[test]
	fn ctors() {
		let data: [u32; 4] = [0x756c6153, 0x2c6e6f74, 0x6e6f6d20, 0x00216f64];
		let bp = BitPtr::<u32>::new(&data as *const u32, 4, 0, 32);
		assert_eq!(bp.pointer().r(), &data as *const u32);
		assert_eq!(bp.elements(), 4);
		assert_eq!(*bp.head(), 0);
		assert_eq!(*bp.tail(), 32);
	}

	#[test]
	fn empty() {
		let data = [0u8; 4];
		//  anything with 0 elements is unconditionally empty
		assert!(BitPtr::<u8>::new(&data as *const u8, 0, 2, 4).is_empty());
	}

	#[test]
	#[should_panic]
	fn overfull() {
		BitPtr::<u32>::new(8 as *const u32, BitPtr::<u32>::MAX_ELTS, 0, 32);
	}

	#[test]
	fn patterns() {
		/// Typehack a tuple of raw bit patterns directly into a bit pointer.
		fn bp(ptr: *const u32, len: usize) -> BitPtr<u32> {
			let ptr = Pointer::from(ptr as *const u8);
			BitPtr {
				_ty: PhantomData,
				ptr: unsafe { NonNull::new_unchecked(ptr.w()) },
				len,
			}
		}

		let ptr = NonNull::<u32>::dangling().as_ptr();

		let h0t0e0 = bp(ptr, 0);
		assert!(h0t0e0.is_empty());

		let h0t1 = bp(ptr, 8);
		assert_eq!(*h0t1.head(), 0);
		assert_eq!(*h0t1.tail(), 1);
		assert_eq!(h0t1.elements(), 1);
		assert_eq!(h0t1.len(), 1);

		let h16t17 = bp((ptr as usize | 2) as *const u32, 17 << 3);
		assert_eq!(*h16t17.head(), 16);
		assert_eq!(*h16t17.tail(), 17);
		assert_eq!(h16t17.elements(), 1);
		assert_eq!(h16t17.len(), 1);

		let h0t0e1 = bp(ptr, 1 << 8);
		assert_eq!(h0t0e1.elements(), 1);
		assert_eq!(h0t0e1.len(), 32);
	}
}
