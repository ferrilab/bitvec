//! Encoded pointer to a span region.

use crate::{
	access::BitAccess,
	domain::Domain,
	index::{
		BitIdx,
		BitIdxErr,
		BitTail,
	},
	mem::BitMemory,
	mutability::{
		Const,
		Mut,
		Mutability,
	},
	order::BitOrder,
	ptr::{
		Address,
		AddressError,
	},
	slice::BitSlice,
	store::BitStore,
};

use core::{
	any,
	convert::{
		Infallible,
		TryInto,
	},
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
		Pointer,
	},
	marker::PhantomData,
	ptr::{
		self,
		NonNull,
	},
};

use wyz::fmt::FmtForward;

/** Encoded handle to a bit-precision memory region.

Rust slices use a pointer/length encoding to represent regions of memory.
References to slices of data, `&[T]`, have the ABI layout `(*const T, usize)`.

`BitSpan` encodes a base address, a first-bit index, and a length counter, into
the Rust slice reference layout using this structure. This permits [`bitvec`] to
use an opaque reference type in its implementation of Rust interfaces that
require references, rather than immediate value types.

# Layout

This structure is a more complex version of the `*const T`/`usize` tuple that
Rust uses to represent slices throughout the language. It breaks the pointer and
counter fundamentals into sub-field components. Rust does not have bitfield
syntax, so the below description of the structure layout is in C++.

```cpp
template <typename T>
struct BitSpan {
  uintptr_t ptr_head : __builtin_ctzll(alignof(T));
  uintptr_t ptr_addr : sizeof(uintptr_T) * 8 - __builtin_ctzll(alignof(T));

  size_t len_head : 3;
  size_t len_bits : sizeof(size_t) * 8 - 3;
};
```

This means that the `BitSpan<O, T>` has three *logical* fields, stored in four
segments, across the two *structural* fields of the type. The widths and
placements of each segment are functions of the size of `*const T`, `usize`, and
of the alignment of the `T` referent buffer element type.

# Fields

This section describes the purpose, semantic meaning, and layout of the three
logical fields.

## Base Address

The address of the base element in a memory region is stored in all but the
lowest bits of the `ptr` field. An aligned pointer to `T` will always have its
lowest log<sub>2</sub>(byte width) bits zeroed, so those bits can be used to
store other information, as long as they are erased before dereferencing the
address as a pointer to `T`.

## Head Bit Index

For any referent element type `T`, the selection of a single bit within the
element requires log<sub>2</sub>(byte width) bits to select a byte within the
element `T`, and another three bits to select a bit within the selected byte.

|Type |Alignment|Trailing Zeros|Count Bits|
|:----|--------:|-------------:|---------:|
|`u8` |        1|             0|         3|
|`u16`|        2|             1|         4|
|`u32`|        4|             2|         5|
|`u64`|        8|             3|         6|

The index of the first live bit in the base element is split to have its three
least significant bits stored in the least significant edge of the `len` field,
and its remaining bits stored in the least significant edge of the `ptr` field.

## Length Counter

All but the lowest three bits of the `len` field are used to store a counter of
live bits in the referent region. When this is zero, the region is empty.
Because it is missing three bits, a `BitSpan` has only ⅛ of the index space of
a `usize` value.

# Significant Values

The following values represent significant instances of the `BitSpan` type.

## Null Slice

The fully-zeroed slot is not a valid member of the `BitSpan<O, T>` type; it is
reserved instead as the sentinel value for `Option::<BitSpan<O, T>>::None`.

## Canonical Empty Slice

All pointers with a `bits: 0` logical field are empty. Pointers that are used to
maintain ownership of heap buffers are not permitted to erase their `addr`
field. The canonical form of the empty slice has an `addr` value of
[`NonNull::<T>::dangling()`], but all pointers to an empty region are equivalent
regardless of address.

### Uninhabited Slices

Any empty pointer with a non-[`dangling()`] base address is considered to be an
uninhabited region. `BitSpan` never discards its address information, even as
operations may alter or erase its head-index or length values.

# Type Parameters

- `O`: The ordering within the register type. The bit-ordering used within a
  region colors all pointers to the region, and orderings can never mix.
- `T`: The memory type of the referent region. `BitSpan<O, T>` is a specialized
  `*[T]` slice pointer, and operates on memory in terms of the `T` type for
  access instructions and pointer calculation.

# Safety

`BitSpan` values may only be constructed from pointers provided by the
surrounding program.

# Undefined Behavior

Values of this type are binary-incompatible with slice pointers. Transmutation
of these values into any other type will result in an incorrect program, and
permit the program to begin illegal or undefined behaviors. This type may never
be manipulated in any way by user code outside of the APIs it offers to this
[`bitvec`]; it certainly may not be seen or observed by other crates.

[`NonNull::<T>::dangling()`]: core::ptr::NonNull::dangling
[`bitvec`]: crate
[`dangling()`]: core::ptr::NonNull::dangling
**/
#[repr(C)]
pub(crate) struct BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	/// Memory address and high bits of the head index.
	///
	/// This stores the address of the zeroth element of the slice, as well as
	/// the high bits of the head bit cursor. It is typed as a [`NonNull<u8>`]
	/// in order to provide null-value optimizations to `Option<BitSpan<O, T>>`,
	/// and because the presence of head-bit cursor information in the lowest
	/// bits means that the bit pattern will not uphold alignment properties
	/// required by `NonNull<T>`.
	///
	/// This field cannot be treated as the address of the zeroth byte of the
	/// slice domain, because the owning handle’s [`BitOrder`] implementation
	/// governs the bit pattern of the head cursor.
	///
	/// [`BitOrder`]: crate::order::BitOrder
	/// [`NonNull<u8>`]: core::ptr::NonNull
	ptr: NonNull<u8>,
	/// Length counter and low bits of the head index.
	///
	/// This stores the slice length counter (measured in bits) in all but its
	/// lowest three bits, and the lowest three bits of the index counter in its
	/// lowest three bits.
	len: usize,
	/// Bit-region pointers must be colored by the bit-ordering they use.
	_or: PhantomData<O>,
	/// This is semantically a pointer to a `T` element.
	_ty: PhantomData<Address<M, T>>,
}

impl<M, O, T> BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	/// The canonical form of a pointer to an empty region.
	pub(crate) const EMPTY: Self = Self {
		/* Note: this must always construct the `T` dangling pointer, and then
		convert it into a pointer to `u8`. Creating `NonNull::dangling()`
		directly will always instantiate the `NonNull::<u8>::dangling()`
		pointer, which is VERY incorrect for any other `T` typarams.
		*/
		ptr: unsafe {
			NonNull::new_unchecked(NonNull::<T>::dangling().as_ptr() as *mut u8)
		},
		len: 0,
		_or: PhantomData,
		_ty: PhantomData,
	};
	/// The number of low bits of `self.len` required to hold the low bits of
	/// the head [`BitIdx`] cursor.
	///
	/// This is always `3`, until Rust tries to target an architecture that does
	/// not have 8-bit bytes.
	///
	/// [`BitIdx`]: crate::index::BitIdx
	pub(crate) const LEN_HEAD_BITS: usize = 3;
	/// Marks the bits of `self.len` that hold part of the `head` logical field.
	pub(crate) const LEN_HEAD_MASK: usize = 0b111;
	/// Marks the bits of `self.ptr` that hold the `addr` logical field.
	pub(crate) const PTR_ADDR_MASK: usize = !0 << Self::PTR_HEAD_BITS;
	/// The number of low bits of `self.ptr` required to hold the high bits of
	/// the head [`BitIdx`] cursor.
	///
	/// [`BitIdx`]: crate::index::BitIdx
	pub(crate) const PTR_HEAD_BITS: usize =
		T::Mem::INDX as usize - Self::LEN_HEAD_BITS;
	/// Marks the bits of `self.ptr` that hold part of the `head` logical field.
	pub(crate) const PTR_HEAD_MASK: usize = !Self::PTR_ADDR_MASK;
	/// The inclusive-maximum number of bits that a `BitSpan` can cover.
	pub(crate) const REGION_MAX_BITS: usize = !0 >> Self::LEN_HEAD_BITS;
	/// The inclusive-maximum number of elements that the region described by a
	/// `BitSpan` can cover in memory.
	///
	/// This is the number of elements required to store [`REGION_MAX_BITS`],
	/// plus one because a region could start in the middle of its base element
	/// and thus push the final bits into a new element.
	///
	/// Since the region is ⅛th the bit span of a `usize` counter already, this
	/// number is guaranteed to be well below the limits of arithmetic or Rust’s
	/// own constraints on memory region handles.
	///
	/// [`REGION_MAX_BITS`]: Self::REGION_MAX_BITS
	pub(crate) const REGION_MAX_ELTS: usize =
		crate::mem::elts::<T::Mem>(Self::REGION_MAX_BITS) + 1;

	//  Constructors

	/// Constructs an empty `BitSpan` at a bare pointer.
	///
	/// This is used when the region has no contents, but the pointer
	/// information must be retained.
	///
	/// # Parameters
	///
	/// - `addr`: Some address of a `T` element or region. It must be valid in
	///   the caller’s memory space.
	///
	/// # Returns
	///
	/// A zero-length `BitSpan` pointing to `addr`.
	///
	/// # Panics
	///
	/// This function panics if `addr` is null or misaligned. All pointers
	/// received from the allocation system are required to satisfy this
	/// constraint, so a failure is an exceptional program fault rather than an
	/// expected logical mistake.
	#[cfg(any(feature = "alloc", test))]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn uninhabited<A>(addr: A) -> Self
	where A: TryInto<Address<M, T>, Error = AddressError<T>> {
		Self {
			ptr: addr
				.try_into()
				.expect(
					"BitSpan::uninhabited cannot be called with an invalid \
					 address",
				)
				.to_nonnull_u8(),
			len: 0,
			_or: PhantomData,
			_ty: PhantomData,
		}
	}

	/// Constructs a new `BitSpan` from its components.
	///
	/// # Parameters
	///
	/// - `addr`: A well-aligned pointer to a storage element.
	/// - `head`: The bit index of the first live bit in the element under
	///   `*addr`.
	/// - `bits`: The number of live bits in the region the produced `BitSpan`
	///   describes.
	///
	/// # Returns
	///
	/// This returns `None` in the following cases:
	///
	/// - `addr` is the null pointer, or is not adequately aligned for `T`.
	/// - `bits` is greater than `Self::REGION_MAX_BITS`, and cannot be encoded
	///   into a `BitSpan`.
	/// - addr` is so high in the address space that the element slice wraps
	///   around the address space boundary.
	///
	/// # Safety
	///
	/// The caller must provide an `addr` pointer and a `bits` counter which
	/// describe a `[T]` region which is correctly aligned and validly allocated
	/// in the caller’s memory space. The caller is responsible for ensuring
	/// that the slice of memory the produced `BitSpan` describes is all
	/// governable in the caller’s context.
	pub(crate) fn new<A>(
		addr: A,
		head: BitIdx<T::Mem>,
		bits: usize,
	) -> Result<Self, BitSpanError<O, T>>
	where
		A: TryInto<Address<M, T>>,
		BitSpanError<O, T>: From<A::Error>,
	{
		let addr = addr.try_into()?;

		if bits > Self::REGION_MAX_BITS {
			return Err(BitSpanError::TooLong(bits));
		}

		let elts = head.offset(bits as isize).0;
		let addr_raw = addr.to_const();
		let last = addr_raw.wrapping_add(elts as usize);
		if last < addr_raw {
			return Err(BitSpanError::TooHigh(addr_raw));
		}

		Ok(unsafe { Self::new_unchecked(addr, head, bits) })
	}

	/// Creates a new `BitSpan` from its components, without any validity
	/// checks.
	///
	/// # Safety
	///
	/// ***ABSOLUTELY NONE.*** This function *only* packs its arguments into the
	/// bit pattern of the `BitSpan` type. It should only be used in
	/// contexts where a previously extant `BitSpan` was constructed with
	/// ancestry known to have survived [`::new`], and any manipulations of its
	/// raw components are known to be valid for reconstruction.
	///
	/// # Parameters
	///
	/// See [`::new`].
	///
	/// # Returns
	///
	/// See [`::new`].
	///
	/// [`::new`]: Self::new
	pub(crate) unsafe fn new_unchecked<A>(
		addr: A,
		head: BitIdx<T::Mem>,
		bits: usize,
	) -> Self
	where
		A: TryInto<Address<M, T>>,
		A::Error: Debug,
	{
		let (addr, head) = (addr.try_into().unwrap(), head.value() as usize);

		let ptr_data = addr.value() & Self::PTR_ADDR_MASK;
		let ptr_head = head >> Self::LEN_HEAD_BITS;

		let len_head = head & Self::LEN_HEAD_MASK;
		let len_bits = bits << Self::LEN_HEAD_BITS;

		let ptr = Address::new(ptr_data | ptr_head)
			.expect("Cannot use a null pointer");

		Self {
			ptr: NonNull::new_unchecked(ptr.to_mut()),
			len: len_bits | len_head,
			_or: PhantomData,
			_ty: PhantomData,
		}
	}

	//  Converters

	/// Converts an opaque `*BitSlice` wide pointer back into a `BitSpan`.
	///
	/// See [`::from_bitslice_ptr()`].
	///
	/// [`::from_bitslice_ptr()`]: Self::from_bitslice_ptr
	//  Mutable pointers can become mutable or immutable span descriptors.
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn from_bitslice_ptr_mut(raw: *mut BitSlice<O, T>) -> Self {
		let BitSpan { ptr, len, _or, .. } =
			BitSpan::from_bitslice_ptr(raw as *const BitSlice<O, T>);
		Self {
			ptr,
			len,
			_or,
			_ty: PhantomData,
		}
	}

	/// Casts the `BitSpan` to an opaque `*BitSlice` pointer.
	///
	/// This is the inverse of [`::from_bitslice_ptr()`].
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// `self`, opacified as a `*BitSlice` raw pointer rather than a `BitSpan`
	/// structure.
	///
	/// [`::from_bitslice_ptr()`]: Self::from_bitslice_ptr
	//  Mutable or immutable span descriptors can become immutable pointers.
	pub(crate) fn to_bitslice_ptr(self) -> *const BitSlice<O, T> {
		ptr::slice_from_raw_parts(
			self.ptr.as_ptr() as *const u8 as *const (),
			self.len,
		) as *const BitSlice<O, T>
	}

	/// Casts the `BitSpan` to a `&BitSlice` reference.
	///
	/// This requires that the pointer be to a validly-allocated region that
	/// is not destroyed for the duration of the provided lifetime.
	/// Additionally, the bits described by `self` must not be writable by any
	/// other handle.
	///
	/// # Lifetimes
	///
	/// - `'a`: A caller-provided lifetime that must not be greater than the
	///   duration of the referent buffer.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// `self`, opacified as a bit-slice region reference rather than a
	/// `BitSpan` structure.
	//  Mutable or immutable span descriptors can become immutable references.
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn to_bitslice_ref<'a>(self) -> &'a BitSlice<O, T> {
		unsafe { &*self.to_bitslice_ptr() }
	}

	/// Casts the span to another element type.
	///
	/// This does not alter the encoded value of the pointer! It only
	/// reinterprets the element type, and the encoded value may shift
	/// significantly in the result type. Use with caution.
	pub(crate) fn cast<U>(self) -> BitSpan<M, O, U>
	where U: BitStore {
		let Self { ptr, len, .. } = self;
		BitSpan {
			ptr,
			len,
			..BitSpan::EMPTY
		}
	}

	/// Split the region descriptor into three descriptors, with the interior
	/// set to a different register type.
	///
	/// By placing the logic in `BitSpan` rather than in `BitSlice`, `BitSlice`
	/// can safely call into it for both shared and exclusive references,
	/// without running into any reference capability issues in the compiler.
	///
	/// # Type Parameters
	///
	/// - `U`: A second [`BitStore`] implementation. This **must** be of the
	///   same type family as `T`; this restriction cannot be enforced in the
	///   type system, but **must** hold at the call site.
	///
	/// # Safety
	///
	/// This can only be called within `BitSlice::align_to{,_mut}`.
	///
	/// # Algorithm
	///
	/// This uses the slice [`Domain`] to split the underlying slice into
	/// regions that cannot (edge) and can (center) be reäligned. The center
	/// slice is then reäligned to `U`, and the edge slices produced from *that*
	/// are merged with the edge slices produced by the domain check.
	///
	/// This results in edge pointers returned from this function that correctly
	/// handle partially-used edge elements as well as misaligned slice
	/// locations.
	///
	/// [`BitStore`]: crate::store::BitStore
	/// [`Domain`]: crate::domain::Domain
	/// [`slice::align_to`]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.align_to
	pub(crate) unsafe fn align_to<U>(self) -> (Self, BitSpan<M, O, U>, Self)
	where U: BitStore {
		match self.to_bitslice_ref().domain() {
			Domain::Enclave { .. } => (self, BitSpan::EMPTY, BitSpan::EMPTY),
			Domain::Region { head, body, tail } => {
				//  Reälign the fully-spanning center slice, creating edge
				//  slices of the original type to merge with `head` and `tail`.
				let (l, c, r) = body.align_to::<U::Mem>();

				let t_bits = T::Mem::BITS as usize;
				let u_bits = U::Mem::BITS as usize;

				let l_bits = l.len() * t_bits;
				let c_bits = c.len() * u_bits;
				let r_bits = r.len() * t_bits;

				let l_addr = l.as_ptr() as *const T as *mut T;
				let c_addr = c.as_ptr() as *const U as *mut U;
				let r_addr = r.as_ptr() as *const T as *mut T;

				/* Compute a pointer for the left-most return span.

				The left span must contain the domain’s head element, if
				produced, as well as the `l` slice produced above. The left span
				begins in:

				- if `head` exists, then `head.1`
				- else, if `l` is not empty, then `l`
				- else, it is the empty pointer
				*/
				let l_ptr = match head {
					/* If the head exists, then the left span begins in it, and
					runs for the remaining bits in it, and all the bits of `l`.
					*/
					Some((head, addr)) => BitSpan::new_unchecked(
						addr as *const T as *mut T,
						head,
						t_bits - head.value() as usize + l_bits,
					),
					//  If the head does not exist, then the left span only
					//  covers `l`. If `l` is empty, then so is the span.
					None => {
						if l_bits == 0 {
							BitSpan::EMPTY
						}
						else {
							BitSpan::new_unchecked(l_addr, BitIdx::ZERO, l_bits)
						}
					},
				};

				let c_ptr = if c_bits == 0 {
					BitSpan::EMPTY
				}
				else {
					BitSpan::new_unchecked(c_addr, BitIdx::ZERO, c_bits)
				};

				/* Compute a pointer for the right-most return span.

				The right span must contain the `r` slice produced above, as
				well as the domain’s tail element, if produced. The right span
				begins in:

				- if `r` is not empty, then `r`
				- else, if `tail` exists, then `tail.0`
				- else, it is the empty pointer
				*/
				let r_ptr = match tail {
					//  If the tail exists, then the right span extends into it.
					Some((addr, tail)) => BitSpan::new_unchecked(
						//  If the `r` slice exists, then the right span
						//  *begins* in it.
						if r.is_empty() {
							addr as *const T as *mut T
						}
						else {
							r_addr
						},
						BitIdx::ZERO,
						tail.value() as usize + r_bits,
					),
					//  If the tail does not exist, then the right span is only
					//  `r`.
					None => {
						//  If `r` exists, then the right span covers it.
						if !r.is_empty() {
							BitSpan::new_unchecked(r_addr, BitIdx::ZERO, r_bits)
						}
						//  Otherwise, the right span is empty.
						else {
							BitSpan::EMPTY
						}
					},
				};

				(l_ptr, c_ptr, r_ptr)
			},
		}
	}

	//  Encoded fields

	/// Gets the base element address of the referent region.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The address of the starting element of the memory region. This address
	/// is weakly typed so that it can be cast by call sites to the most useful
	/// access type.
	pub(crate) fn pointer(&self) -> Address<M, T> {
		unsafe {
			Address::new_unchecked(
				self.ptr.as_ptr() as usize & Self::PTR_ADDR_MASK,
			)
		}
	}

	/// Overwrites the data pointer with a new address. This method does not
	/// perform safety checks on the new pointer.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `ptr`: The new address of the `BitSpan`’s domain.
	///
	/// # Safety
	///
	/// None. The invariants of [`::new`] must be checked at the caller.
	///
	/// [`::new`]: Self::new
	#[cfg(any(feature = "alloc", test))]
	pub(crate) unsafe fn set_pointer<A>(&mut self, addr: A)
	where
		A: TryInto<Address<M, T>>,
		A::Error: Debug,
	{
		let addr = addr.try_into().unwrap();
		let mut addr_value = addr.value();
		addr_value &= Self::PTR_ADDR_MASK;
		addr_value |= self.ptr.as_ptr() as usize & Self::PTR_HEAD_MASK;
		let addr = Address::new_unchecked(addr_value);
		self.ptr = NonNull::new_unchecked(addr.to_mut() as *mut u8);
	}

	/// Gets the starting bit index of the referent region.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A [`BitIdx`] of the first live bit in the element at the
	/// [`self.pointer()`] address.
	///
	/// [`BitIdx`]: crate::index::BitIdx
	/// [`self.pointer()`]: Self::pointer
	pub(crate) fn head(&self) -> BitIdx<T::Mem> {
		//  Get the high part of the head counter out of the pointer.
		let ptr = self.ptr.as_ptr() as usize;
		let ptr_head = (ptr & Self::PTR_HEAD_MASK) << Self::LEN_HEAD_BITS;
		//  Get the low part of the head counter out of the length.
		let len_head = self.len & Self::LEN_HEAD_MASK;
		//  Combine and mark as an index.
		unsafe { BitIdx::new_unchecked((ptr_head | len_head) as u8) }
	}

	/// Write a new `head` value into the pointer, with no other effects.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `head`: A new starting index.
	///
	/// # Effects
	///
	/// `head` is written into the `.head` logical field, without affecting
	/// `.addr` or `.bits`.
	#[cfg(any(feature = "alloc", test))]
	pub(crate) unsafe fn set_head(&mut self, head: BitIdx<T::Mem>) {
		let head = head.value() as usize;
		let mut ptr = self.ptr.as_ptr() as usize;

		ptr &= Self::PTR_ADDR_MASK;
		ptr |= head >> Self::LEN_HEAD_BITS;
		self.ptr = NonNull::new_unchecked(ptr as *mut u8);

		self.len &= !Self::LEN_HEAD_MASK;
		self.len |= head & Self::LEN_HEAD_MASK;
	}

	/// Gets the number of live bits in the referent region.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A count of how many live bits the region pointer describes.
	pub(crate) fn len(&self) -> usize {
		self.len >> Self::LEN_HEAD_BITS
	}

	/// Sets the `.bits` logical member to a new value.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `len`: A new bit length. This must not be greater than
	///   [`REGION_MAX_BITS`].
	///
	/// # Effects
	///
	/// The `new_len` value is written directly into the `.bits` logical field.
	///
	/// [`REGION_MAX_BITS`]: Self::REGION_MAX_BITS
	pub(crate) unsafe fn set_len(&mut self, new_len: usize) {
		debug_assert!(
			new_len <= Self::REGION_MAX_BITS,
			"Length {} out of range",
			new_len,
		);
		self.len &= Self::LEN_HEAD_MASK;
		self.len |= new_len << Self::LEN_HEAD_BITS;
	}

	/// Gets the three logical components of the pointer.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `.0`: The base address of the referent memory region.
	/// - `.1`: The index of the first live bit in the first element of the
	///   region.
	/// - `.2`: The number of live bits in the region.
	pub(crate) fn raw_parts(&self) -> (Address<M, T>, BitIdx<T::Mem>, usize) {
		(self.pointer(), self.head(), self.len())
	}

	//  Computed information

	/// Computes the number of elements, starting at [`self.pointer()`], that
	/// the region touches.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The count of all elements, starting at [`self.pointer()`], that contain
	/// live bits included in the referent region.
	///
	/// [`self.pointer()`]: Self::pointer
	pub(crate) fn elements(&self) -> usize {
		//  Find the distance of the last bit from the base address.
		let total = self.len() + self.head().value() as usize;
		//  The element count is always the bit count divided by the bit width,
		let base = total >> T::Mem::INDX;
		//  plus whether any fractional element exists after the division.
		let tail = total as u8 & T::Mem::MASK;
		base + (tail != 0) as usize
	}

	/// Computes the tail index for the first dead bit after the live bits.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitTail` that is the index of the first dead bit after the last live
	/// bit in the last element. This will almost always be in the range `1 ..=
	/// T::Mem::BITS`.
	///
	/// It will be zero only when `self` is empty.
	pub(crate) fn tail(&self) -> BitTail<T::Mem> {
		let (head, len) = (self.head(), self.len());

		if head.value() == 0 && len == 0 {
			return BitTail::ZERO;
		}

		//  Compute the in-element tail index as the head plus the length,
		//  modulated by the element width.
		let tail = (head.value() as usize + len) & T::Mem::MASK as usize;
		/* If the tail is zero, wrap it to `T::Mem::BITS` as the maximal. This
		upshifts `1` (tail is zero) or `0` (tail is not), then sets the upshift
		on the rest of the tail, producing something in the range
		`1 ..= T::Mem::BITS`.
		*/
		unsafe {
			BitTail::new_unchecked(
				(((tail == 0) as u8) << T::Mem::INDX) | tail as u8,
			)
		}
	}

	//  Manipulators

	/// Increments the `.head` logical field, rolling over into `.addr`.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Effects
	///
	/// Increments `.head` by one. If the increment resulted in a rollover to
	/// `0`, then the `.addr` field is increased to the next [`T::Mem`]
	/// stepping.
	///
	/// [`T::Mem`]: crate::store::BitStore::Mem
	pub(crate) unsafe fn incr_head(&mut self) {
		//  Increment the cursor, permitting rollover to `T::Mem::BITS`.
		let head = self.head().value() as usize + 1;

		//  Write the low bits into the `.len` field, then discard them.
		self.len &= !Self::LEN_HEAD_MASK;
		self.len |= head & Self::LEN_HEAD_MASK;
		let head = head >> Self::LEN_HEAD_BITS;

		//  Erase the high bits of `.head` from `.ptr`,
		let mut ptr = self.ptr.as_ptr() as usize;
		ptr &= Self::PTR_ADDR_MASK;
		/* Then numerically add the high bits of `.head` into the low bits of
		`.ptr`. If the head increment rolled over into a new element, this will
		have the effect of raising the `.addr` logical field to the next element
		address, in one instruction.
		*/
		ptr += head;
		self.ptr = NonNull::new_unchecked(ptr as *mut u8);
	}

	//  Memory accessors

	/// Reads a bit some distance away from `self`.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The bit distance away from `self` at which to read.
	///
	/// # Returns
	///
	/// The value of the bit `index` bits away from [`self.head()`], according
	/// to the `O` ordering.
	///
	/// [`self.head()`]: Self::head
	pub(crate) unsafe fn read(&self, index: usize) -> bool {
		let (elt, bit) = self.head().offset(index as isize);
		let base = self.pointer().to_const();
		(&*base.offset(elt)).get_bit::<O>(bit)
	}

	//  Comparators

	/// Computes the distance, in elements and bits, between two bit-pointers.
	///
	/// # Undefined Behavior
	///
	/// It is undefined to calculate the distance between pointers that are not
	/// part of the same allocation region. This function is defined only when
	/// `self` and `other` are produced from the same region.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `other`: A reference to another `BitSpan`. This function is undefined
	///   if it is not produced from the same region as `self`.
	///
	/// # Returns
	///
	/// - `.0`: The distance in elements `T` between the first element of `self`
	///   and the first element of `other`. This is negative if `other` is lower
	///   in memory than `self`, and positive if `other` is higher.
	/// - `.1`: The distance in bits between the first bit of `self` and the
	///   first bit of `other`. This is negative if `other`’s first bit is lower
	///   in its element than `self`’s first bit is in its element, and positive
	///   if `other`’s first bit is higher in its element than `self`’s first
	///   bit is in its element.
	///
	/// # Truth Tables
	///
	/// Consider two adjacent bytes in memory. We will define four pairs of
	/// bit-pointers of width `1` at various points in this span in order to
	/// demonstrate the four possible states of difference.
	///
	/// ```text
	///    [ 0 1 2 3 4 5 6 7 ] [ 8 9 a b c d e f ]
	/// 1.       A                       B
	/// 2.             A             B
	/// 3.           B           A
	/// 4.     B                             A
	/// ```
	///
	/// 1. The pointer `A` is in the lower element and `B` is in the higher. The
	///    first bit of `A` is lower in its element than the first bit of `B` is
	///    in its element. `A.ptr_diff(B)` thus produces positive element and
	///    bit distances: `(1, 2)`.
	/// 2. The pointer `A` is in the lower element and `B` is in the higher. The
	///    first bit of `A` is higher in its element than the first bit of `B`
	///    is in its element. `A.ptr_diff(B)` thus produces a positive element
	///    distance and a negative bit distance: `(1, -3)`.
	/// 3. The pointer `A` is in the higher element and `B` is in the lower. The
	///    first bit of `A` is lower in its element than the first bit of `B` is
	///    in its element. `A.ptr_diff(B)` thus produces a negative element
	///    distance and a positive bit distance: `(-1, 4)`.
	/// 4. The pointer `A` is in the higher element and `B` is in the lower. The
	///    first bit of `A` is higher in its element than the first bit of `B`
	///    is in its element. `A.ptr_diff(B)` thus produces negative element and
	///    bit distances: `(-1, -5)`.
	pub(crate) unsafe fn ptr_diff(&self, other: &Self) -> (isize, i8) {
		let self_ptr = self.pointer().to_const();
		let other_ptr = other.pointer().to_const();
		let elts = other_ptr.offset_from(self_ptr);
		let bits = other.head().value() as i8 - self.head().value() as i8;
		(elts, bits)
	}

	/// Renders the pointer structure into a formatter for use during
	/// higher-level type [`Debug`] implementations.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `fmt`: The formatter into which the pointer is rendered.
	/// - `name`: The suffix of the structure rendering its pointer. The `Bit`
	///   prefix is applied to the object type name in this format.
	/// - `fields`: Any additional fields in the object’s debug info to be
	///   rendered.
	///
	/// # Returns
	///
	/// The result of formatting the pointer into the receiver.
	///
	/// # Behavior
	///
	/// This function writes `Bit{name}<{ord}, {type}> {{ {fields } }}` into the
	/// `fmt` formatter, where `{fields}` includes the address, head index, and
	/// bit length of the pointer, as well as any additional fields provided by
	/// the caller.
	///
	/// Higher types in the crate should use this function to drive their
	/// [`Debug`] implementations, and then use [`BitSlice`]’s list formatters
	/// to display their buffer contents.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	/// [`Debug`]: core::fmt::Debug
	pub(crate) fn render<'a>(
		&'a self,
		fmt: &'a mut Formatter,
		name: &'a str,
		fields: impl IntoIterator<Item = &'a (&'a str, &'a dyn Debug)>,
	) -> fmt::Result {
		write!(
			fmt,
			"Bit{}<{}, {}>",
			name,
			any::type_name::<O>(),
			any::type_name::<T::Mem>()
		)?;
		let mut builder = fmt.debug_struct("");
		builder
			.field("addr", &self.pointer().fmt_pointer())
			.field("head", &self.head().fmt_binary())
			.field("bits", &self.len());
		for (name, value) in fields {
			builder.field(name, value);
		}
		builder.finish()
	}
}

impl<O, T> BitSpan<Const, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Converts an opaque `*BitSlice` wide pointer back into a `BitSpan`.
	///
	/// This should compile down to a noöp, but the implementation should
	/// nevertheless be an explicit deconstruction and reconstruction rather
	/// than a bare [`mem::transmute`], to guard against unforseen compiler
	/// reördering.
	///
	/// # Parameters
	///
	/// - `raw`: An opaque bit-region pointer
	///
	/// # Returns
	///
	/// `raw`, interpreted as a `BitSpan` so that it can be used as more than an
	/// opaque handle.
	///
	/// [`mem::transmute`]: core::mem::transmute
	//  Immutable pointers can only become immutable span descriptors.
	pub(crate) fn from_bitslice_ptr(raw: *const BitSlice<O, T>) -> Self {
		let slice_nn = match NonNull::new(raw as *const [()] as *mut [()]) {
			Some(nn) => nn,
			None => return Self::EMPTY,
		};
		let ptr = slice_nn.cast::<u8>();
		let len = unsafe { slice_nn.as_ref() }.len();
		Self {
			ptr,
			len,
			_or: PhantomData,
			_ty: PhantomData,
		}
	}

	/// Assert that an immutable span pointer is in fact mutable.
	///
	/// This can only be called from a context where a mutable span descriptor
	/// was lowered to immutable and needs to be re-raised; it is Undefined
	/// Behavior in the compiler to call it on a span descriptor that was never
	/// mutable.
	pub(crate) unsafe fn assert_mut(self) -> BitSpan<Mut, O, T> {
		let Self { ptr, len, _or, .. } = self;
		BitSpan {
			ptr,
			len,
			_or,
			_ty: PhantomData,
		}
	}
}

impl<O, T> BitSpan<Mut, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Casts the `BitSpan` to an opaque `*BitSlice` pointer.
	///
	/// See [`.to_bitslice_ptr()`].
	///
	/// [`.to_bitslice_ptr()`]: Self::to_bitslice_ptr
	//  Only mutable span descriptors can become mutable pointers.
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn to_bitslice_ptr_mut(self) -> *mut BitSlice<O, T> {
		self.to_bitslice_ptr() as *mut BitSlice<O, T>
	}

	/// Casts the `BitSpan` to a `&mut BitSlice` reference.
	///
	/// This requires that the pointer be to a validly-allocated region that is
	/// not destroyed for the duration of the provided lifetime. Additionally,
	/// the bits described by `self` must not be viewable by any other handle.
	///
	/// # Lifetimes
	///
	/// - `'a`: A caller-provided lifetime that must not be greater than the
	///   duration of the referent buffer.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// `self`, opacified as an exclusive bit-slice region reference rather than
	/// a `BitSpan` structure.
	//  Only mutable span descriptors can become mutable references.
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn to_bitslice_mut<'a>(self) -> &'a mut BitSlice<O, T> {
		unsafe { &mut *self.to_bitslice_ptr_mut() }
	}

	/// Casts the pointer structure into a [`NonNull<BitSlice>`] pointer.
	///
	/// This function is used by the owning indirect handles, and does not yet
	/// have any purpose in non-`alloc` programs.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// `self`, marked as a `NonNull` pointer.
	///
	/// [`NonNull<BitSlice>`]: core::ptr::NonNull
	#[cfg(any(feature = "alloc", test))]
	#[cfg(not(tarpaulin_include))]
	pub(crate) fn to_nonnull(self) -> NonNull<BitSlice<O, T>> {
		self.to_bitslice_mut().into()
	}

	/// Writes a bit some distance away from `self`.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`: The `self` pointer must be describing a write-capable region.
	/// - `index`: The bit distance away from `self` at which to write,
	///   according to the `O` ordering.
	/// - `value`: The bit value to insert at `index`.
	///
	/// # Effects
	///
	/// `value` is written to the bit specified by `index`, relative to
	/// [`self.head()`] and [`self.pointer()`].
	///
	/// [`self.head()`]: Self::head
	/// [`self.pointer()`]: Self::pointer
	pub(crate) unsafe fn write(&self, index: usize, value: bool) {
		let (elt, bit) = self.head().offset(index as isize);
		let base = self.pointer().to_access();
		(&*base.offset(elt)).write_bit::<O>(bit, value);
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> Clone for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		*self
	}
}

impl<M, O, T> Eq for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}

impl<M1, M2, O, T1, T2> PartialEq<BitSpan<M2, O, T2>> for BitSpan<M1, O, T1>
where
	M1: Mutability,
	M2: Mutability,
	O: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn eq(&self, other: &BitSpan<M2, O, T2>) -> bool {
		let (addr_a, head_a, bits_a) = self.raw_parts();
		let (addr_b, head_b, bits_b) = other.raw_parts();
		//  Since ::BITS is an associated const, the compiler will automatically
		//  replace the entire function with `false` when the types don’t match.
		T1::Mem::BITS == T2::Mem::BITS
			&& addr_a.value() == addr_b.value()
			&& head_a.value() == head_b.value()
			&& bits_a == bits_b
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> Default for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn default() -> Self {
		Self::EMPTY
	}
}

impl<M, O, T> Debug for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(self, fmt)
	}
}

impl<M, O, T> Pointer for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.render(fmt, "Ptr", None)
	}
}

impl<M, O, T> Copy for BitSpan<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}

/// An error produced when creating `BitSpan` encoded references.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// `BitSpan` cannot accept the null address.
	Null,
	/// `BitSpan` requires well-aligned addresses.
	Misaligned(PhantomData<O>, *const T),
	/// `BitSpan` requires valid head indices.
	InvalidHead(BitIdxErr<T::Mem>),
	/// `BitSpan` domains have a length ceiling.
	TooLong(usize),
	/// `BitSpan` domains have an address ceiling.
	TooHigh(*const T),
}

#[cfg(not(tarpaulin_include))]
impl<O, T> From<AddressError<T>> for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(err: AddressError<T>) -> Self {
		match err {
			AddressError::Null => Self::Null,
			AddressError::Misaligned(t) => Self::Misaligned(PhantomData, t),
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> From<BitIdxErr<T::Mem>> for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(err: BitIdxErr<T::Mem>) -> Self {
		Self::InvalidHead(err)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> From<Infallible> for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(_: Infallible) -> Self {
		Self::Null
	}
}

impl<O, T> Debug for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let oname = any::type_name::<O>();
		let tname = any::type_name::<T>();
		write!(fmt, "BitSpanError<{}, {}>::", oname, tname,)?;
		match self {
			Self::Null => fmt.write_str("Null"),
			Self::Misaligned(_, ptr) => write!(fmt, "Misaligned({:p})", *ptr),
			Self::InvalidHead(head) => write!(fmt, "InvalidHead({})", head),
			Self::TooLong(len) => {
				fmt.debug_tuple("TooLong").field(&len).finish()
			},
			Self::TooHigh(addr) => {
				fmt.debug_tuple("TooHigh").field(&addr).finish()
			},
		}
	}
}

impl<O, T> Display for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		match self {
			Self::Null => Display::fmt(&AddressError::<T>::Null, fmt),
			Self::Misaligned(_, ptr) => {
				Display::fmt(&AddressError::Misaligned(*ptr), fmt)
			},
			Self::InvalidHead(head) => Display::fmt(head, fmt),
			Self::TooLong(len) => write!(
				fmt,
				"Length {} is too long to encode in a bit slice, which can \
				 only accept {} bits",
				len,
				BitSpan::<Const, O, T>::REGION_MAX_BITS
			),
			Self::TooHigh(addr) => {
				write!(fmt, "Address {:p} would wrap the address space", addr)
			},
		}
	}
}

unsafe impl<O, T> Send for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

unsafe impl<O, T> Sync for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(feature = "std")]
impl<O, T> std::error::Error for BitSpanError<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;
	use core::{
		mem,
		ptr,
	};

	#[test]
	fn ctor() {
		assert!(matches!(
			Address::<Const, u8>::new(0),
			Err(AddressError::Null)
		));
		assert!(matches!(
			Address::<Const, u16>::new(3),
			Err(AddressError::Misaligned(addr)) if addr as usize == 3
		));

		let data = 0u8;
		assert!(BitSpan::<_, LocalBits, _>::new(&data, BitIdx::ZERO, 5).is_ok());
		assert!(matches!(
			BitSpan::<_, LocalBits, _>::new(&data, BitIdx::ZERO, (!0 >> 3) + 1),
			Err(BitSpanError::TooLong(_))
		));
		assert!(matches!(
			BitSpan::<_, LocalBits, _>::new(
				!0usize as *const u8,
				BitIdx::ZERO,
				8
			),
			Err(BitSpanError::TooHigh(_))
		));

		//  Double check the null pointers, but they are in practice impossible
		//  to construct.
		assert_eq!(
			BitSpan::<Const, LocalBits, u8>::from_bitslice_ptr(
				ptr::slice_from_raw_parts(ptr::null::<()>(), 1)
					as *mut BitSlice<LocalBits, u8>
			),
			BitSpan::<Const, LocalBits, u8>::EMPTY,
		);
	}

	#[test]
	fn recast() {
		let data = 0u32;
		let bitspan =
			BitSpan::<_, LocalBits, _>::new(&data, BitIdx::ZERO, 32).unwrap();
		let raw_ptr = bitspan.to_bitslice_ptr();
		assert_eq!(
			bitspan,
			BitSpan::<Const, Lsb0, u32>::from_bitslice_ptr(raw_ptr)
		);
	}

	#[test]
	fn realign() {
		let data = [0u8; 10];
		let bits = data.view_bits::<LocalBits>();

		let (l, c, r) = unsafe { bits.bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 80);

		let (l, c, r) = unsafe { bits[4 ..].bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 76);

		let (l, c, r) = unsafe { bits[.. 76].bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 76);

		let (l, c, r) = unsafe { bits[8 ..].bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 72);

		let (l, c, r) = unsafe { bits[.. 72].bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 72);

		let (l, c, r) = unsafe { bits[4 .. 76].bit_span().align_to::<u16>() };
		assert_eq!(l.len() + c.len() + r.len(), 72);
	}

	#[test]
	fn modify() {
		let (a, b) = (0u16, 1u16);

		let mut bitspan = a.view_bits::<LocalBits>().bit_span();
		let mut expected = (&a as *const _ as usize, 16usize << 3);

		assert_eq!(bitspan.pointer().to_const(), &a as *const _);
		assert_eq!(bitspan.ptr.as_ptr() as usize, expected.0);
		assert_eq!(bitspan.len, expected.1);

		expected.0 = &b as *const _ as usize;
		unsafe {
			bitspan.set_pointer(&b as *const _);
		}
		assert_eq!(bitspan.pointer().to_const(), &b as *const _);
		assert_eq!(bitspan.ptr.as_ptr() as usize, expected.0);
		assert_eq!(bitspan.len, expected.1);

		let orig_head = bitspan.head();
		unsafe {
			bitspan.set_head(orig_head.next().0);
		}
		assert_eq!(bitspan.head(), orig_head.next().0);
	}

	#[test]
	fn mem_size() {
		assert_eq!(
			mem::size_of::<BitSpan<Const, LocalBits, usize>>(),
			mem::size_of::<*const [usize]>()
		);
		assert_eq!(
			mem::size_of::<Option<BitSpan<Const, LocalBits, usize>>>(),
			mem::size_of::<*const [usize]>()
		);
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn render() {
		#[cfg(not(feature = "std"))]
		use alloc::format;

		assert_eq!(
			format!("{}", Address::<u8, Const>::new(0).unwrap_err()),
			"Cannot use a null pointer"
		);
		assert_eq!(
			format!("{}", Address::<u16, Const>::new(0x13579).unwrap_err()),
			"Address 0x13579 must clear its least 1 bits to be aligned for u16"
		);
		assert_eq!(
			format!("{}", Address::<u32, Const>::new(0x13579).unwrap_err()),
			"Address 0x13579 must clear its least 2 bits to be aligned for u32"
		);
	}
}
