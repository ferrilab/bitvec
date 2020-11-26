/*! Bit-region pointer encoding.

This module defines the in-memory representations of various pointers to bits.
These include single-bit pointers, and pairs of them, which cannot be encoded
into a raw Rust pointer, and span descriptors, which can be encoded into a raw
Rust slice pointer and retyped as [`*BitSlice`].

This module makes the type symbols available to the public API, but they are all
opaque types and their values **cannot** be modified by user code. The encoding
system used to pack span descriptors into slice-pointer types is not public API,
and is not available for general inspection or modification.

[`*BitSlice`]: crate::slice::BitSlice
!*/

use crate::{
	mem::BitMemory,
	mutability::{
		Const,
		Mut,
		Mutability,
	},
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	any,
	convert::{
		Infallible,
		TryFrom,
	},
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
		Pointer,
	},
	marker::PhantomData,
	ptr::NonNull,
};

mod range;
mod single;
mod span;

pub use self::{
	range::BitPtrRange,
	single::BitPtr,
};

pub(crate) use self::span::{
	BitSpan,
	BitSpanError,
};

/** A weakly-typed memory address.

This wrapper adds easy, limited, type-casting support so that a memory address
can be reïnterpreted according to [`bitvec`]’s rules and needs.

This is not public API: it is an opaque helper type, exposed only as a
conversion target in pointer constructors.

# Type Parameters

- `T`: The referent data type.
- `M`: The mutability level of the contained address.

[`bitvec`]: crate
**/
#[repr(transparent)]
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	inner: NonNull<T>,
	_mut: PhantomData<M>,
}

impl<T, M> Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	/// Views a numeric address as a typed data address.
	pub(crate) fn new(addr: usize) -> Result<Self, AddressError<T>> {
		let align_mask = core::mem::align_of::<T>() - 1;
		if addr & align_mask != 0 {
			return Err(AddressError::Misaligned(addr as *const T));
		}
		let inner = NonNull::new(addr as *mut T).ok_or(AddressError::Null)?;
		Ok(Self {
			inner,
			_mut: PhantomData,
		})
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	pub(crate) const DANGLING: Self = Self {
		inner: NonNull::dangling(),
		_mut: PhantomData,
	};

	/// Views a numeric address as a typed data address.
	#[inline(always)]
	pub(crate) unsafe fn new_unchecked(addr: usize) -> Self {
		Self {
			inner: NonNull::new_unchecked(addr as *mut T),
			_mut: PhantomData,
		}
	}

	/// Views the memory address as an access pointer.
	#[inline(always)]
	pub(crate) fn to_access(self) -> *const T::Access {
		self.inner.as_ptr() as *const T::Access
	}

	/// Views the memory address as an immutable pointer.
	#[inline(always)]
	pub(crate) fn to_const(self) -> *const T {
		self.inner.as_ptr() as *const T
	}

	/// Gets the memory address as a non-null pointer.
	#[inline(always)]
	#[cfg(any(feature = "alloc", test))]
	pub(crate) fn to_nonnull(self) -> NonNull<T> {
		self.inner
	}

	/// Gets the memory address as a non-null byte pointer.
	#[inline(always)]
	#[cfg(any(feature = "alloc", test))]
	pub(crate) fn to_nonnull_u8(self) -> NonNull<u8> {
		self.inner.cast::<u8>()
	}

	/// Gets the numeric value of the address.
	#[inline(always)]
	pub(crate) fn value(self) -> usize {
		self.inner.as_ptr() as usize
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> Address<T, Mut>
where T: BitStore
{
	/// Views the memory address as a mutable pointer.
	#[inline(always)]
	#[allow(clippy::wrong_self_convention)]
	pub(crate) fn to_mut(self) -> *mut T {
		self.inner.as_ptr()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> Clone for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> From<&T> for Address<T, Const>
where T: BitStore
{
	#[inline(always)]
	fn from(addr: &T) -> Self {
		unsafe { Self::new_unchecked(addr as *const T as usize) }
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> TryFrom<*const T> for Address<T, Const>
where T: BitStore
{
	type Error = AddressError<T>;

	#[inline(always)]
	fn try_from(addr: *const T) -> Result<Self, Self::Error> {
		Self::new(addr as usize)
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> From<&mut T> for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn from(addr: &mut T) -> Self {
		Self {
			inner: addr.into(),
			_mut: PhantomData,
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> From<NonNull<T>> for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn from(addr: NonNull<T>) -> Self {
		Self {
			inner: addr,
			_mut: PhantomData,
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> TryFrom<*mut T> for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	type Error = AddressError<T>;

	#[inline(always)]
	fn try_from(addr: *mut T) -> Result<Self, Self::Error> {
		Self::new(addr as usize)
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> Debug for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(self, fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, M> Pointer for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(&self.to_const(), fmt)
	}
}

impl<T, M> Copy for Address<T, M>
where
	T: BitStore,
	M: Mutability,
{
}

/// An error produced when operating on `BitStore` memory addresses.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AddressError<T>
where T: BitStore
{
	/// The null address cannot be used.
	Null,
	/// The address was misaligned for the type.
	Misaligned(*const T),
}

impl<T> From<Infallible> for AddressError<T>
where T: BitStore
{
	fn from(_: Infallible) -> Self {
		Self::Null
	}
}

impl<T> Display for AddressError<T>
where T: BitStore
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		match *self {
			Self::Null => fmt.write_str("Cannot use a null pointer"),
			Self::Misaligned(ptr) => write!(
				fmt,
				"Address {:p} must clear its least {} bits to be aligned for {}",
				ptr,
				T::Mem::INDX - 3,
				any::type_name::<T>(),
			),
		}
	}
}

unsafe impl<T> Send for AddressError<T> where T: BitStore
{
}

unsafe impl<T> Sync for AddressError<T> where T: BitStore
{
}

#[cfg(feature = "std")]
impl<T> std::error::Error for AddressError<T> where T: BitStore
{
}

/** Forms a raw [`BitSlice`] pointer from its component data.

This function is safe, but actually using the return value is unsafe. See the
documentation of [`slice::bits_from_raw_parts`] for slice safety requirements.

# Original

[`ptr::slice_from_raw_parts`](core::ptr::slice_from_raw_parts)

# API Differences

`bitvec` uses a custom structure for `*const bool` that cannot be cast into a
raw pointer.

# Type Parameters

- `O`: The ordering of bits within elements `T`.
- `T`: The type of each memory element in the backing storage region.

# Returns

If the input parameters are valid, this returns a shared reference to a
[`BitSlice`]. The failure conditions that cause this to return an `Err`or are:

- `ptr` is not adequately aligned to `T`
- `ptr` is so high in the memory space that the region wraps to the base of the
memory space
- `len` is greater than [`BitSlice::MAX_BITS`]

# Examples

```rust
use bitvec::{
  index::BitIdx,
  order::Msb0,
  ptr as bp,
  slice::BitSlice,
};

let data = 0xF0u8;
let data_bit_ptr = bp::BitPtr::from(&data);
let bitspan: *const BitSlice<Msb0, u8>
  = bp::bitslice_from_raw_parts(data_bit_ptr, 4).unwrap();
assert_eq!(unsafe { &*bitspan }.len(), 4);
assert!(unsafe { &*bitspan }.all());
```

[`BitSlice`]: crate::slice::BitSlice
[`BitSlice::MAX_BITS`]: crate::slice::BitSlice::MAX_BITS
[`T::Mem::BITS`]: crate::mem::BitMemory::BITS
[`ptr::slice_from_raw_parts`]: core::ptr::slice_from_raw_parts
[`slice::bits_from_raw_parts`]: crate::slice::bits_from_raw_parts
**/
pub fn bitslice_from_raw_parts<O, T>(
	ptr: BitPtr<O, T, Const>,
	len: usize,
) -> Result<*const BitSlice<O, T>, BitSpanError<O, T>>
where
	O: BitOrder,
	T: BitStore,
{
	let (addr, head) = ptr.raw_parts();
	BitSpan::new(addr, head, len).map(BitSpan::to_bitslice_ptr)
}

/** Performs the same functionality as [`ptr::bitslice_from_raw_parts], except
that a raw mutable [`BitSlice`] pointer is returned, as opposed to a raw
immutable `BitSlice`.

See the documentation of [`bitslice_from_raw_parts`] for more details.

This function is safe, but actually using the return value is unsafe. See the
documentation of [`slice::bits_from_raw_parts_mut`] for slice safety requirements.

# Original

[`ptr::slice_from_raw_parts_mut](core::ptr::slice_from_raw_parts_mut)

# Type Parameters

- `O`: The ordering of bits within elements `T`.
- `T`: The type of each memory element in the backing storage region.

# Parameters

- `addr`: The base address of the memory region that the [`BitSlice`] covers.
- `head`: The index of the first live bit in `*addr`, at which the `BitSlice`
  begins. This is required to be in the range `0 .. T::Mem::BITS`.
- `bits`: The number of live bits, beginning at `head` in `*addr`, that the
  `BitSlice` contains. This must be no greater than [`BitSlice::MAX_BITS`].

# Returns

If the input parameters are valid, this returns `Some` shared reference to a
[`BitSlice`]. The failure conditions causing this to return `None` are:

- `head` is not less than [`T::Mem::BITS`]
- `bits` is greater than [`BitSlice::MAX_BITS`]
- `addr` is not adequately aligned to `T`
- `addr` is so high in the memory space that the region wraps to the base of the
  memory space

# Examples

```rust
use bitvec::{
  index::BitIdx,
  order::Msb0,
  ptr as bp,
  slice::BitSlice,
};

let mut data = 0x00u8;
let data_bit_ptr = bp::BitPtr::from(&mut data);
let bitspan: *mut BitSlice<Msb0, u8>
  = bp::bitslice_from_raw_parts_mut(data_bit_ptr, 4).unwrap();
assert_eq!(unsafe { &*bitspan }.len(), 4);
unsafe { &mut *bitspan }.set_all(true);
assert_eq!(data, 0xF0);
```

[`BitSlice`]: crate::slice::BitSlice
[`BitSlice::MAX_BITS`]: crate::slice::BitSlice::MAX_BITS
[`T::Mem::BITS`]: crate::mem::BitMemory::BITS
[`bitslice_from_raw_parts`]: crate::ptr::bitslice_from_raw_parts
[`slice::bits_from_raw_parts_mut`]: crate::slice::bits_from_raw_parts_mut
**/
pub fn bitslice_from_raw_parts_mut<O, T>(
	ptr: BitPtr<O, T, Mut>,
	len: usize,
) -> Result<*mut BitSlice<O, T>, BitSpanError<O, T>>
where
	O: BitOrder,
	T: BitStore,
{
	let (addr, head) = ptr.raw_parts();
	BitSpan::<O, T, Mut>::new(addr, head, len).map(BitSpan::to_bitslice_ptr_mut)
}
