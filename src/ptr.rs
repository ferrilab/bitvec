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
	any::TypeId,
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

use tap::{
	conv::Conv,
	pipe::Pipe,
};

mod proxy;
mod range;
mod single;
mod span;

pub use self::{
	proxy::BitMut,
	range::BitPtrRange,
	single::BitPtr,
};

pub(crate) use self::span::{
	BitSpan,
	BitSpanError,
};

/** Copies `count` bits from `src` to `dst`. The source and destination may
overlap.

If the source and destination will *never* overlap, [`copy_nonoverlapping`] can
be used instead.

# Additional Constraints

`bitvec` considers it Undefined Behavior for two descriptors to overlap in
memory if their `BitOrder` parameters differ.

```rust
use bitvec::prelude::*;

let mut x = 0u8;
let lsb0: BitPtr<Lsb0, _, _> = (&mut x).into();
let msb0: BitPtr<Msb0, _, _> = (&x).into();

//  Defined: the regions do not select the same bits
bitvec::ptr::copy(lsb0, msb0, 4);

//  Undefined: the regions overlap in bits
bitvec::ptr::copy(lsb0, msb0, 5);
```

`bitvec` assumes that if `O1` and `O2` differ, then the regions will never
overlap in actual bits, and copies naïvely. If `O1` and `O2` are the same type,
then this performs overlap analysis to determine the copy direction.

If `T1` and `T2` have different memory types, then the behavior will follow the
tables of order/store traversal shown in the manual. Overlapping bytes in this
condition will likely clobber, and the function will make no attempt to preserve
them for correct copying.

Do not use this function on overlapping memory regions unless the source and
destination pointers have the same type parameters.

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
[`copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping
**/
pub unsafe fn copy<O1, O2, T1, T2>(
	src: BitPtr<Const, O1, T1>,
	dst: BitPtr<Mut, O2, T2>,
	count: usize,
) where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	if TypeId::of::<O1>() == TypeId::of::<O2>() {
		let (addr, head) = dst.raw_parts();
		let dst = BitPtr::<Mut, O1, T2>::new_unchecked(addr, head);

		let src_pair = src.range(count);
		let dst_pair = dst.range(count);

		if src_pair.contains(&dst) {
			for (src, dst) in src_pair.zip(dst_pair).rev() {
				write(dst, read(src));
			}
		}
		else {
			for (src, dst) in src_pair.zip(dst_pair) {
				write(dst, read(src));
			}
		}
	}
	//  Pointers with different orderings **cannot** overlap. Such an overlap is
	//  a fault in the caller, and `bitvec` undefines this behavior.
	else {
		for (src, dst) in src.range(count).zip(dst.range(count)) {
			write(dst, read(src));
		}
	}
}

/** Reads one bit from a memory location.

# Original

[`ptr::read`](core::ptr::read)

# API Differences

This must load the entire memory element from `*src`, then discard all bits but
the referent.

# Safety

Behavior is undefined if any of the following conditions are violated:

- `src` must be [valid] for reads.
- `src` must be a validly constructed pointer.
- `src` must point to a properly initialized value of type `T`.

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let x = 128u8;
let x_ptr: BitPtr<Msb0, _, _> = (&x).into();
assert!(
  unsafe { bitvec::ptr::read(x_ptr) }
);
```

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
**/
pub unsafe fn read<O, T>(src: BitPtr<Const, O, T>) -> bool
where
	O: BitOrder,
	T: BitStore,
{
	src.read()
}

/** Overwrites a memory location with the given bit.

# Original

[`ptr::write`](core::ptr::write)

# API Differences

The referent memory location must be read, modified in a register, then written
back.

# Safety

Behavior is undefined if any of the following conditions are violated:

- `dst` must be [valid] for writes.
- `dst` must be a validly constructed pointer.

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let mut x = 0u8;
let x_ptr: BitPtr<Lsb0, _, _> = (&mut x).into();
unsafe { bitvec::ptr::write(x_ptr, true); }
assert_eq!(x, 1);
```

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
**/
pub unsafe fn write<O, T>(dst: BitPtr<Mut, O, T>, src: bool)
where
	O: BitOrder,
	T: BitStore,
{
	dst.write(src);
}

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
pub struct Address<M, T>
where
	M: Mutability,
	T: BitStore,
{
	inner: NonNull<T>,
	_mut: PhantomData<M>,
}

impl<M, T> Address<M, T>
where
	M: Mutability,
	T: BitStore,
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
impl<M, T> Address<M, T>
where
	M: Mutability,
	T: BitStore,
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

	/// Offsets the address by `count` elements of `T`.
	///
	/// This delegates to `ptr::offset`, and panics if the sum comes out to the
	/// null pointer.
	pub(crate) unsafe fn offset(mut self, count: isize) -> Self {
		self.inner = self
			.inner
			.as_ptr()
			.offset(count)
			.pipe(NonNull::new)
			.expect("Offset cannot produce the null pointer");
		self
	}

	/// Offsets the address by `count` elements of `T`, wrapping around the
	/// address space.
	///
	/// This delegates to `ptr::wrapping_offset`, and panics if the sum comes
	/// out to the null pointer.
	pub(crate) unsafe fn wrapping_offset(mut self, count: isize) -> Self {
		self.inner = self
			.inner
			.as_ptr()
			.wrapping_offset(count)
			.pipe(NonNull::new)
			.expect("Wrapping offset cannot produce the null pointer");
		self
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
impl<T> Address<Const, T>
where T: BitStore
{
	#[inline(always)]
	pub(crate) unsafe fn assert_mut(self) -> Address<Mut, T> {
		let Self { inner, .. } = self;
		Address {
			inner,
			..Address::DANGLING
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> Address<Mut, T>
where T: BitStore
{
	/// Views the memory address as a mutable pointer.
	#[inline(always)]
	#[allow(clippy::wrong_self_convention)]
	pub(crate) fn to_mut(self) -> *mut T {
		self.inner.as_ptr()
	}

	#[inline(always)]
	pub(crate) fn immut(self) -> Address<Const, T> {
		let Self { inner, .. } = self;
		Address {
			inner,
			..Address::DANGLING
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, T> Clone for Address<M, T>
where
	M: Mutability,
	T: BitStore,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> From<&T> for Address<Const, T>
where T: BitStore
{
	#[inline(always)]
	fn from(addr: &T) -> Self {
		unsafe { Self::new_unchecked(addr as *const T as usize) }
	}
}

#[cfg(not(tarpaulin_include))]
impl<T> TryFrom<*const T> for Address<Const, T>
where T: BitStore
{
	type Error = AddressError<T>;

	#[inline(always)]
	fn try_from(addr: *const T) -> Result<Self, Self::Error> {
		Self::new(addr as usize)
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, T> From<&mut T> for Address<M, T>
where
	M: Mutability,
	T: BitStore,
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
impl<M, T> From<NonNull<T>> for Address<M, T>
where
	M: Mutability,
	T: BitStore,
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
impl<M, T> TryFrom<*mut T> for Address<M, T>
where
	M: Mutability,
	T: BitStore,
{
	type Error = AddressError<T>;

	#[inline(always)]
	fn try_from(addr: *mut T) -> Result<Self, Self::Error> {
		Self::new(addr as usize)
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, T> Debug for Address<M, T>
where
	M: Mutability,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(self, fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, T> Pointer for Address<M, T>
where
	M: Mutability,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(&self.to_const(), fmt)
	}
}

impl<M, T> Copy for Address<M, T>
where
	M: Mutability,
	T: BitStore,
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
