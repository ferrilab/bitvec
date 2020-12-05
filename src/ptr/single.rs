//! Unencoded pointer to a single bit.

use crate::{
	access::BitAccess,
	index::BitIdx,
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
		BitPtrRange,
		BitSpan,
	},
	store::BitStore,
};

use core::{
	any::TypeId,
	cmp,
	convert::{
		TryFrom,
		TryInto,
	},
	fmt::{
		self,
		Binary,
		Debug,
		Formatter,
		Pointer,
	},
	hash::{
		Hash,
		Hasher,
	},
	marker::PhantomData,
	ptr::NonNull,
};

use tap::tap::Tap;

/** An opaque, non-null, pointer to a single bit in a memory element.

# Original

[`*const bool` and `*mut bool`](https://doc.rust-lang.org/std/primitive.pointer.html)

# API Differences

All pointer types in `bitvec` take type parameters to determine the type of the
underlying memory element and the ordering of bits within it.

Additionally, the types corresponding to raw pointers take a third type
parameter to encode mutability, rather than follow the standard library
convention of having two near-equivalent sibling types.

Lastly, this type is **not** a general pointer and **cannot** be used for
general I/O. It **only** supports reading or writing the exact bit it targets.
All other I/O APIs from the standard library are deliberately removed. If you
need them, please file an issue.

You may freely perform pointer arithmetic on this type.
**/
pub struct BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	/// Address of the referent element.
	addr: Address<T, M>,
	/// Index of the bit within the referent element.
	head: BitIdx<T::Mem>,
	/// The ordering used to map `self.head` to an electrical position.
	_ord: PhantomData<O>,
}

impl<O, T, M> BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	pub(crate) const DANGLING: Self = Self {
		addr: Address::DANGLING,
		head: BitIdx::ZERO,
		_ord: PhantomData,
	};

	/// Constructs a new single-bit pointer from an element address and a bit
	/// index.
	///
	/// # Parameters
	///
	/// - `addr`: Something that can be used as a memory address. This can be a
	///   reference, a raw pointer, or a [`NonNull`] pointer.
	/// - `head`: An index of a bit within the memory element at `addr`.
	///
	/// # Returns
	///
	/// An opaque pointer to a single bit within a memory element. This cannot
	/// be cast to any raw pointer type. If `addr` is null, or incorrectly
	/// aligned for `T`, this returns an error rather than a pointer.
	///
	/// [`NonNull`]: core::ptr::NonNull
	pub fn new<A>(addr: A, head: BitIdx<T::Mem>) -> Result<Self, AddressError<T>>
	where
		A: TryInto<Address<T, M>>,
		AddressError<T>: From<A::Error>,
	{
		let addr = addr.try_into()?;
		Ok(unsafe { Self::new_unchecked(addr, head) })
	}

	/// Constructs a new single-bit pointer from an element address and bit
	/// index, without checking that the address is correctly usable.
	///
	/// # Parameters
	///
	/// - `addr`: Something that can be used as a memory address. This can be a
	///   reference, a raw pointer, or a [`NonNull`] pointer.
	/// - `head`: An index of a bit within the memory element at `addr`.
	///
	/// # Returns
	///
	/// An opaque pointer to a single bit within a memory element. This cannot
	/// be cast to any raw pointer type.
	///
	/// # Safety
	///
	/// `addr` is not inspected for correctness, and invalid values can
	/// invalidate program state.
	pub unsafe fn new_unchecked<A>(addr: A, head: BitIdx<T::Mem>) -> Self
	where A: Into<Address<T, M>> {
		let addr = addr.into();
		Self {
			addr,
			head,
			_ord: PhantomData,
		}
	}

	/// Decomposes the pointer into its element address and bit index.
	pub fn raw_parts(self) -> (Address<T, M>, BitIdx<T::Mem>) {
		(self.addr, self.head)
	}

	/// Converts a base-pointer into a span-pointer by attaching a length.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `bits`: The length of the span.
	///
	/// # Returns
	///
	/// A span pointer beginning at `self` and running for `bits`.
	///
	/// # Safety
	///
	/// `bits` must be no greater than `BitSpan::REGION_MAX_BITS`. The high bits
	/// of the counter will be truncated during encoding.
	pub(crate) unsafe fn into_bitspan_unchecked(
		self,
		bits: usize,
	) -> BitSpan<O, T, M>
	{
		BitSpan::new_unchecked(self.addr, self.head, bits)
	}

	/// Constructs a bit-pointer range, starting at `self` and running for
	/// `count` bits.
	pub(crate) fn range(self, count: usize) -> BitPtrRange<O, T, M> {
		(self .. unsafe { self.add(count) }).into()
	}

	//  `pointer` fundamental API

	/// Tests if a bit-pointer is the null value.
	///
	/// This is always false, as null addresses are rejected during
	/// construction. Use `Option<BitPtr>` to encode nullability.
	///
	/// # Original
	///
	/// [`pointer::is_null`](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null)
	#[deprecated = "Bit pointers are never null"]
	pub fn is_null(self) -> bool {
		false
	}

	/// Casts to a pointer of another type.
	///
	/// This is not free! It encodes the pointer into the crate’s internal
	/// format, then decodes that as a base-address and bit-offset according to
	/// `U`. This permits casting to a wider or narrower element type without
	/// loss of information.
	///
	/// **HOWEVER!!** There is **no** guarantee that the pointer produced by
	/// this cast selects the same electrical bit as was selected before the
	/// cast! The `bitvec` addressing model is more complex than the
	/// byte-addressed address model of the processor.
	///
	/// Do not use this unless you are **absolutely** sure you know what you are
	/// doing.
	///
	/// # Original
	///
	/// [`pointer::cast`](https://doc.rust-lang.org/std/primitive.pointer.html#method.cast)
	///
	/// # Safety
	///
	/// This is subject to the same validity requirements as ordinary pointer
	/// casting. It presumes that all byte addresses for the type `U`, beginning
	/// at the address rounded down from the byte-address of type `T`, are valid
	/// to access. You are unlikely to encounter an address that violates this
	/// requirement.
	pub fn cast<U>(self) -> BitPtr<O, U, M>
	where U: BitStore {
		let (addr, head, _) = unsafe { self.into_bitspan_unchecked(1) }
			.cast::<U>()
			.raw_parts();
		BitPtr {
			addr,
			head,
			..BitPtr::DANGLING
		}
	}

	/// Calculates the offset from a pointer.
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::offset`](https://doc.rust-lang.org/std/primitive.pointer.html#method.offset)
	///
	/// # Safety
	///
	/// If any of the following conditions are violated, the result is Undefined
	/// Behavior:
	///
	/// - Both the starting and resulting pointer must be either in bounds or
	///   one byte past the end of the same allocated object. Note that in Rust,
	///   every (stack-allocated) variable is considered a separate allocated
	///   object.
	/// - The computed address-offset value, **in bytes**, cannot overflow an
	///   `isize`.
	/// - The offset being in bounds cannot rely on “wrapping around” the
	///   address space. That is, the infinite-precision sum, in bytes must fit
	///   in a `usize`.
	///
	/// Note that `bitvec` has additional restrictions that any given `BitSlice`
	/// region can only span ⅛th of a `usize`’s counting capacity. You *may* be
	/// able to produce a single allocation region larger than this, especially
	/// on 32-bit systems; pointer arithmetic within single regions is always
	/// defined, even if production of a `&BitSlice` descriptor for the entire
	/// region is not possible due to `bitvec` encoding restrictions.
	pub unsafe fn offset(self, count: isize) -> Self {
		let (elts, head) = self.head.offset(count);
		Self::new_unchecked(self.addr.offset(elts), head)
	}

	/// Calculates the offset from a pointer using wrapping arithmetic.
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::wrapping_offset`](https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_offset)
	///
	/// # Safety
	///
	/// The resulting pointer does not need to be in bounds, but it is
	/// potentially hazardous to dereference (which requires `unsafe fn` calls).
	///
	/// In particular, the resulting pointer remains attached to the same
	/// allocated object that `self` points to. It may not be used to access a
	/// different allocated object. Note that in Rust, every (stack-allocated)
	/// variable is considered a separate allocated object.
	///
	/// In other words, `x.wrapping_offset((y as usize).wrapping_sub(x as
	/// usize))` is not the same as `y`, and dereferencing it is undefined
	/// behavior unless `x` and `y` point into the same allocated object.
	pub unsafe fn wrapping_offset(self, count: isize) -> Self {
		let (elts, head) = self.head.offset(count);
		Self::new_unchecked(self.addr.wrapping_offset(elts), head)
	}

	/// Calculates the distance between two pointers. The returned value is in
	/// units of bits.
	///
	/// This function is the inverse of [`offset`].
	///
	/// [`offset`]: Self::offset
	///
	/// # Original
	///
	/// [`pointer::offset_from`](https://doc.rust-lang.org/std/primitive.pointer.html#method.offset_from)
	///
	/// # Safety
	///
	/// If any of the following conditions are violated, the result is Undefined
	/// Behavior:
	///
	/// - Both the starting and other pointer must be either in bounds or one
	///   byte past the end of the same allocated object. Note that in Rust,
	///   every (stack-allocated) variable is considered a separate allocated
	///   object.
	/// - Both pointers must be derived from a pointer to the same object. (See
	///   below for an example.)
	/// - The distance between the pointers, in bytes, cannot overflow an
	///   `isize`.
	/// - The distance being in bounds cannot rely on “wrapping around” the
	///   address space.
	pub unsafe fn offset_from<U, N>(self, other: BitPtr<O, U, N>) -> isize
	where
		U: BitStore,
		N: Mutability,
	{
		let this = self.addr.value() as isize;
		let that = other.addr.value() as isize;
		//  Get the byte distance between `self` and `other`,
		this.wrapping_sub(that)
			//  Multiply it to the bit distance between their base bits,
			.wrapping_mul(<u8 as BitMemory>::BITS as isize)
			//  Add the bit-offset of `self`,
			.wrapping_add(self.head.value() as isize)
			//  And subtract the bit-offset of `other`.
			.wrapping_sub(other.head.value() as isize)
	}

	/// Calculates the offset from a pointer (convenience for `.offset(count as
	/// isize)`).
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::add`](https://doc.rust-lang.org/std/primitive.pointer.html#method.add)
	///
	/// # Safety
	///
	/// If any of the following conditions are violated, the result is Undefined
	/// Behavior:
	///
	/// - Both the starting and resulting pointer must be either in bounds or
	///   one byte past the end of the same allocated object. Note that in Rust,
	///   every (stack-allocated) variable is considered a separate allocated
	///   object.
	/// - The computed offset, in bytes, cannot overflow an `isize`.
	/// - The offset being in bounds cannot rely on "wrapping around" the
	///   address space. That is, the infinite-precision sum must fit in a
	///   `usize`.
	///
	/// Note that `bitvec` has additional restrictions that any given `BitSlice`
	/// region can only span ⅛th of a `usize`’s counting capacity. You *may* be
	/// able to produce a single allocation region larger than this, especially
	/// on 32-bit systems; pointer arithmetic within single regions is always
	/// defined, even if production of a `&BitSlice` descriptor for the entire
	/// region is not possible due to `bitvec` encoding restrictions.
	pub unsafe fn add(self, count: usize) -> Self {
		self.offset(count as isize)
	}

	/// Calculates the offset from a pointer (convenience for `.offset((count as
	/// isize).wrapping_neg())`).
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::add`](https://doc.rust-lang.org/std/primitive.pointer.html#method.add)
	///
	/// # Safety
	///
	/// If any of the following conditions are violated, the result is Undefined
	/// Behavior:
	///
	/// - Both the starting and resulting pointer must be either in bounds or
	///   one byte past the end of the same allocated object. Note that in Rust,
	///   every (stack-allocated) variable is considered a separate allocated
	///   object.
	/// - The computed offset, in bytes, cannot overflow an `isize`.
	/// - The offset being in bounds cannot rely on "wrapping around" the
	///   address space. That is, the infinite-precision sum must fit in a
	///   `usize`.
	///
	/// Note that `bitvec` has additional restrictions that any given `BitSlice`
	/// region can only span ⅛th of a `usize`’s counting capacity. You *may* be
	/// able to produce a single allocation region larger than this, especially
	/// on 32-bit systems; pointer arithmetic within single regions is always
	/// defined, even if production of a `&BitSlice` descriptor for the entire
	/// region is not possible due to `bitvec` encoding restrictions.
	pub unsafe fn sub(self, count: usize) -> Self {
		self.offset(-(count as isize))
	}

	/// Calculates the offset from a pointer using wrapping arithmetic
	/// (convenience for `.wrapping_add(count as isize)`).
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::wrapping_add`](https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_add)
	///
	/// # Safety
	///
	/// The resulting pointer does not need to be in bounds, but it is
	/// potentially hazardous to dereference (which requires `unsafe fn` calls).
	///
	/// In particular, the resulting pointer remains attached to the same
	/// allocated object that `self` points to. It may not be used to access a
	/// different allocated object. Note that in Rust, every (stack-allocated)
	/// variable is considered a separate allocated object.
	///
	/// In other words, `x.wrapping_add((y as usize).wrapping_sub(x as usize))`
	/// is not the same as `y`, and dereferencing it is undefined behavior
	/// unless `x` and `y` point into the same allocated object.
	pub unsafe fn wrapping_add(self, count: usize) -> Self {
		self.wrapping_offset(count as isize)
	}

	/// Calculates the offset from a pointer using wrapping arithmetic
	/// (convenience for `.wrapping_sub(count as isize)`).
	///
	/// `count` is measured in bits; e.g. a `count` of 3 represents a pointer
	/// offset of 3 bits, which may or may not be in the original memory element
	/// address.
	///
	/// # Original
	///
	/// [`pointer::wrapping_sub`](https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_sub)
	///
	/// # Safety
	///
	/// The resulting pointer does not need to be in bounds, but it is
	/// potentially hazardous to dereference (which requires `unsafe fn` calls).
	///
	/// In particular, the resulting pointer remains attached to the same
	/// allocated object that `self` points to. It may not be used to access a
	/// different allocated object. Note that in Rust, every (stack-allocated)
	/// variable is considered a separate allocated object.
	///
	/// In other words, `x.wrapping_sub((y as usize).wrapping_sub(x as usize))`
	/// is not the same as `y`, and dereferencing it is undefined ehavior unless
	/// `x` and `y` point into the same allocated object.
	pub unsafe fn wrapping_sub(self, count: usize) -> Self {
		self.wrapping_offset(-(count as isize))
	}

	/// Reads the referent bit out of memory.
	///
	/// # Safety
	///
	/// This is `unsafe`, because there is no requirement that the pointer
	/// target validly initialized, or even allocated, memory. You must
	/// guarantee that the referent element is allocated, initialized, and not
	/// in aliasing violations, before calling this.
	pub unsafe fn read(self) -> bool {
		self.addr.to_const().read().get_bit::<O>(self.head)
	}
}

impl<O, T> BitPtr<O, T, Const>
where
	O: BitOrder,
	T: BitStore,
{
	/// Raises an immutable pointer to mutable.
	///
	/// # Safety
	///
	/// This pointer **must** have previously been mutable, and lowered to
	/// immutable through [`.immut()`].
	///
	/// [`.immut()`]: BitPtr::immut
	pub unsafe fn assert_mut(self) -> BitPtr<O, T, Mut> {
		let Self { addr, head, .. } = self;
		BitPtr {
			addr: addr.assert_mut(),
			head,
			..BitPtr::DANGLING
		}
	}
}

impl<O, T> BitPtr<O, T, Mut>
where
	O: BitOrder,
	T: BitStore,
{
	/// Lower a mutable pointer to immutable.
	pub fn immut(self) -> BitPtr<O, T, Const> {
		let Self { addr, head, .. } = self;
		BitPtr {
			addr: addr.immut(),
			head,
			..BitPtr::DANGLING
		}
	}

	/// Writes a bit into the referent slot.
	///
	/// # Safety
	///
	/// This is `unsafe`, because there is no requirement that the pointer
	/// target validily initialized, or even allocated, memory. You must
	/// guarantee that the referent element is allocated, initialized, and not
	/// in aliasing violations, before calling this.
	pub unsafe fn write(self, value: bool) {
		(&*self.addr.to_access()).write_bit::<O>(self.head, value)
	}

	/// Replaces the bit at `self` with `src`, returning the old bit.
	///
	/// # Original
	///
	/// [`pointer::replace`](https://doc.rust-lang.org/std/primitive.pointer.html#method.replace)
	pub unsafe fn replace(self, src: bool) -> bool {
		self.read().tap(|_| self.write(src))
	}

	/// Swaps the bits at two mutable locations. They are permitted to be the
	/// same location.
	///
	/// # Original
	///
	/// [`pointer::swap`](https://doc.rust-lang.org/std/primitive.pointer.html#method.swap)
	///
	/// # API Differences
	///
	/// This does not require that the two pointers be of exactly the same type.
	pub unsafe fn swap<O2, T2>(self, other: BitPtr<O2, T2, Mut>)
	where
		O2: BitOrder,
		T2: BitStore,
	{
		let (a, b) = (self.read(), other.read());
		self.write(b);
		other.write(a);
	}
}

impl<O, T, M> Clone for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn clone(&self) -> Self {
		*self
	}
}

impl<O, T, M> Eq for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
}

impl<O, T, M> Ord for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.partial_cmp(&other)
			.expect("BitPtr should have a total ordering")
	}
}

impl<O, T, U, M, N> PartialEq<BitPtr<O, U, N>> for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	U: BitStore,
	M: Mutability,
	N: Mutability,
{
	fn eq(&self, other: &BitPtr<O, U, N>) -> bool {
		if TypeId::of::<T::Mem>() != TypeId::of::<U::Mem>() {
			return false;
		}
		self.addr.value() == other.addr.value()
			&& self.head.value() == other.head.value()
	}
}

impl<O, T, U, M, N> PartialOrd<BitPtr<O, U, N>> for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	U: BitStore,
	M: Mutability,
	N: Mutability,
{
	fn partial_cmp(&self, other: &BitPtr<O, U, N>) -> Option<cmp::Ordering> {
		if TypeId::of::<T::Mem>() != TypeId::of::<U::Mem>() {
			return None;
		}
		match (self.addr.value()).cmp(&(other.addr.value())) {
			cmp::Ordering::Equal => {
				self.head.value().partial_cmp(&other.head.value())
			},
			ord => return Some(ord),
		}
	}
}

impl<O, T> From<&T> for BitPtr<O, T, Const>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(src: &T) -> Self {
		Self {
			addr: src.into(),
			..Self::DANGLING
		}
	}
}

impl<O, T> From<&mut T> for BitPtr<O, T, Mut>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(src: &mut T) -> Self {
		Self {
			addr: src.into(),
			..Self::DANGLING
		}
	}
}

impl<O, T> From<NonNull<T>> for BitPtr<O, T, Mut>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(src: NonNull<T>) -> Self {
		Self {
			addr: src.into(),
			..Self::DANGLING
		}
	}
}

impl<O, T> TryFrom<*const T> for BitPtr<O, T, Const>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = AddressError<T>;

	fn try_from(src: *const T) -> Result<Self, Self::Error> {
		Ok(Self {
			addr: src.try_into()?,
			..Self::DANGLING
		})
	}
}

impl<O, T> TryFrom<*mut T> for BitPtr<O, T, Mut>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = AddressError<T>;

	fn try_from(src: *mut T) -> Result<Self, Self::Error> {
		Ok(Self {
			addr: src.try_into()?,
			..Self::DANGLING
		})
	}
}

impl<O, T, M> Debug for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(self, fmt)
	}
}

impl<O, T, M> Pointer for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(&self.addr, fmt)?;
		fmt.write_str("_")?;
		Binary::fmt(&self.head, fmt)
	}
}

impl<O, T, M> Hash for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		hasher.write_usize(self.addr.value());
		hasher.write_u8(self.head.value());
	}
}

impl<O, T, M> Copy for BitPtr<O, T, M>
where
	O: BitOrder,
	T: BitStore,
	M: Mutability,
{
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::order::Lsb0;

	#[test]
	fn ctor() {
		let data = 0u16;
		let head = BitIdx::new(5).unwrap();

		let bitptr = BitPtr::<Lsb0, _, _>::new(&data, head).unwrap();
		let (addr, indx) = bitptr.raw_parts();
		assert_eq!(addr.to_const(), &data as *const _);
		assert_eq!(indx.value(), 5);
	}
}
