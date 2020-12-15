//! A pointer to a single bit.

use crate::{
	access::BitAccess,
	index::{
		BitIdx,
		BitIdxError,
	},
	mem::BitMemory,
	mutability::{
		Const,
		Mut,
		Mutability,
	},
	order::{
		BitOrder,
		Lsb0,
	},
	ptr::{
		Address,
		AddressError,
		BitPtrRange,
		BitRef,
		BitSpan,
	},
	store::BitStore,
};

use wyz::fmt::FmtForward;

use core::{
	any::{
		type_name,
		TypeId,
	},
	cmp,
	convert::{
		Infallible,
		TryFrom,
		TryInto,
	},
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
		Pointer,
	},
	hash::{
		Hash,
		Hasher,
	},
	marker::PhantomData,
	ops::Deref,
	ptr,
};

/** Pointer to an individual bit in a memory element. Analagous to `*bool`.

# Original

[`*bool`](https://doc.rust-lang.org/std/primitive.pointer.html) and
[`NonNull<bool>`](core::ptr::NonNull)

# API Differences

This must be a structure, rather than a raw pointer, for two reasons:

- It is larger than a raw pointer.
- Raw pointers are not `#[fundamental]` and cannot have foreign implementations.

Additionally, rather than create two structures to map to `*const bool` and
`*mut bool`, respectively, this takes mutability as a type parameter.

Because the encoded span pointer requires that memory addresses are well
aligned, this type also imposes the alignment requirement and refuses
construction for misaligned element addresses. While this type is used in the
API equivalent of ordinary raw pointers, it is restricted in value to only be
*references* to memory elements.

# ABI Differences

This has alignment `1`, rather than an alignment to the processor word. This is
necessary for some crate-internal optimizations.

# Type Parameters

- `M`: Marks whether the pointer permits mutation of memory through it.
- `O`: The ordering of bits within a memory element.
- `T`: A memory type used to select both the register size and the access
  behavior when performing loads/stores.

# Usage

This structure is used as the [`bitvec`] equivalent to `*bool`. It is used in
all raw-pointer APIs, and provides behavior to emulate raw pointers. It cannot
be directly dereferenced, as it is not a pointer; it can only be transformed
back into higher referential types, or used in [`bitvec::ptr`] free functions.

These pointers can never be null, or misaligned.

[`bitvec`]: crate
[`bitvec::ptr`]: crate::ptr
**/
#[repr(C, packed)]
pub struct BitPtr<M, O = Lsb0, T = usize>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	/// Memory addresses must be well-aligned and non-null.
	addr: Address<M, T>,
	/// The index of the referent bit within `*addr`.
	head: BitIdx<T::Mem>,
	/// The ordering used to select the bit at `head` in `*addr`.
	_ord: PhantomData<O>,
}

impl<M, O, T> BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	/// The dangling pointer. This selects the starting bit of the `T` dangling
	/// address.
	pub const DANGLING: Self = Self {
		addr: Address::DANGLING,
		head: BitIdx::ZERO,
		_ord: PhantomData,
	};

	/// Loads the address field, sidestepping any alignment problems.
	pub(crate) fn get_addr(&self) -> Address<M, T> {
		unsafe {
			ptr::read_unaligned(self as *const Self as *const Address<M, T>)
		}
	}

	/// Produces the dangling pointer, [`Self::DANGLING`].
	///
	/// [`Self::DANGLING`]: Self::DANGLING
	pub fn dangling() -> Self {
		Self::DANGLING
	}

	/// Constructs a `BitPtr` from an `Address`, using the zero `BitIdx`.
	pub(crate) fn from_address(addr: Address<M, T>) -> Self {
		Self::new(addr, BitIdx::ZERO)
	}

	/// Tries to construct a `BitPtr` from a memory location and a bit index.
	///
	/// # Type Parameters
	///
	/// - `A`: This accepts anything that may be used as a memory address.
	///
	/// # Parameters
	///
	/// - `addr`: The memory address to use in the `BitPtr`. If this value
	///   violates the [`Address`] rules, then its conversion error will be
	///   returned.
	/// - `head`: The index of the bit in `*addr` that this pointer selects. If
	///   this value violates the [`BitIdx`] rules, then its conversion error
	///   will be returned.
	///
	/// # Returns
	///
	/// A new `BitPtr`, selecting the memory location `addr` and the bit `head`.
	/// If either `addr` or `head` are invalid values, then this propagates
	/// their error.
	///
	/// [`Address`]: crate::ptr::Address
	/// [`BitIdx`]: crate::index::BitIdx
	pub fn try_new<A>(addr: A, head: u8) -> Result<Self, BitPtrError<T>>
	where
		A: TryInto<Address<M, T>>,
		BitPtrError<T>: From<A::Error>,
	{
		Ok(Self::new(addr.try_into()?, BitIdx::new(head)?))
	}

	/// Constructs a `BitPtr` from a memory location and a bit index.
	///
	/// Since this requires that the address and bit index are already
	/// well-formed, it can assemble the `BitPtr` without inspecting their
	/// values.
	///
	/// # Parameters
	///
	/// - `addr`: A well-formed memory address of `T`.
	/// - `head`: A well-formed bit index within `T`.
	///
	/// # Returns
	///
	/// A `BitPtr` selecting the `head` bit in the location `addr`.
	pub fn new(addr: Address<M, T>, head: BitIdx<T::Mem>) -> Self {
		Self {
			addr,
			head,
			_ord: PhantomData,
		}
	}

	/// Decomposes the pointer into its element address and bit index.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// - `.0`: The memory address in which the referent bit is located.
	/// - `.1`: The index of the referent bit within `*.0`.
	pub fn raw_parts(self) -> (Address<M, T>, BitIdx<T::Mem>) {
		(self.addr, self.head)
	}

	/// Converts `self` into a span descriptor for a single bit.
	///
	/// `self` must not be targeting the very last bit in the address space.
	pub(crate) unsafe fn span_unchecked(self, bits: usize) -> BitSpan<M, O, T> {
		BitSpan::new_unchecked(self.addr, self.head, bits)
	}

	/// Produces a pointer range starting at `self` and running for `count`
	/// bits.
	///
	/// This calls `self.add(count)`, then bundles the resulting pointer as the
	/// high end of the produced range.
	///
	/// # Parameters
	///
	/// - `self`: The starting pointer of the produced range.
	/// - `count`: The number of bits that the produced range includes.
	///
	/// # Returns
	///
	/// A half-open range of pointers, beginning at (and including) `self`,
	/// running for `count` bits, and ending at (and excluding)
	/// `self.add(count)`.
	///
	/// # Safety
	///
	/// `count` cannot violate the constraints in [`add`].
	///
	/// [`add`]: Self::add
	pub unsafe fn range(self, count: usize) -> BitPtrRange<M, O, T> {
		BitPtrRange {
			start: self,
			end: self.add(count),
		}
	}

	/// Converts a bit-pointer into a proxy bit-reference.
	///
	/// # Safety
	///
	/// The pointer must be valid to dereference.
	pub unsafe fn into_bitref<'a>(self) -> BitRef<'a, M, O, T> {
		BitRef::from_bitptr(self)
	}

	/// Removes write permissions from a bit-pointer.
	pub fn immut(self) -> BitPtr<Const, O, T> {
		let Self { addr, head, .. } = self;
		BitPtr {
			addr: addr.immut(),
			head,
			..BitPtr::DANGLING
		}
	}

	/// Adds write permissions to a bit-pointer.
	///
	/// # Safety
	///
	/// This pointer must have been derived from a `*mut` pointer.
	pub unsafe fn assert_mut(self) -> BitPtr<Mut, O, T> {
		let Self { addr, head, .. } = self;
		BitPtr {
			addr: addr.assert_mut(),
			head,
			..BitPtr::DANGLING
		}
	}

	//  `pointer` inherent API

	/// Tests if a bit-pointer is the null value.
	///
	/// This is always false, as `BitPtr` is a `NonNull` internally. Use
	/// `Option<BitPtr>` to express the potential for a null pointer.
	///
	/// # Original
	///
	/// [`pointer::is_null`](https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null)
	#[deprecated = "`BitPtr` is never null"]
	pub fn is_null(self) -> bool {
		false
	}

	/// Casts to a bit-pointer of another storage type, preserving the
	/// bit-ordering and mutability permissions.
	///
	/// # Original
	///
	/// [`pointer::cast`](https://doc.rust-lang.org/std/primitive.pointer.html#method.cast)
	///
	/// # Behavior
	///
	/// This is not a free typecast! It encodes the pointer as a crate-internal
	/// span descriptor, casts the span descriptor to the `U` storage element
	/// parameter, then decodes the result. This preserves general correctness,
	/// but will likely change both the virtual and physical bits addressed by
	/// this pointer.
	pub fn cast<U>(self) -> BitPtr<M, O, U>
	where U: BitStore {
		let (addr, head, _) =
			unsafe { self.span_unchecked(1) }.cast::<U>().raw_parts();
		BitPtr::new(addr, head)
	}

	/// Produces a proxy reference to the referent bit.
	///
	/// Because `BitPtr` is a non-null, well-aligned, pointer, this never
	/// returns `None`.
	///
	/// # Original
	///
	/// [`pointer::as_ref`](https://doc.rust-lang.org/std/primitive.pointer.html#method.as_ref)
	///
	/// # API Differences
	///
	/// This produces a proxy type rather than a true reference. The proxy
	/// implements `Deref<Target = bool>`, and can be converted to `&bool` with
	/// `&*`.
	///
	/// # Safety
	///
	/// Since `BitPtr` does not permit null or misaligned pointers, this method
	/// will always dereference the pointer and you must ensure the following
	/// conditions are met:
	///
	/// - the pointer must be dereferencable as defined in the standard library
	///   documentation
	/// - the pointer must point to an initialized instance of `T`
	/// - you must ensure that no other pointer will race to modify the referent
	///   location while this call is reading from memory to produce the proxy
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let data = 1u8;
	/// let ptr = BitPtr::<_, Lsb0, _>::from_ref(&data, 0).unwrap();
	/// let val = unsafe { ptr.as_ref() }.unwrap();
	/// assert!(*val);
	/// ```
	pub unsafe fn as_ref<'a>(self) -> Option<BitRef<'a, Const, O, T>> {
		Some(BitRef::from_bitptr(self.immut()))
	}

	/// Calculates the offset from a pointer.
	///
	/// `count` is in units of bits.
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
	/// - The computed offset, **in bytes**, cannot overflow an `isize`.
	/// - The offset being in bounds cannot rely on “wrapping around” the
	///   address space. That is, the infinite-precision sum, **in bytes** must
	///   fit in a `usize`.
	///
	/// These pointers are almost always derived from [`BitSlice`] regions,
	/// which have an encoding limitation that the high three bits of the length
	/// counter are zero, so `bitvec` pointers are even less likely than
	/// ordinary pointers to run afoul of these limitations.
	///
	/// Use [`wrapping_offset`] if you expect to risk hitting the high edge of
	/// the address space.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let data = 5u8;
	/// let ptr = BitPtr::<_, Lsb0, _>::from_ref(&data, 0).unwrap();
	/// assert!(*ptr);
	/// assert!(!* unsafe { ptr.offset(1) });
	/// assert!(* unsafe { ptr.offset(2) });
	/// ```
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	/// [`wrapping_offset`]: Self::wrapping_offset
	pub unsafe fn offset(self, count: isize) -> Self {
		let (elts, head) = self.head.offset(count);
		Self::new(self.addr.offset(elts), head)
	}

	/// Calculates the offset from a pointer using wrapping arithmetic.
	///
	/// `count` is in units of bits.
	///
	/// # Original
	///
	/// [`pointer::wrapping_offset`](https://doc.rust/lang.org/std/primitive.pointer.html#method.wrapping_offset)
	///
	/// # Safety
	///
	/// The resulting pointer does not need to be in bounds, but it is
	/// potentially hazardous to dereference.
	///
	/// In particular, the resulting pointer remains attached to the same
	/// allocated object that `self` points to. It may *not* be used to access a
	/// different allocated object. Note that in Rust, every (stack-allocated)
	/// variable is considered a separate allocated object.
	///
	/// In other words, `x.wrapping_offset((y as usize).wrapping_sub(x as
	/// usize)` is not the same as `y`, and dereferencing it is undefined
	/// behavior unless `x` and `y` point into the same allocated object.
	///
	/// Compared to [`offset`], this method basically delays the requirement of
	/// staying within the same allocated object: [`offset`] is immediate
	/// Undefined Behavior when crossing object boundaries; `wrapping_offset`
	/// produces a pointer but still leads to Undefined Behavior if that pointer
	/// is dereferenced. [`offset`] can be optimized better and is thus
	/// preferable in performance-sensitive code.
	///
	/// If you need to cross object boundaries, destructure this pointer into
	/// its base address and bit index, cast the base address to an integer, and
	/// do the arithmetic in the purely integer space.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let data = 0u8;
	/// let mut ptr = BitPtr::<_, Lsb0, _>::from_ref(&data, 0).unwrap();
	/// let end = ptr.wrapping_offset(8);
	/// while ptr < end {
	///   # #[cfg(feature = "std")] {
	///   println!("{}", *ptr);
	///   # }
	///   ptr = ptr.wrapping_offset(3);
	/// }
	/// ```
	///
	/// [`offset`]: Self::offset
	pub fn wrapping_offset(self, count: isize) -> Self {
		let (elts, head) = self.head.offset(count);
		Self::new(self.addr.wrapping_offset(elts), head)
	}

	/// Calculates the distance between two pointers. The returned value is in
	/// units of bits.
	///
	/// This function is the inverse of [`offset`].
	///
	/// # Original
	///
	/// [`pointer::offset`](https://doc.rust-lang.org/std/primitive.pointer.html#method.offset_from)
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
	/// - Both pointers must be *derived from* a pointer to the same object.
	/// - The distance between the pointers, **in bytes**, cannot overflow an
	///   `isize`.
	/// - The distance being in bounds cannot rely on “wrapping around” the
	///   address space.
	///
	/// These pointers are almost always derived from [`BitSlice`] regions,
	/// which have an encoding limitation that the high three bits of the length
	/// counter are zero, so `bitvec` pointers are even less likely than
	/// ordinary pointers to run afoul of these limitations.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let data = 0u16;
	/// let base = BitPtr::<_, Lsb0, _>::from_ref(&data, 0).unwrap();
	/// let low = unsafe { base.add(5) };
	/// let high = unsafe { low.add(6) };
	/// unsafe {
	///   assert_eq!(high.offset_from(low), 6);
	///   assert_eq!(low.offset_from(high), -6);
	///   assert_eq!(low.offset(6), high);
	///   assert_eq!(high.offset(-6), low);
	/// }
	/// ```
	///
	/// *Incorrect* usage:
	///
	/// ```rust,no_run
	/// use bitvec::prelude::*;
	///
	/// let a = 0u8;
	/// let b = !0u8;
	/// let a_ptr = BitPtr::<_, Lsb0, _>::from_ref(&a, 0).unwrap();
	/// let b_ptr = BitPtr::<_, Lsb0, _>::from_ref(&b, 0).unwrap();
	/// let diff = (b_ptr.pointer() as isize)
	///   .wrapping_sub(a_ptr.pointer() as isize)
	///   // Remember: raw pointers are byte-addressed,
	///   // but these are bit-addressed.
	///   .wrapping_mul(8);
	/// // Create a pointer to `b`, derived from `a`.
	/// let b_ptr_2 = a_ptr.wrapping_offset(diff);
	///
	/// // The pointers are *arithmetically* equal now
	/// assert_eq!(b_ptr, b_ptr_2);
	/// // Undefined Behavior!
	/// unsafe {
	///   b_ptr_2.offset_from(b_ptr);
	/// }
	/// ```
	///
	/// [`offset`]: Self::offset
	pub unsafe fn offset_from(self, origin: Self) -> isize {
		self.addr
			.value()
			.wrapping_sub(origin.addr.value())
			.wrapping_mul(<u8 as BitMemory>::BITS as usize)
			.wrapping_add(self.head.value() as usize)
			.wrapping_sub(origin.head.value() as usize) as isize
	}

	/// Calculates the offset from a pointer (convenience for `.offset(count as
	/// isize)`).
	///
	/// `count` is in units of bits.
	///
	/// # Original
	///
	/// [`pointer::add`](https://doc.rust-lang.org/std/primitive.pointer.html#method.add)
	///
	/// # Safety
	///
	/// See [`offset`].
	///
	/// [`offset`]: Self::offset
	pub unsafe fn add(self, count: usize) -> Self {
		self.offset(count as isize)
	}

	/// Calculates the offset from a pointer (convenience for `.offset((count as
	/// isize).wrapping_neg())`).
	///
	/// `count` is in units of bits.
	///
	/// # Original
	///
	/// [`pointer::sub`](https://doc.rust-lang.org/std/primitive.pointer.html#method.sub)
	///
	/// # Safety
	///
	/// See [`offset`].
	///
	/// [`offset`]: Self::offset
	pub unsafe fn sub(self, count: usize) -> Self {
		self.offset((count as isize).wrapping_neg())
	}

	/// Calculates the offset from a pointer using wrapping arithmetic
	/// (convenience for `.wrapping_offset(count as isize)`).
	///
	/// # Original
	///
	/// [`pointer::wrapping_add`](https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_add)
	///
	/// # Safety
	///
	/// See [`wrapping_offset`].
	///
	/// [`wrapping_offset`]: Self::wrapping_offset
	pub fn wrapping_add(self, count: usize) -> Self {
		self.wrapping_offset(count as isize)
	}

	/// Calculates the offset from a pointer using wrapping arithmetic
	/// (convenience for `.wrapping_offset((count as isize).wrapping_neg())`).
	///
	/// # Original
	///
	/// [`pointer::wrapping_sub`](https://doc.rust-lang.org/std/primitive.pointer.html#method.wrapping_sub)
	///
	/// # Safety
	///
	/// See [`wrapping_offset`].
	///
	/// [`wrapping_offset`]: Self::wrapping_offset
	pub fn wrapping_sub(self, count: usize) -> Self {
		self.wrapping_offset((count as isize).wrapping_neg())
	}

	/// Reads the bit from `*self`.
	///
	/// # Original
	///
	/// [`pointer::read`](https://doc.rust-lang.org/std/primitive.pointer.html#method.read)
	///
	/// # Safety
	///
	/// See [`ptr::read`] for safety concerns and examples.
	///
	/// [`ptr::read`]: crate::ptr::read
	pub unsafe fn read(self) -> bool {
		(&*self.addr.to_const())
			.load_value()
			.get_bit::<O>(self.head)
	}

	/// Performs a volatile read of the bit from `self`.
	///
	/// Volatile operations are intended to act on I/O memory, and are
	/// guaranteed to not be elided or reördered by the compiler across other
	/// volatile operations.
	///
	/// # Original
	///
	/// [`pointer::read_volatile`](https://doc.rust-lang.org/std/primitive.pointer.html#method.read_volatile)
	///
	/// # Safety
	///
	/// See [`ptr::read_volatile`] for safety concerns and examples.
	///
	/// [`ptr::read_volatile`]: crate::ptr::read_volatile
	pub unsafe fn read_volatile(self) -> bool {
		self.addr.to_const().read_volatile().get_bit::<O>(self.head)
	}

	/// Copies `count` bits from `self` to `dest`. The source and destination
	/// may overlap.
	///
	/// NOTE: this has the *same* argument order as [`ptr::copy`].
	///
	/// # Original
	///
	/// [`pointer::copy_to`](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to)
	///
	/// # Safety
	///
	/// See [`ptr::copy`] for safety concerns and examples.
	///
	/// [`ptr::copy`]: crate::ptr::copy
	pub unsafe fn copy_to<O2, T2>(self, dest: BitPtr<Mut, O2, T2>, count: usize)
	where
		O2: BitOrder,
		T2: BitStore,
	{
		if TypeId::of::<O>() == TypeId::of::<O2>() {
			let (addr, head) = dest.raw_parts();
			let dst = BitPtr::<Mut, O, T2>::new(addr, head);
			let src_pair = self.range(count);

			if src_pair.contains(&dst) {
				for (from, to) in src_pair.zip(dest.range(count)).rev() {
					to.write(from.read());
				}
				return;
			}
		}
		self.copy_to_nonoverlapping(dest, count);
	}

	/// Copies `count` bits from `self` to `dest`. The source and destination
	/// may *not* overlap.
	///
	/// NOTE: this has the *same* argument order as
	/// [`ptr::copy_nonoverlapping`].
	///
	/// # Original
	///
	/// [`pointer::copy_to_nonoverlapping`](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_to_nonoverlapping)
	///
	/// # Safety
	///
	/// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
	///
	/// [`ptr::copy_nonoverlapping`](crate::ptr::copy_nonoverlapping)
	pub unsafe fn copy_to_nonoverlapping<O2, T2>(
		self,
		dest: BitPtr<Mut, O2, T2>,
		count: usize,
	) where
		O2: BitOrder,
		T2: BitStore,
	{
		for (from, to) in self.range(count).zip(dest.range(count)) {
			to.write(from.read());
		}
	}

	/// Computes the offset (in bits) that needs to be applied to the pointer in
	/// order to make it aligned to `align`.
	///
	/// “Alignment” here means that the pointer is selecting the start bit of a
	/// memory location whose address satisfies the requested alignment.
	///
	/// `align` is measured in **bytes**. If you wish to align your bit-pointer
	/// to a specific fraction (½, ¼, or ⅛ of one byte), please file an issue
	/// and this functionality will be added to [`BitIdx`].
	///
	/// # Original
	///
	/// [`pointer::align_offset`](https://doc.rust-lang.org/std/primitive.pointer.html#method.align_offset)
	///
	/// If the base-element address of the pointer is already aligned to
	/// `align`, then this will return the bit-offset required to select the
	/// first bit of the successor element.
	///
	/// If it is not possible to align the pointer, the implementation returns
	/// `usize::MAX`. It is permissible for the implementation to *always*
	/// return `usize::MAX`. Only your algorithm’s performance can depend on
	/// getting a usable offset here, not its correctness.
	///
	/// The offset is expressed in number of bits, and not `T` elements or
	/// bytes. The value returned can be used with the [`wrapping_add`] method.
	///
	/// # Safety
	///
	/// There are no guarantees whatsoëver that offsetting the pointer will not
	/// overflow or go beyond the allocation that the pointer points into. It is
	/// up to the caller to ensure that the returned offset is correct in all
	/// terms other than alignment.
	///
	/// # Panics
	///
	/// The function panics if `align` is not a power-of-two.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let data = [0u8; 3];
	/// let ptr = BitPtr::<_, Lsb0, _>::from_ref(&data[0], 4).unwrap();
	/// let count = ptr.align_offset(2);
	/// assert!(count > 0);
	/// ```
	///
	/// [`BitIdx`]: crate::index::BitIdx
	/// [`wrapping_add`]: Self::wrapping_add
	pub fn align_offset(self, align: usize) -> usize {
		let width = <T::Mem as BitMemory>::BITS as usize;
		match (
			self.addr.to_const().align_offset(align),
			self.head.value() as usize,
		) {
			(0, 0) => 0,
			(0, head) => width - head,
			(usize::MAX, _) => !0,
			(elts, head) => elts.wrapping_mul(width).wrapping_sub(head),
		}
	}
}

impl<O, T> BitPtr<Const, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Creates a new `BitPtr` from an element address and a bit index.
	///
	/// # Parameters
	///
	/// - `address`: A read-only pointer to a memory element. It may be null or
	///   misaligned.
	/// - `head`: An index of a bit within `*address`.
	///
	/// # Returns
	///
	/// If `address` is null or misaligned, this rejects the address and returns
	/// an error. Non-null, aligned, addresses are packed into a `BitPtr`.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::ptr::Const;
	///
	/// let data = 1u8;
	/// let ptr = BitPtr::<Const, Lsb0, _>::from_ptr(&data, 0).unwrap();
	/// ```
	///
	/// Errors caused by invalid pointers or indices:
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use bitvec::ptr::Const;
	///
	/// let data = 0u16;
	/// let addr = &data as *const u16 as *const u8;
	/// let addr = unsafe { addr.add(1) } as *const u16;
	///
	/// assert!(BitPtr::<Const, Lsb0, _>::from_ptr(addr, 0).is_err());
	/// assert!(BitPtr::<Const, Lsb0, _>::from_ptr(&data, 16).is_err());
	/// ```
	pub fn from_ptr(
		address: *const T,
		head: u8,
	) -> Result<Self, BitPtrError<T>> {
		let addr = address.try_into()?;
		let head = head.try_into()?;
		Ok(Self::new(addr, head))
	}

	/// Constructs a `BitPtr` from an element reference and a bit index.
	///
	/// References are always valid, so this will only fail if `head` is out of
	/// range.
	///
	/// # Parameters
	///
	/// - `elem`: A borrowed memory element.
	/// - `head`: An index of a bit within `*elem`.
	///
	/// # Returns
	///
	/// A read-only bit-pointer to the `head` bit in the `*elem` location.
	pub fn from_ref(elem: &T, head: u8) -> Result<Self, BitIdxError<T::Mem>> {
		head.try_into().map(|head| Self::new(elem.into(), head))
	}

	/// Gets the pointer to the base memory location containing the referent
	/// bit.
	pub fn pointer(&self) -> *const T {
		self.get_addr().to_const()
	}
}

impl<O, T> BitPtr<Mut, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Creates a new `BitPtr` from an element address and a bit index.
	///
	/// # Parameters
	///
	/// - `address`: A write-capable pointer to a memory element. It may be null
	///   or misaligned.
	/// - `head`: An index of a bit within `*address`.
	///
	/// # Returns
	///
	/// If `address` is null or misaligned, this rejects the address and returns
	/// an error. Non-null, aligned, addresses are packed into a `BitPtr`.
	///
	/// # Safety
	///
	/// You must not use any other pointer than that returned by this function
	/// to view or modify `*address`, unless the `T` type supports aliased
	/// mutation.
	pub fn from_ptr(address: *mut T, head: u8) -> Result<Self, BitPtrError<T>> {
		let addr = address.try_into()?;
		let head = head.try_into()?;
		Ok(Self::new(addr, head))
	}

	/// Constructs a `BitPtr` from an element reference and a bit index.
	///
	/// References are always valid, so this will only fail if `head` is out of
	/// range.
	///
	/// # Parameters
	///
	/// - `elem`: A borrowed memory element.
	/// - `head`: An index of a bit within `*elem`.
	///
	/// # Returns
	///
	/// A write-capable bit-pointer to the `head` bit in the `*elem` location.
	///
	/// # Safety
	///
	/// The exclusive borrow of `elem` is released after this function returns.
	/// However, you must not use any other pointer than that returned by this
	/// function to view or modify `*elem`, unless the `T` type supports aliased
	/// mutation.
	pub fn from_mut(
		elem: &mut T,
		head: u8,
	) -> Result<Self, BitIdxError<T::Mem>> {
		head.try_into().map(|head| Self::new(elem.into(), head))
	}

	/// Gets the pointer to the base memory location containing the referent
	/// bit.
	pub fn pointer(&self) -> *mut T {
		self.get_addr().to_mut()
	}

	//  `pointer` fundamental inherent API

	/// Produces a proxy mutable reference to the referent bit.
	///
	/// Because `BitPtr` is a non-null, well-aligned, pointer, this never
	/// returns `None`.
	///
	/// # Original
	///
	/// [`pointer::as_mut`](https://doc.rust-lang.org/std/primitive.pointer.html#method.as_mut)
	///
	/// # API Differences
	///
	/// This produces a proxy type rather than a true reference. The proxy
	/// implements `DerefMut<Target = bool>`, and can be converted to `&mut
	/// bool` with `&mut *`. Writes to the proxy are not reflected in the
	/// proxied location until the proxy is destroyed, either through `Drop` or
	/// with its [`set`] method.
	///
	/// The proxy must be bound as `mut` in order to write through the binding.
	///
	/// # Safety
	///
	/// Since `BitPtr` does not permit null or misaligned pointers, this method
	/// will always dereference the pointer and you must ensure the following
	/// conditions are met:
	///
	/// - the pointer must be dereferencable as defined in the standard library
	///   documentation
	/// - the pointer must point to an initialized instance of `T`
	/// - you must ensure that no other pointer will race to modify the referent
	///   location while this call is reading from memory to produce the proxy
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut data = 0u8;
	/// let ptr = BitPtr::<_, Lsb0, _>::from_mut(&mut data, 0).unwrap();
	/// let mut val = unsafe { ptr.as_mut() }.unwrap();
	/// assert!(!*val);
	/// *val = true;
	/// assert!(*val);
	/// ```
	///
	/// [`set`]: crate::ptr::BitRef::set
	pub unsafe fn as_mut<'a>(self) -> Option<BitRef<'a, Mut, O, T>> {
		Some(BitRef::from_bitptr(self))
	}

	/// Copies `count` bits from `src` to `self`. The source and destination may
	/// overlap.
	///
	/// Note: this has the *opposite* argument order of [`ptr::copy`].
	///
	/// # Original
	///
	/// [`pointer::copy_from`](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_from)
	///
	/// # Safety
	///
	/// See [`ptr::copy`] for safety concerns and examples.
	///
	/// [`ptr::copy`]: crate::ptr::copy
	pub unsafe fn copy_from<O2, T2>(
		self,
		src: BitPtr<Const, O2, T2>,
		count: usize,
	) where
		O2: BitOrder,
		T2: BitStore,
	{
		src.copy_to(self, count);
	}

	/// Copies `count` bits from `src` to `self`. The source and destination may
	/// *not* overlap.
	///
	/// NOTE: this has the *opposite* argument order of
	/// [`ptr::copy_nonoverlapping`].
	///
	/// # Original
	///
	/// [`pointer::copy_from_nonoverlapping`](https://doc.rust-lang.org/std/primitive.pointer.html#method.copy_from_nonoverlapping)
	///
	/// # Safety
	///
	/// See [`ptr::copy_nonoverlapping`] for safety concerns and examples.
	///
	/// [`ptr::copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping
	pub unsafe fn copy_from_nonoverlapping<O2, T2>(
		self,
		src: BitPtr<Const, O2, T2>,
		count: usize,
	) where
		O2: BitOrder,
		T2: BitStore,
	{
		src.copy_to_nonoverlapping(self, count);
	}

	/// Overwrites a memory location with the given bit.
	///
	/// See [`ptr::write`] for safety concerns and examples.
	///
	/// # Original
	///
	/// [`pointer::write`](https://doc.rust-lang.org/std/primitive.pointer.html#method.write)
	///
	/// [`ptr::write`]: crate::ptr::write
	pub unsafe fn write(self, value: bool) {
		(&*self.addr.to_access()).write_bit::<O>(self.head, value);
	}

	/// Performs a volatile write of a memory location with the given bit.
	///
	/// Because processors do not have single-bit write instructions, this must
	/// perform a volatile read of the location, perform the bit modification
	/// within the processor register, and then perform a volatile write back to
	/// memory. These three steps are guaranteed to be sequential, but are not
	/// guaranteed to be atomic.
	///
	/// Volatile operations are intended to act on I/O memory, and are
	/// guaranteed to not be elided or reördered by the compiler across other
	/// volatile operations.
	///
	/// # Original
	///
	/// [`pointer::write_volatile`](https://doc.rust-lang.org/std/primitive.pointer.html#method.write_volatile)
	///
	/// # Safety
	///
	/// See [`ptr::write_volatile`] for safety concerns and examples.
	///
	/// [`ptr::write_volatile`]: crate::ptr::write_volatile
	pub unsafe fn write_volatile(self, val: bool) {
		let select = O::select(self.head).value();
		let mut tmp = self.addr.to_mem().read_volatile();
		if val {
			tmp |= &select;
		}
		else {
			tmp &= &!select;
		}
		self.addr.to_mem_mut().write_volatile(tmp);
	}

	/// Replaces the bit at `*self` with `src`, returning the old bit.
	///
	/// # Original
	///
	/// [`pointer::replace`](https://doc.rust-lang.org/std/primitive.pointer.html#method.replace)
	///
	/// # Safety
	///
	/// See [`ptr::replace`] for safety concerns and examples.
	///
	/// [`ptr::replace`]: crate::ptr::replace
	pub unsafe fn replace(self, src: bool) -> bool {
		let out = self.read();
		self.write(src);
		out
	}

	/// Swaps the bits at two mutable locations. They may overlap.
	///
	/// # Original
	///
	/// [`pointer::swap`](https://doc.rust-lang.org/std/primitive.pointer.html#method.swap)
	///
	/// # Safety
	///
	/// See [`ptr::swap`] for safety concerns and examples.
	///
	/// [`ptr::swap`]: crate::ptr::swap
	pub unsafe fn swap<O2, T2>(self, with: BitPtr<Mut, O2, T2>)
	where
		O2: BitOrder,
		T2: BitStore,
	{
		let (a, b) = (self.read(), with.read());
		self.write(b);
		with.write(a);
	}
}

impl<M, O, T> Clone for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		Self {
			addr: self.get_addr(),
			..*self
		}
	}
}

impl<M, O, T> Eq for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}

impl<M, O, T> Ord for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.partial_cmp(other).expect(
			"BitPtr has a total ordering when type parameters are identical",
		)
	}
}

impl<M1, M2, O, T1, T2> PartialEq<BitPtr<M2, O, T2>> for BitPtr<M1, O, T1>
where
	M1: Mutability,
	M2: Mutability,
	O: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn eq(&self, other: &BitPtr<M2, O, T2>) -> bool {
		if TypeId::of::<T1::Mem>() != TypeId::of::<T2::Mem>() {
			return false;
		}
		self.get_addr().value() == other.get_addr().value()
			&& self.head.value() == other.head.value()
	}
}

impl<M1, M2, O, T1, T2> PartialOrd<BitPtr<M2, O, T2>> for BitPtr<M1, O, T1>
where
	M1: Mutability,
	M2: Mutability,
	O: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn partial_cmp(&self, other: &BitPtr<M2, O, T2>) -> Option<cmp::Ordering> {
		if TypeId::of::<T1::Mem>() != TypeId::of::<T2::Mem>() {
			return None;
		}
		match (self.get_addr().value()).cmp(&other.get_addr().value()) {
			cmp::Ordering::Equal => {
				self.head.value().partial_cmp(&other.head.value())
			},
			ord => Some(ord),
		}
	}
}

impl<O, T> From<&T> for BitPtr<Const, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(elem: &T) -> Self {
		Self::new(elem.into(), BitIdx::ZERO)
	}
}

impl<O, T> From<&mut T> for BitPtr<Mut, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(elem: &mut T) -> Self {
		Self::new(elem.into(), BitIdx::ZERO)
	}
}

impl<O, T> TryFrom<*const T> for BitPtr<Const, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = BitPtrError<T>;

	fn try_from(elem: *const T) -> Result<Self, Self::Error> {
		elem.try_into().map(Self::from_address).map_err(Into::into)
	}
}

impl<O, T> TryFrom<*mut T> for BitPtr<Mut, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = BitPtrError<T>;

	fn try_from(elem: *mut T) -> Result<Self, Self::Error> {
		elem.try_into().map(Self::from_address).map_err(Into::into)
	}
}

impl<M, O, T> Debug for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(
			fmt,
			"*{} Bit<{}, {}>",
			match TypeId::of::<M>() {
				t if t == TypeId::of::<Const>() => "const",
				t if t == TypeId::of::<Mut>() => "mut",
				_ => unreachable!(),
			},
			type_name::<O>(),
			type_name::<T>()
		)?;
		Pointer::fmt(self, fmt)
	}
}

impl<M, O, T> Pointer for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("")
			.field(&self.get_addr().fmt_pointer())
			.field(&self.head.fmt_binary())
			.finish()
	}
}

impl<M, O, T> Hash for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn hash<H>(&self, state: &mut H)
	where H: Hasher {
		self.get_addr().hash(state);
		self.head.hash(state);
	}
}

impl<M, O, T> Copy for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}

impl<M, O, T> Deref for BitPtr<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	type Target = bool;

	fn deref(&self) -> &Self::Target {
		if unsafe { self.read() } {
			&true
		}
		else {
			&false
		}
	}
}

/// Errors produced by invalid bit-pointer components.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BitPtrError<T>
where T: BitStore
{
	/// The element address was somehow invalid.
	InvalidAddress(AddressError<T>),
	/// The bit index was somehow invalid.
	InvalidIndex(BitIdxError<T::Mem>),
}

impl<T> From<AddressError<T>> for BitPtrError<T>
where T: BitStore
{
	fn from(err: AddressError<T>) -> Self {
		Self::InvalidAddress(err)
	}
}

impl<T> From<BitIdxError<T::Mem>> for BitPtrError<T>
where T: BitStore
{
	fn from(err: BitIdxError<T::Mem>) -> Self {
		Self::InvalidIndex(err)
	}
}

impl<T> From<Infallible> for BitPtrError<T>
where T: BitStore
{
	fn from(_: Infallible) -> Self {
		unreachable!("Infallible errors can never be produced");
	}
}

impl<T> Display for BitPtrError<T>
where T: BitStore
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		match self {
			Self::InvalidAddress(addr) => Display::fmt(addr, fmt),
			Self::InvalidIndex(index) => Display::fmt(index, fmt),
		}
	}
}

unsafe impl<T> Send for BitPtrError<T> where T: BitStore
{
}

unsafe impl<T> Sync for BitPtrError<T> where T: BitStore
{
}

#[cfg(feature = "std")]
impl<T> std::error::Error for BitPtrError<T> where T: BitStore
{
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		mutability::Const,
		prelude::Lsb0,
	};

	#[test]
	fn ctor() {
		let data = 0u16;
		let head = 5;

		let bitptr = BitPtr::<Const, Lsb0, _>::try_new(&data, 5).unwrap();
		let (addr, indx) = bitptr.raw_parts();
		assert_eq!(addr.to_const(), &data as *const _);
		assert_eq!(indx.value(), head);
	}

	#[test]
	fn assert_size() {
		assert!(
			core::mem::size_of::<BitPtr<Const, Lsb0, u8>>()
				<= core::mem::size_of::<usize>() + core::mem::size_of::<u8>(),
		);
	}
}
