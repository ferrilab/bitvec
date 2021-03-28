/*! Address management.

This module only provides utilities for requiring that `T: BitStore` addresses
are well aligned to their type. It also exports the type-level mutability
tracking behavior now provided by [`wyz::comu`].
!*/

use core::{
	any,
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
		Pointer,
	},
	mem,
};

use tap::{
	Pipe,
	TryConv,
};
pub use wyz::comu::{
	Address,
	Const,
	Mut,
	Mutability,
	NullPtrError,
};
use wyz::FmtForward;

/// Ensures that an address is well-aligned to its referent type.
#[inline]
pub fn check_alignment<M, T>(
	addr: Address<M, T>,
) -> Result<Address<M, T>, MisalignError<T>>
where M: Mutability {
	let ptr = addr.to_const();
	let mask = mem::align_of::<T>() - 1;
	if ptr as usize & mask != 0 {
		Err(MisalignError { ptr })
	}
	else {
		Ok(addr)
	}
}

/// Extension methods for raw pointers.
pub(crate) trait AddressExt<T> {
	/// Tracks the original mutation capability of the source pointer.
	type Permission: Mutability;

	/// Forcibly wraps the raw pointer as an `Address`, without handling errors.
	///
	/// In debug builds, this will panic on null or misaligned pointers. In
	/// release builds, it is permitted to remove the error-handling codepaths
	/// and assume those invariants are upheld by the caller.
	///
	/// # Safety
	///
	/// The caller must ensure that this is only called on non-null,
	/// well-aligned, pointers. Pointers derived from Rust references or calls
	/// to the Rust allocator API will always satisfy this.
	unsafe fn force_wrap(self) -> Address<Self::Permission, T>;
}

impl<T> AddressExt<T> for *const T {
	type Permission = Const;

	unsafe fn force_wrap(self) -> Address<Const, T> {
		self.try_conv::<Address<_, _>>()
			//  Don’t call this with null pointers.
			.unwrap_or_else(|err| unreachable!("{}", err))
			.pipe(check_alignment)
			//  Don’t call this with misaligned pointers either.
			.unwrap_or_else(|err| unreachable!("{}", err))
	}
}

impl<T> AddressExt<T> for *mut T {
	type Permission = Mut;

	unsafe fn force_wrap(self) -> Address<Mut, T> {
		self.try_conv::<Address<_, _>>()
			.unwrap_or_else(|err| unreachable!("{}", err))
			.pipe(check_alignment)
			.unwrap_or_else(|err| unreachable!("{}", err))
	}
}

/// Error produced when an address is insufficiently aligned to its type.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MisalignError<T> {
	/// The misaligned pointer.
	pub ptr: *const T,
}

impl<T> MisalignError<T> {
	const ALIGN: usize = mem::align_of::<T>();
	const CTTZ: usize = Self::ALIGN.trailing_zeros() as usize;
}

impl<T> Debug for MisalignError<T> {
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("Misalign")
			.field(&self.ptr.fmt_pointer())
			.field(&Self::ALIGN)
			.finish()
	}
}

impl<T> Display for MisalignError<T> {
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(
			fmt,
			"Type {} requires {}-byte alignment: address ",
			any::type_name::<T>(),
			Self::ALIGN,
		)?;
		Pointer::fmt(&self.ptr, fmt)?;
		write!(fmt, " must clear its least {} bits", Self::CTTZ)
	}
}

unsafe impl<T> Send for MisalignError<T> {
}

unsafe impl<T> Sync for MisalignError<T> {
}

#[cfg(feature = "std")]
impl<T> std::error::Error for MisalignError<T> {
}

#[test]
#[cfg(feature = "alloc")]
fn render() {
	#[cfg(not(feature = "std"))]
	use alloc::format;
	use core::ptr::NonNull;

	assert_eq!(
		format!(
			"{}",
			check_alignment(Address::<Const, u16>::new(
				NonNull::new(0x13579 as *mut _).unwrap()
			))
			.unwrap_err()
		),
		"Type u16 requires 2-byte alignment: address 0x13579 must clear its \
		 least 1 bits"
	);
	assert_eq!(
		format!(
			"{}",
			check_alignment(Address::<Const, u32>::new(
				NonNull::new(0x13579 as *mut _).unwrap()
			))
			.unwrap_err()
		),
		"Type u32 requires 4-byte alignment: address 0x13579 must clear its \
		 least 2 bits"
	);
}
