/*! Bit management

The `BitStore` trait defines constants and associated functions suitable for
managing the bit patterns of a fundamental, and is the constraint for the
storage type of the data structures of the rest of the crate.

The other types in this module provide stronger rules about how indices map to
concrete bits in fundamental elements. They are implementation details, and are
not exported in the prelude.
!*/

use crate::{
	access::BitAccess,
	mem::BitMemory,
};

use core::fmt::{
	Binary,
	Debug,
};

#[cfg(feature = "atomic")]
use core::sync::atomic;

#[cfg(not(feature = "atomic"))]
use core::cell::Cell;

/** Generalizes over the fundamental types for use in `bitvec` data structures.

This trait must only be implemented on unsigned integer primitives with full
alignment. It cannot be implemented on `u128` on any architecture, or on `u64`
on 32-bit systems.

The `Sealed` supertrait ensures that this can only be implemented locally, and
will never be implemented by downstream crates on new types.
**/
pub trait BitStore:
	//  Forbid external implementation
	seal::Sealed
	+ Binary
	+ Copy
	+ Debug
	//  Allow direct access to a concrete implementor type.
	+ Sized
{
	/// The register type this store describes.
	type Mem: BitMemory;

	/// Shared/mutable access wrapper.
	///
	/// Within `&BitSlice` and `&mut BitSlice` contexts, the `Access` type
	/// governs all access to underlying memory that may be contended by
	/// multiple slices. When a codepath knows that it has full, uncontended
	/// ownership of a memory element of `Self`, and no other codepath may
	/// observe or modify it, then that codepath may skip the `Access` type and
	/// use plain accessors.
	type Access: BitAccess<Self::Mem>;

}

/// Batch implementation of `BitStore` for the appropriate fundamental integers.
macro_rules! bitstore {
	($($t:ty => $bits:literal , $atom:ty ;)*) => { $(
		impl BitStore for $t {
			type Mem = Self;

			#[cfg(feature = "atomic")]
			type Access = $atom;

			#[cfg(not(feature = "atomic"))]
			type Access = Cell<Self>;
		}
	)* };
}

bitstore! {
	u8 => 1, atomic::AtomicU8;
	u16 => 2, atomic::AtomicU16;
	u32 => 4, atomic::AtomicU32;
}

#[cfg(target_pointer_width = "32")]
bitstore! {
	usize => 4, atomic::AtomicUsize;
}

#[cfg(target_pointer_width = "64")]
bitstore! {
	u64 => 8, atomic::AtomicU64;
	usize => 8, atomic::AtomicUsize;
}

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_fail!(concat!(
	"This architecture is currently not supported. File an issue at ",
	env!(CARGO_PKG_REPOSITORY)
));

mod seal {
	/// Marker trait to seal `BitStore` against downstream implementation.
	///
	/// This trait is public in the module, so that other modules in the crate
	/// can use it, but so long as it is not exported by the crate root and this
	/// module is private, this trait effectively forbids downstream
	/// implementation of the `BitStore` trait.
	#[doc(hidden)]
	pub trait Sealed {}

	macro_rules! seal {
		($($t:ty),*) => { $(
			impl Sealed for $t {}
		)* };
	}

	seal!(u8, u16, u32, usize);

	#[cfg(target_pointer_width = "64")]
	seal!(u64);
}
