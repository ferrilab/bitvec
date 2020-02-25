/*! Memory management.

The `BitStore` trait defines the types that can be used in `bitvec` data
structures, and describes how those data structures are allowed to access the
memory they govern.
!*/

use crate::{
	access::BitAccess,
	mem::BitMemory,
};

use core::cell::Cell;

#[cfg(feature = "atomic")]
use core::sync::atomic;

/** Generalize over types which may be used to access memory holding bits.

This trait is implemented on the fundamental integers, their `Cell<>` wrappers,
and (if present) their `Atomic` variants. Users provide this type as a parameter
to their data structures in order to inform the structure of how it may access
memory.

Specifically, this has the advantage that a `BitSlice<_, Cell<_>>` knows that it
has a view of memory that will not undergo concurrent modification. As such, it
can skip using atomic accesses, and just use ordinary load/store instructions,
without fear of causing observable race conditions.

The associated types `Mem` and `Alias` allow implementors to know the register
width of the memory they describe (`Mem`) and to change the aliasing status of
a slice.

A universal property of `BitSlice` regions is that for any handle, it may be
described as a triad of:

- zero or one partially-used, aliased, elements at the head
- zero or more wholly-used, unaliased, elements in the body
- zero or one partially-used, aliased, elements at the tail

As such, a `&BitSlice` reference with any aliasing type can be split into its
`Self::Alias` variant for the edges, and `Cell<Self::Mem>` for the interior,
without violating memory safety.
**/
pub trait BitStore: seal::Sealed + Sized {
	/// The fundamental integer type of the governed memory.
	type Mem: BitMemory + Into<Self>;
	/// The type used for performing memory accesses.
	type Access: BitAccess<Self::Mem> + BitStore;
	/// The destination type when marking a region as known-aliased.
	type Alias: BitStore + BitAccess<Self::Mem>;
	/// The destination type when marking a region as known-unaliased.
	type NoAlias: BitStore;

	/// Mark whether a type is threadsafe when viewed as bits.
	///
	/// This is necessary because `Cell<T: Send>` is `Send`, but `Cell` is *not*
	/// synchronized and thus cannot be used for aliasing, parallel, bit
	/// manipulation.
	#[doc(hidden)]
	type Threadsafe;

	/* Note: The `NoAlias` type had its `BitAccess` bound removed so that the
	integers and atoms could form a cycle, rather than trending into `Cell`.
	This had the unpleasant side effect of making `T::NoAlias` use sites much
	less pleasant to use in generic contexts, due to the inability of the Rust
	type system to unwind associated types. This removal necessitated the
	addition of the `.retype()` method in `BitMemory`, and the `.get_elem()` and
	`.set_elem()` methods below.

	Attempting to do this same `BitAccess` bound removal on `Alias` proved to
	be *extremely* awful, as the change required adding these new methods
	throughout the crate. This is needless spaghetti code, required only by the
	inadequacy of the type system to smoothly handle the graph of associated
	types used in this crate. It is, to be fair, my fault for attempting to
	cause cycles, when the type system expects a DAG.

	Long story short: don’t try to remove the bound in the future. It needs to
	stay off of `NoAlias`, because making a `BitAccess` wrapper type for the
	integers is profoundly unpleasant. Don’t do that either.

	Hopefully, the aliasing detection work is the last major overhaul of the
	memory access system, and these modules will be left alone unless
	demonstrated to be unsound.
	*/

	/// Gets the memory element behind this reference, mediated through
	/// `Self::Access`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The current value of the referent element.
	fn get_elem(&self) -> Self::Mem {
		unsafe { &*(self as *const Self as *const Self::Access) }.load()
	}

	/// Sets the memory element behind this reference, mediated through
	/// `Self::Access`.
	///
	/// # Parameters
	///
	/// - `&mut self`: Even when aliased, you must have exclusive control of the
	///   referent element to set it to a new value.
	/// - `value`: The new value to write into the referent element.
	fn set_elem(&mut self, value: Self::Mem) {
		unsafe { &*(self as *mut Self as *mut Self::Access) }.store(value);
	}
}

/// Batch implementation of `BitStore` for appropriate types.
macro_rules! bitstore {
	($($t:ty => $a:ty),* $(,)?) => { $(
		impl seal::Sealed for $t {}

		impl BitStore for $t {
			/// The unsigned integers are only the `BitStore` parameter for
			/// unaliased slices.
			type Access = Cell<Self>;

			/// Aliases are required to use atomic access, as `BitSlice`s of
			/// this type are safe to move across threads.
			#[cfg(feature = "atomic")]
			type Alias = $a;

			/// Aliases are permitted to use `Cell` wrappers and ordinary
			/// access, as `BitSlice`s of this type are forbidden from crossing
			/// threads.
			#[cfg(not(feature = "atomic"))]
			type Alias = Cell<Self>;

			type Mem = Self;

			type NoAlias = Self;

			#[doc(hidden)]
			type Threadsafe = Self;
		}

		#[cfg(feature = "atomic")]
		impl seal::Sealed for $a {}

		#[cfg(feature = "atomic")]
		impl BitStore for $a {
			/// Atomic stores always use atomic accesses.
			type Access = Self;

			type Alias = Self;

			type Mem = $t;

			type NoAlias = $t;

			#[doc(hidden)]
			type Threadsafe = Self;
		}

		impl seal::Sealed for Cell<$t> {}

		impl BitStore for Cell<$t> {
			/// `Cell`s always use ordinary, unsynchronized, accesses, as the
			/// type system forbids them from creating memory collisions.
			type Access = Self;

			type Alias = Self;

			type Mem = $t;

			type NoAlias = Self;

			/// Raw pointers are never threadsafe, so this prevents
			/// `BitSlice<_, Cell<_>>` from crossing threads.
			#[doc(hidden)]
			type Threadsafe = *const Self;
		}
	)* };
}

bitstore!(
	u8 => atomic::AtomicU8,
	u16 => atomic::AtomicU16,
	u32 => atomic::AtomicU32,
	usize => atomic::AtomicUsize,
);

#[cfg(target_pointer_width = "64")]
bitstore!(u64 => atomic::AtomicU64);

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_fail!(concat!(
	"This architecture is currently not supported. File an issue at ",
	env!("CARGO_PKG_REPOSITORY")
));

/// Enclose the `Sealed` trait against client use.
mod seal {
	/// Marker trait to seal `BitStore` against downstream implementation.
	///
	/// This trait is public in the module, so that other modules in the crate
	/// can use it, but so long as it is not exported by the crate root and this
	/// module is private, this trait effectively forbids downstream
	/// implementation of the `BitStore` trait.
	#[doc(hidden)]
	pub trait Sealed {}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;
	use core::cell::Cell;
	use static_assertions::*;

	#[test]
	fn traits() {
		//  The integers are threadsafe, as they are known to be unaliased.
		assert_impl_all!(BitSlice<Local, u8>: Send, Sync);
		assert_impl_all!(BitSlice<Local, u16>: Send, Sync);
		assert_impl_all!(BitSlice<Local, u32>: Send, Sync);
		assert_impl_all!(BitSlice<Local, usize>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_impl_all!(BitSlice<Local, u64>: Send, Sync);

		//  The integer alias is threadsafe when atomics are enabled.
		#[cfg(feature = "atomic")]
		{
			assert_impl_all!(BitSlice<Local, <u8 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<Local, <u16 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<Local, <u32 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<Local, <usize as BitStore>::Alias>: Send, Sync);

			#[cfg(target_pointer_width = "64")]
			assert_impl_all!(BitSlice<Local, <u64 as BitStore>::Alias>: Send, Sync);
		}

		//  The integer alias is thread unsafe when atomics are disabled.
		#[cfg(not(feature = "atomic"))]
		{
			assert_not_impl_any!(BitSlice<Local, <u8 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<Local, <u16 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<Local, <u32 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<Local, <usize as BitStore>::Alias>: Send, Sync);

			#[cfg(target_pointer_width = "64")]
			assert_not_impl_any!(BitSlice<Local, <u64 as BitStore>::Alias>: Send, Sync);
		}

		//  `Cell`s are never threadsafe.
		assert_not_impl_any!(BitSlice<Local, Cell<u8>>: Send, Sync);
		assert_not_impl_any!(BitSlice<Local, Cell<u16>>: Send, Sync);
		assert_not_impl_any!(BitSlice<Local, Cell<u32>>: Send, Sync);
		assert_not_impl_any!(BitSlice<Local, Cell<usize>>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_not_impl_any!(BitSlice<Local, Cell<u64>>: Send, Sync);
	}
}
