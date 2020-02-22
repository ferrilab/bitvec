/*! Memory management.

The `BitStore` trait defines the types that can be used in `bitvec` data
structures, and describes how those data structures are allowed to access the
memory they govern.
!*/

use crate::{
	access::BitAccess,
	mem::BitMemory,
};

use core::{
	cell::Cell,
	sync::atomic,
};

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
	type Alias: BitAccess<Self::Mem> + BitStore;
	/// The destination type when marking a region as known-unaliased.
	type NoAlias: BitAccess<Self::Mem> + BitStore;
}

/// Batch implementation of `BitStore` for appropriate types.
macro_rules! bitstore {
	($($t:ty => $a:ty),* $(,)?) => { $(
		impl seal::Sealed for $t {}

		impl BitStore for $t {
			/// Fundamental integers must use the target’s aliased type for safe
			/// access to memory.
			type Access = Self::Alias;

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

			type NoAlias = Cell<Self>;
		}

		#[cfg(feature = "atomic")]
		impl seal::Sealed for $a {}

		#[cfg(feature = "atomic")]
		impl BitStore for $a {
			/// Atomic stores always use atomic accesses.
			type Access = Self;

			type Alias = Self;

			type Mem = $t;

			type NoAlias=Cell<$t>;
		}

		impl seal::Sealed for Cell<$t> {}

		impl BitStore for Cell<$t> {
			/// `Cell`s always use ordinary, unsynchronized, accesses, as the
			/// type system forbids them from creating memory collisions.
			type Access = Self;

			/// In atomic builds, splitting a `BitSlice` of this type to produce
			/// aliases requires reverting to atomic accesses, as `BitSlice`s
			/// are safe to move across threads.
			#[cfg(feature = "atomic")]
			type Alias = $a;

			///
			#[cfg(not(feature = "atomic"))]
			type Alias = Self;

			type Mem = $t;

			type NoAlias = Self;
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
