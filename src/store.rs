/*! Memory modeling.

This module provides the [`BitStore`] trait, which contains all of the logic
required to perform memory accesses from a data structure handle.

[`BitStore`]: self::BitStore
!*/

use crate::{
	access::*,
	index::{
		BitIdx,
		BitMask,
	},
	mem::{
		self,
		BitRegister,
	},
	order::BitOrder,
};

use core::{
	cell::Cell,
	fmt::Debug,
};

use tap::pipe::Pipe;

/** Common interface for memory regions.

This trait is implemented on the fundamental integers no wider than the target
processor word size, as well as on [write-incapable wrappers][`BitSafe`] over
[`Cell`]s and [atoms] of those integers. This type is added to the [`bitvec`]
data structures when they are created, and informs those structures as they use
and perhaps alias the underlying memory.

Currently, [`bitvec`] is only tested on 32- and 64- bit architectures. This
means that `u8`, `u16`, `u32`, and `usize` unconditionally implement `BitStore`,
but `u64` will only do so on 64-bit targets. This is a necessary restriction of
`bitvec` internals. Please comment on [Issue #76] if this affects you.

Specifically, this trait allows any [`BitSlice`] to use alias-aware rules for
thread-safety or memory access when they detect that multiple `BitSlice` handles
may read or write to the same memory register address.

The [`Mem`] associated type is always a bare integer, and indicates the register
type that the structure uses. The [`Access`] associated type manages the
instructions used to operate the memory bus when reading or writing from the
underlying region, and the [`Alias`] associated type prevents writing to memory
when a slice does not have write permission to an element, but some other slice
might.

# Generic Programming

You are not expected to do significant programming that is generic over the
`BitStore` type parameter. When using a concrete type, the compiler will gladly
reduce the abstract type associatons into their instantiated selections,
allowing monomorphized code to be clearly and conveniently written.

Generic programming with associated types, especially with the relationship
graph used in this trait, rapidly becomes unwieldy. [`bitvec`] uses internal
type-manipulation functions for convenience, in order to handle the growth of
associated type spans in its work.

[Issue #76]: https://github.com/myrrlyn/bitvec/issues/76
[atoms]: core::sync::atomic
[`Access`]: Self::Access
[`Alias`]: Self::Alias
[`BitSafe`]: crate::access::BitSafe
[`BitSlice`]: crate::slice::BitSlice
[`Cell`]: core::cell::Cell
[`Mem`]: Self::Mem
[`bitvec`]: crate
**/
pub trait BitStore: 'static + seal::Sealed + Debug {
	/// The register type that the implementor uses.
	type Mem: BitRegister + BitStore;

	/// The type used to perform memory access to a `Self::Mem` register.
	type Access: BitAccess<Item = Self::Mem>;

	/// A sibling `BitStore` implementor used when a region becomes aliased.
	type Alias: BitSafe<Mem = Self::Mem> + BitStore<Mem = Self::Mem>;

	/// Copies a memory element into the caller’s local context.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A copy of the value at `*self`.
	fn load_value(&self) -> Self::Mem;

	/// Fetches the value of one bit in a memory element.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit in `*self` to read.
	///
	/// # Returns
	///
	/// The value of the bit in `*self` corresponding to `index`.
	fn get_bit<O>(&self, index: BitIdx<Self::Mem>) -> bool
	where O: BitOrder {
		self.load_value()
			.pipe(BitMask::new)
			.test(index.select::<O>())
	}

	/// Require that all implementors are aligned to their width.
	#[doc(hidden)]
	const __ALIGNED_TO_SIZE: [(); 0];

	/// Require that the `::Alias` associated type has the same width and
	/// alignment as `Self`.
	#[doc(hidden)]
	const __ALIAS_WIDTH: [(); 0];
}

/// Batch implementation of `BitStore` for appropriate types.
macro_rules! store {
	($($t:ident => $w:ident),+ $(,)?) => { $(
		impl BitStore for $t {
			type Mem = $t;
			/// The unsigned integers will only be `BitStore` type parameters
			/// for handles to unaliased memory, following the normal Rust
			/// reference rules.
			type Access = Cell<$t>;

			type Alias = $w;

			fn load_value(&self) -> $t {
				*self
			}

			#[doc(hidden)]
			const __ALIGNED_TO_SIZE: [(); 0]
				= [(); mem::aligned_to_size::<Self>()];

			#[doc(hidden)]
			const __ALIAS_WIDTH: [(); 0]
				= [(); mem::cmp_layout::<Self::Mem, Self::Alias>()];
		}

		impl BitStore for $w {
			type Mem = $t;
			type Access = <$w as BitSafe>::Rad;
			type Alias = $w;

			fn load_value(&self) -> $t {
				self.load()
			}

			#[doc(hidden)]
			const __ALIGNED_TO_SIZE: [(); 0]
				= [(); mem::aligned_to_size::<Self>()];

			#[doc(hidden)]
			const __ALIAS_WIDTH: [(); 0]
				= [(); mem::cmp_layout::<Self::Mem, Self>()];
		}

		impl seal::Sealed for $t {}
		impl seal::Sealed for $w {}
	)+ };
}

store! {
	u8 => BitSafeU8,
	u16 => BitSafeU16,
	u32 => BitSafeU32,
}

#[cfg(target_pointer_width = "64")]
store!(u64 => BitSafeU64);

store!(usize => BitSafeUsize);

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
	use static_assertions::*;

	/// Unaliased `BitSlice`s are universally threadsafe, because they satisfy
	/// Rust’s unysnchronized mutation rules.
	#[test]
	fn unaliased_send_sync() {
		assert_impl_all!(BitSlice<LocalBits, u8>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, u16>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, u32>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, usize>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_impl_all!(BitSlice<LocalBits, u64>: Send, Sync);
	}

	/// In non-atomic builds, aliased `BitSlice`s become universally
	/// thread-unsafe. An `&mut BitSlice` is an `&Cell`, and `&Cell` cannot be
	/// sent across threads.
	///
	/// This test cannot be meaningfully expressed in atomic builds, because the
	/// atomiticy of a `BitSafeUN` type is target-specific, and expressed in
	/// `radium` rather than in `bitvec`.
	#[test]
	#[cfg(not(feature = "atomic"))]
	fn aliased_nonatomic_unsend_unsync() {
		use crate::access::*;

		assert_not_impl_any!(BitSlice<LocalBits, BitSafeU8>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeU16>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeU32>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeUsize>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeU64>: Send, Sync);
	}
}
