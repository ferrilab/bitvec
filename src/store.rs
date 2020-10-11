/*! Memory modeling.

This module provides a [`BitStore`] trait, which describes the register width
and alias condition of memory underlying a [`BitSlice`] region. This trait is
used to handle all access to memory and transformation of alias status for the
regions.

[`BitSlice`]: crate::slice::BitSlice
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

#[cfg(feature = "atomic")]
use core::sync::atomic::{
	AtomicU16,
	AtomicU32,
	AtomicU8,
	AtomicUsize,
};

#[cfg(all(feature = "atomic", target_pointer_width = "64"))]
use core::sync::atomic::AtomicU64;

/** Common interface for memory regions.

This trait is implemented on the fundamental integers no wider than the target
processor word size, their [`Cell`] wrappers, and (if present) their [`Atomic`]
variants. Users provide this type as a parameter to their data structures in
order to inform the structure of how it may access the memory it describes.

Currently, [`bitvec`] is only tested on 32- and 64- bit architectures. This
means that `u8`, `u16`, `u32`, and `usize` unconditionally implement `BitStore`,
but `u64` will only do so on 64-bit targets, and will be unavailable on 32-bit
targets. This is a necessary restriction of `bitvec` internals. Please comment
on [Issue #76](https://github.com/myrrlyn/bitvec/issues/76) if this affects you.

Specifically, this has the advantage that a [`BitSlice<_, Cell<_>>`] knows that
it has a view of memory that will not undergo concurrent modification. As such,
it can forego atomic accesses, and just use ordinary load/store instructions
without fear of causing observable race conditions.

The associated types [`Mem`] and [`Alias`] allow implementors to know the
register width of the memory they describe (`Mem`) and to know the aliasing
status of the region.

# Generic Programming

Generic programming with associated types is *hard*, especially when using them,
as in this trait, to implement a closed graph of relationships between types.

For example, this trait is implemented such that for any given type `T`,
`T::Alias::Mem` == `T::Mem` == `T::NoAlias::Mem`, `T::Alias::Alias == T::Alias`,
and `T::NoAlias::NoAlias == T::NoAlias`. Unfortunately, the Rust type system
does not allow these relationships to be described, so generic programming that
performs type transitions will *rapidly* become uncomfortable to use.

Internally, [`bitvec`] makes use of type-manipulation functions that are known
to be correct with respect to the implementations of `BitStore in order to ease
implementation of library methods.

You are not expected to do significant programming that is generic over the
`BitStore memory parameter. When using a concrete type, the compiler will gladly
reduce the abstract type associations into their instantiated selections,
allowing monomorphized code to be *much* more convenient than generic.

If you have a use case that involves generic programming over this trait, and
you are encountering difficulties dealing with the type associations, please
file an issue asking for support in this area.

# Supertraits

This trait has requirements that better express its behavior:

- `'static`: Implementors never contain references.
- `Sealed` prevents it from being implemented by downstream libraries (`Sealed`
  is a public trait in a private module, that only this crate can name).
- [`Debug`] informs the compiler that other structures using this trait bound
can correctly derive `Debug`.

[`Alias`]: Self::Alias
[`Atomic`]: core::sync::atomic
[`BitSlice<_, Cell<_>>`]: crate::slice::BitSlice
[`Cell`]: core::cell::Cell
[`Debug`]: core::fmt::Debug
[`Mem`]: Self::Mem
[`Sized`]: core::marker::Sized
[`bitvec`]: crate
**/
pub trait BitStore: 'static + seal::Sealed + Debug {
	/// The register type that the implementor describes.
	type Mem: BitRegister + BitStore;

	/// The type used to perform memory access to a `Self::Mem` region.
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
		unsafe { BitMask::new(self.load_value()) }.test(index.select::<O>())
	}

	/// Fetches any number of bits from a memory element.
	///
	/// The mask provided to this method must be constructed from indices that
	/// are valid in the caller’s context. As the mask is already computed by
	/// the caller, this does not take an ordering type parameter.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: A mask of any number of bits. This is a selection mask of bits
	///   to read.
	///
	/// # Returns
	///
	/// A copy of the memory element at `*self`, with all bits not selected (set
	/// to `0`) in `mask` erased and all bits selected (set to `1`) in `mask`
	/// preserved.
	#[inline]
	fn get_bits(&self, mask: BitMask<Self::Mem>) -> Self::Mem {
		self.load_value() & mask.value()
	}

	/// Marker for the thread safety of the implementor.
	///
	/// This is necessary because `Cell<T: Send>` is `Send`, but `Cell` does not
	/// use synchronization instructions and thus cannot be used for aliased
	/// parallelized memory manipulation.
	#[doc(hidden)]
	type Threadsafe;

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
	($($t:ident => $cw:ident => $aw:ident => $a:ident),+ $(,)?) => { $(
		impl BitStore for $t {
			type Mem = $t;
			/// The unsigned integers will only be `BitStore` type parameters
			/// for handles to unaliased memory, following the normal Rust
			/// reference rules.
			type Access = Cell<$t>;

			/// In atomic builds, use the safed [atomic] wrapper.
			///
			/// [atomic]: core::sync::atomic
			#[cfg(feature = "atomic")]
			type Alias = $aw;

			/// In non-atomic builds, use the safed [`Cell`] wrapper.
			///
			/// [`Cell`]: core::cell::Cell
			#[cfg(not(feature = "atomic"))]
			type Alias = $cw;

			#[inline(always)]
			fn load_value(&self) -> $t {
				*self
			}

			#[doc(hidden)]
			type Threadsafe = Self;

			#[doc(hidden)]
			const __ALIGNED_TO_SIZE: [(); 0] = [(); mem::misaligned_to_size::<Self>()];

			#[doc(hidden)]
			const __ALIAS_WIDTH: [(); 0] = [(); mem::cmp_layout::<Self::Mem, Self::Alias>()];
		}

		impl BitStore for $cw {
			type Mem = $t;
			type Access = Cell<$t>;
			type Alias = $cw;

			#[inline(always)]
			fn load_value(&self) -> $t {
				self.load()
			}

			/// Raw pointers are never threadsafe, so this prevents handles using
			/// `Cell` wrappers from crossing thread boundaries.
			#[doc(hidden)]
			type Threadsafe = *const Self;

			// If these are true for `R: BitRegister`, then they are true for `Cell<R>`.
			#[doc(hidden)]
			const __ALIAS_WIDTH: [(); 0] = [];
			#[doc(hidden)]
			const __ALIGNED_TO_SIZE: [(); 0] = [];
		}

		#[cfg(feature = "atomic")]
		impl BitStore for $aw {
			type Mem = $t;
			type Access = $a;
			type Alias = $aw;

			#[inline(always)]
			fn load_value(&self) -> $t {
				self.load()
			}

			#[doc(hidden)]
			type Threadsafe = Self;

			#[doc(hidden)]
			const __ALIGNED_TO_SIZE: [(); 0] = [(); mem::misaligned_to_size::<Self>()];

			#[doc(hidden)]
			const __ALIAS_WIDTH: [(); 0] = [(); mem::cmp_layout::<Self::Mem, Self::Alias>()];
		}

		impl seal::Sealed for $t {}
		impl seal::Sealed for $cw {}

		#[cfg(feature = "atomic")]
		impl seal::Sealed for $aw {}
	)+ };
}

store! {
	u8 => BitSafeCellU8 => BitSafeAtomU8 => AtomicU8,
	u16 => BitSafeCellU16 => BitSafeAtomU16 => AtomicU16,
	u32 => BitSafeCellU32 => BitSafeAtomU32 => AtomicU32,
}

#[cfg(target_pointer_width = "64")]
store!(u64 => BitSafeCellU64 => BitSafeAtomU64 => AtomicU64);

store!(usize => BitSafeCellUsize => BitSafeAtomUsize => AtomicUsize);

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
	use crate::{
		access::*,
		prelude::*,
	};

	use static_assertions::*;

	#[test]
	fn traits() {
		//  The integers are threadsafe, as they are known to be unaliased.
		assert_impl_all!(BitSlice<LocalBits, u8>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, u16>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, u32>: Send, Sync);
		assert_impl_all!(BitSlice<LocalBits, usize>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_impl_all!(BitSlice<LocalBits, u64>: Send, Sync);

		//  The integer alias is threadsafe when atomics are enabled.
		#[cfg(feature = "atomic")]
		{
			assert_impl_all!(BitSlice<LocalBits, <u8 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<LocalBits, <u16 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<LocalBits, <u32 as BitStore>::Alias>: Send, Sync);
			assert_impl_all!(BitSlice<LocalBits, <usize as BitStore>::Alias>: Send, Sync);

			#[cfg(target_pointer_width = "64")]
			assert_impl_all!(BitSlice<LocalBits, <u64 as BitStore>::Alias>: Send, Sync);
		}

		//  The integer alias is thread unsafe when atomics are disabled.
		#[cfg(not(feature = "atomic"))]
		{
			assert_not_impl_any!(BitSlice<LocalBits, <u8 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<LocalBits, <u16 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<LocalBits, <u32 as BitStore>::Alias>: Send, Sync);
			assert_not_impl_any!(BitSlice<LocalBits, <usize as BitStore>::Alias>: Send, Sync);

			#[cfg(target_pointer_width = "64")]
			assert_not_impl_any!(BitSlice<LocalBits, <u64 as BitStore>::Alias>: Send, Sync);
		}

		//  `Cell`s are never threadsafe.
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeCellU8>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeCellU16>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeCellU32>: Send, Sync);
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeCellUsize>: Send, Sync);

		#[cfg(target_pointer_width = "64")]
		assert_not_impl_any!(BitSlice<LocalBits, BitSafeCellU64>: Send, Sync);
	}
}
