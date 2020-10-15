/*! Memory access guards.

[`bitvec`] allows a program to produce handles over memory that do not logically
alias their bits, but may alias in hardware. This module provides a unified
interface for memory accesses that can be specialized to handle aliased and
unaliased access events.

The [`BitAccess`] trait provides capabilities to access bits in memory elements
through shared references, and its implementations are responsible for
coördinating synchronization and contention as needed.

The [`BitSafe`] trait abstracts over wrappers to the [`Cell`] and [atomic] types
that forbid writing through their references, even when other references to the
same location may write.

[`BitAccess`]: self::BitAccess
[`BitSafe`]: self::BitSafe
[`bitvec`]: crate
!*/

use crate::{
	index::{
		BitIdx,
		BitMask,
	},
	mem::BitRegister,
	order::BitOrder,
};

use core::{
	cell::Cell,
	sync::atomic,
};

use radium::Radium;

/** Abstracts over the instructions used when accessing a memory location.

This trait provides functions to manipulate bits in a referent memory register
through the appropriate access instructions, so that use sites elsewhere in the
crate can select their required behavior without changing their interface.

This is automatically implemented for all types that permit shared/mutable
memory access to memory registers through the [`radium`] crate. Its use is
constrained in the [`store`] module.

This trait is only ever used by [`bitvec`] internals, and is never exposed
outside the crate. It must be marked as public so that it can be used as an
associated item in [`BitStore`], even though it is never made accessible.

[`BitStore`]: crate::store::BitStore
[`bitvec`]: crate
[`radium`]: radium
[`store`]: crate::store
**/
pub trait BitAccess: Radium
where <Self as Radium>::Item: BitRegister
{
	/// Clears one bit in a memory register to `0`.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit in `*self` to be cleared.
	///
	/// # Effects
	///
	/// The memory register at address `self` has the bit corresponding to the
	/// `index` cursor under the `O` order cleared to `0`, and all other bits
	/// are unchanged.
	#[inline]
	fn clear_bit<O>(&self, index: BitIdx<Self::Item>)
	where O: BitOrder {
		self.fetch_and(!index.select::<O>().value(), atomic::Ordering::Relaxed);
	}

	/// Clears any number of bits in a memory register to `0`.
	///
	/// The mask provided to this method must be constructed from indices that
	/// are valid in the caller’s context. As the mask is already computed by
	/// the caller, this does not take an ordering type parameter.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: A mask of any number of bits. This is a selection mask: all
	///   bits in the mask that are set to `1` will be modified in the element
	///   at `*self`.
	///
	/// # Effects
	///
	/// All bits in `*self` that are selected (set to `1` in the `mask`) will be
	/// cleared. All bits in `*self` that are not selected (cleared to `0` in
	/// the `mask`) are unchanged.
	///
	/// Do not invert the `mask` prior to calling this function in order to save
	/// the unselected bits and clear the selected bits. [`BitMask`] is a
	/// selection type, not a bitwise-operation argument.
	///
	/// [`BitMask`]: crate::index::BitMask
	#[inline]
	fn clear_bits(&self, mask: BitMask<Self::Item>) {
		self.fetch_and(!mask.value(), atomic::Ordering::Relaxed);
	}

	/// Sets one bit in a memory register to `1`.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit in `*self` to be set.
	///
	/// # Effects
	///
	/// The memory register at address `self` has the bit corresponding to the
	/// `index` cursor under the `O` order set to `1`, and all other bits are
	/// unchanged.
	#[inline]
	fn set_bit<O>(&self, index: BitIdx<Self::Item>)
	where O: BitOrder {
		self.fetch_or(index.select::<O>().value(), atomic::Ordering::Relaxed);
	}

	/// Sets any number of bits in a memory register to `1`.
	///
	/// The mask provided to this method must be constructed from indices that
	/// are valid in the caller’s context. As the mask is already computed by
	/// the caller, this does not take an ordering type parameter.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: A mask of any number of bits. This is a selection mask: all
	///   bits in the mask that are set to `1` will be modified in the element
	///   at `*self`.
	///
	/// # Effects
	///
	/// All bits in `*self` that are selected (set to `1` in the `mask`) will be
	/// cleared. All bits in `*self` that are not selected (cleared to `0` in
	/// the `mask`) are unchanged.
	#[inline]
	fn set_bits(&self, mask: BitMask<Self::Item>) {
		self.fetch_or(mask.value(), atomic::Ordering::Relaxed);
	}

	/// Inverts one bit in a memory register.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit in `*self` to be inverted.
	///
	/// # Effects
	///
	/// The memory register at address `self` has the bit corresponding to the
	/// `index` cursor under the `O` order inverted, and all other bits are
	/// unchanged.
	#[inline]
	fn invert_bit<O>(&self, index: BitIdx<Self::Item>)
	where O: BitOrder {
		self.fetch_xor(index.select::<O>().value(), atomic::Ordering::Relaxed);
	}

	/// Inverts any number of bits in a memory register.
	///
	/// The mask provided to this method must be constructed from indices that
	/// are valid in the caller’s context. As the mask is already computed by
	/// the caller, this does not take an ordering type parameter.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: A mask of any number of bits. This is a selection mask: all
	///   bits in the mask that are set to `1` will be modified in the element
	///   at `*self`.
	///
	/// # Effects
	///
	/// All bits in `*self` that are selected (set to `1` in the `mask`) will be
	/// inverted. All bits in `*self` that are not selected (cleared to `0` in
	/// the `mask`) are unchanged.
	#[inline]
	fn invert_bits(&self, mask: BitMask<Self::Item>) {
		self.fetch_xor(mask.value(), atomic::Ordering::Relaxed);
	}

	/// Writes a value to one bit in a memory register.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit in `*self` to write.
	/// - `value`: The bit value to write into `*self` at `index`.
	///
	/// # Effects
	///
	/// The memory register at address `self` has the bit corresponding to the
	/// `index` cursor under the `O` order written with the new `value`, and all
	/// other bits are unchanged.
	#[inline]
	fn write_bit<O>(&self, index: BitIdx<Self::Item>, value: bool)
	where O: BitOrder {
		if value {
			self.set_bit::<O>(index);
		}
		else {
			self.clear_bit::<O>(index);
		}
	}

	/// Writes a value to any number of bits in a memory register.
	///
	/// The mask provided to this method must be constructed from indices that
	/// are valid in the caller’s context. As the mask is already computed by
	/// the caller, this does not take an ordering type parameter.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: A mask of any number of bits. This is a selection mask: all
	///   bits in the mask that are set to `1` will be modified in the element
	///   at `*self`.
	///
	/// # Effects
	///
	/// All bits in `*self` that are selected (set to `1` in the `mask`) will be
	/// written with the new `value`. All bits in `*self` that are not selected
	/// (cleared to `0` in the `mask`) are unchanged.
	#[inline]
	fn write_bits(&self, mask: BitMask<Self::Item>, value: bool) {
		if value {
			self.set_bits(mask);
		}
		else {
			self.clear_bits(mask);
		}
	}

	/// Gets the function that writes `value` to an index.
	///
	/// # Type Parameters
	///
	/// - `O`: A bit ordering.
	///
	/// # Parameters
	///
	/// - `value`: The bit that will be directly written by the returned
	///   function.
	///
	/// # Returns
	///
	/// A function which, when applied to a reference and an index, will write
	/// `value` into memory. If `value` is `false`, then this produces
	/// [`clear_bit`]; if it is `true`, then this produces [`set_bit`].
	///
	/// [`clear_bit`]: Self::clear_bit
	/// [`set_bit`]: Self::set_bit
	#[inline]
	fn get_writer<O>(value: bool) -> for<'a> fn(&'a Self, BitIdx<Self::Item>)
	where O: BitOrder {
		if value {
			Self::set_bit::<O>
		}
		else {
			Self::clear_bit::<O>
		}
	}

	/// Gets the function that writes `value` into all bits under a mask.
	///
	/// # Parameters
	///
	/// - `value`: The bit that will be directly written by the returned
	///   function.
	///
	/// # Returns
	///
	/// A function which, when applied to a reference and a mask, will write
	/// `value` into memory. If `value` is `false`, then this produces
	/// [`clear_bits`]; if it is `true`, then this produces [`set_bits`].
	///
	/// [`clear_bits`]: Self::clear_bits
	/// [`set_bits`]: Self::set_bits
	#[inline]
	fn get_writers(value: bool) -> for<'a> fn(&'a Self, BitMask<Self::Item>) {
		if value {
			Self::set_bits
		}
		else {
			Self::clear_bits
		}
	}

	/// Unconditionally writes a value into a memory location.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `value`: The new value to write into `*self`.
	///
	/// # Effects
	///
	/// The current value at `*self` is replaced with `value`.
	///
	/// # Safety
	///
	/// The calling context must either have write permissions to the entire
	/// memory element at `*self`, or construct a `value` that does not modify
	/// the bits of `*self` that the caller does not currently own.
	///
	/// As this directly permits the modification of memory outside the logical
	/// ownership of the caller, this method risks behavior that violates the
	/// Rust memory model, even if it may not be technically undefined.
	#[inline]
	fn store_value(&self, value: Self::Item) {
		self.store(value, atomic::Ordering::Relaxed);
	}
}

impl<A> BitAccess for A
where
	A: Radium,
	A::Item: BitRegister,
{
}

/** Restricts memory modification to only exclusive references.

The shared-mutability types do not permit locking their references to prevent
writing through them when inappropriate. Implementors of this trait are able to
view aliased memory and handle other references writing to it, even though they
themselves may be forbidden from doing so.
**/
pub trait BitSafe {
	/// The register type being guarded against shared mutation.
	type Mem: BitRegister;

	/// Reads the value out of memory only if a shared reference to the location
	/// can be produced.
	fn load(&self) -> Self::Mem;
}

macro_rules! safe {
	($($t:ident => $cw:ident => $aw:ident => $a:path),+ $(,)?) => { $(
		/// A wrapper over a [`Cell`] that forbids writing to the location
		/// through its own reference. Other references to the location may
		/// still write to it.
		///
		/// This is necessary in order to enforce [`bitvec`]’s memory model,
		/// which disallows shared mutation to individual bits. [`BitSlice`]s
		/// may produce memory views that use this type in order to ensure that
		/// handles that lack write permission to an area may not write to it,
		/// even if other handles may.
		///
		/// [`BitSlice`]: crate::slice::BitSlice
		/// [`Cell`]: core::cell::Cell
		/// [`bitvec`]: crate
		#[derive(Debug)]
		#[repr(transparent)]
		#[cfg(not(tarpaulin_include))]
		pub struct $cw {
			inner: Cell<$t>,
		}

		/// A wrapper over an [atom] that forbids writing to the location
		/// through its own reference. Other references to the location may
		/// still write to it.
		///
		/// This is necessary in order to enforce [`bitvec`]’s memory model,
		/// which disallows shared mutation to individual bits. [`BitSlice`]s
		/// may produce memory views that use this type in order to ensure that
		/// handles that lack write permission to an area may not write to it,
		/// even if other handles may.
		///
		/// [`BitSlice`]: crate::slice::BitSlice
		/// [atom]: core::sync::atomic
		/// [`bitvec`]: crate
		#[derive(Debug)]
		#[repr(transparent)]
		#[cfg(feature = "atomic")]
		#[cfg(not(tarpaulin_include))]
		pub struct $aw {
			inner: $a,
		}

		#[cfg(not(tarpaulin_include))]
		impl BitSafe for $cw {
			type Mem = $t;

			#[inline(always)]
			fn load(&self) -> $t {
				self.inner.get()
			}
		}

		#[cfg(feature = "atomic")]
		#[cfg(not(tarpaulin_include))]
		impl BitSafe for $aw {
			type Mem = $t;

			#[inline(always)]
			fn load(&self) -> $t {
				self.inner.load(atomic::Ordering::Relaxed)
			}
		}
	)+ };
}

safe! {
	u8 => BitSafeCellU8 => BitSafeAtomU8 => atomic::AtomicU8,
	u16 => BitSafeCellU16 => BitSafeAtomU16 => atomic::AtomicU16,
	u32 => BitSafeCellU32 => BitSafeAtomU32 => atomic::AtomicU32,
}

#[cfg(target_pointer_width = "64")]
safe!(u64 => BitSafeCellU64 => BitSafeAtomU64 => atomic::AtomicU64);

safe!(usize => BitSafeCellUsize => BitSafeAtomUsize => atomic::AtomicUsize);

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn touch_memory() {
		let mut data = 0u8;
		let bits = data.view_bits_mut::<LocalBits>();
		let accessor = unsafe { &*(bits.bitptr().pointer().to_access()) };
		let aliased = unsafe {
			&*(bits.bitptr().pointer().to_const()
				as *const <u8 as BitStore>::Alias)
		};

		BitAccess::set_bit::<Lsb0>(accessor, BitIdx::ZERO);
		assert_eq!(accessor.get(), 1);

		BitAccess::set_bits(accessor, BitMask::ALL);
		assert_eq!(accessor.get(), !0);

		BitAccess::clear_bit::<Lsb0>(accessor, BitIdx::ZERO);
		assert_eq!(accessor.get(), !1);

		BitAccess::clear_bits(accessor, BitMask::ALL);
		assert_eq!(accessor.get(), 0);

		BitAccess::invert_bit::<Lsb0>(accessor, BitIdx::ZERO);
		assert_eq!(accessor.get(), 1);
		BitAccess::invert_bits(accessor, BitMask::ALL);
		assert_eq!(accessor.get(), !1);

		assert!(!BitStore::get_bit::<Lsb0>(aliased, BitIdx::ZERO));
		assert_eq!(accessor.get(), !1);

		BitAccess::write_bit::<Lsb0>(accessor, BitIdx::new(1).unwrap(), false);
		assert_eq!(accessor.get(), !3);

		BitAccess::write_bits(accessor, BitMask::ALL, true);
		assert_eq!(accessor.get(), !0);
		BitAccess::write_bits(
			accessor,
			Lsb0::mask(BitIdx::new(2).unwrap(), None),
			false,
		);
		assert_eq!(
			BitStore::get_bits(
				aliased,
				Lsb0::mask(BitIdx::new(2).unwrap(), None)
			),
			0
		);
		assert_eq!(accessor.get(), 3);

		BitAccess::get_writer::<Lsb0>(false)(accessor, BitIdx::ZERO);
		assert_eq!(accessor.get(), 2);

		BitAccess::store_value(accessor, !1);
		assert_eq!(accessor.get(), !1);
	}

	#[test]
	#[cfg(not(miri))]
	fn sanity_check_prefetch() {
		assert_eq!(
			<Cell<u8> as BitAccess>::get_writer::<Msb0>(false) as *const (),
			<Cell<u8> as BitAccess>::clear_bit::<Msb0> as *const ()
		);

		assert_eq!(
			<Cell<u8> as BitAccess>::get_writer::<Msb0>(true) as *const (),
			<Cell<u8> as BitAccess>::set_bit::<Msb0> as *const ()
		);

		assert_eq!(
			<Cell<u8> as BitAccess>::get_writers(false) as *const (),
			<Cell<u8> as BitAccess>::clear_bits as *const ()
		);

		assert_eq!(
			<Cell<u8> as BitAccess>::get_writers(true) as *const (),
			<Cell<u8> as BitAccess>::set_bits as *const ()
		);
	}
}
