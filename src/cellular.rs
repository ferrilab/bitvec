/*! Cellular element access

This module enables the `BitStore` trait to access its storage elements through
`Cell` wrappers, which are a poorer substitute for atomic access but are good
enough for environments that cannot observe true parallelism.

Rust requires the use of `&Cell<T>` instead of `&mut T` when modifying the
underlying element store, because `BitSlice` is capable of producing write
references that alias the same element from different `BitSlice` handles. As
aliased `&mut` references are illegal, but `&Cell` references are type-level
immutable and thus permitted to alias, this sidesteps the `&mut` alias checks
and permits sound write access to the underlying store.

This module is only enabled when the default `atomic` feature is turned off. The
`x86` architecture guarantees that this module will still observe atomic
behavior; other architectures might not.

As the crate routes all writes through either this module or the `atomic`
module, these two sites can guarantee that all access follows a
read/modify/write immediate cycle, and does not cache the read value for any
longer than is required to modify it and write back.
!*/

#![cfg(not(feature = "atomic"))]

use crate::{
	cursor::Cursor,
	store::{
		BitIdx,
		BitStore,
	},
};

use core::cell::Cell;

/** Cellular element access

This is not part of the public API; it is an implementation detail of
[`BitStore`], which is public API but is not publicly implementable.

This trait provides four methods, which the `BitStore` trait uses to manipulate
or inspect storage items in as safe a manner as is possible without atomic
operations.

# Synchrony

This module is present only when the `atomic` feature has been disabled. Its
accesses are not synchronized, and are subject to race conditions under
parallelism. Since `BitSlice` removes its `Send` implementation in these
conditions, race conditions that cause data loss cannot occur.

[`BitStore`]: ../store/trait.BitStore.html
**/
pub trait Cellular: Sized {
	/// Defines the underlying fundamental type that this trait is wrapping.
	type Fundamental: BitStore;

	/// Sets the bit at some position to `0`.
	///
	/// # Parameters
	///
	/// - `&self`: This is able to be immutable, rather than mutable, because
	///   the trait is implemented on a `Cell` wrapper.
	/// - `bit`: The position in the element to set low.
	fn clear<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor;

	/// Sets the bit at some position to `1`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `bit`: The position in the element to set high.
	fn set<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor;

	/// Inverts the bit at some position.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `bit`: The position in the element to invert.
	fn invert<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor;

	/// Gets the element underneath the cellular access.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The fundamental type underneath the cellular type.
	fn get(&self) -> Self::Fundamental;
}

impl Cellular for Cell<u8> {
	type Fundamental = u8;

	#[inline(always)]
	fn clear<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get(&self) -> u8 {
		self.get()
	}
}

impl Cellular for Cell<u16> {
	type Fundamental = u16;

	#[inline(always)]
	fn clear<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get(&self) -> u16 {
		self.get()
	}
}

impl Cellular for Cell<u32> {
	type Fundamental = u32;

	#[inline(always)]
	fn clear<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get(&self) -> u32 {
		self.get()
	}
}

#[cfg(target_pointer_width = "64")]
impl Cellular for Cell<u64> {
	type Fundamental = u64;

	#[inline(always)]
	fn clear<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() & !*C::mask(bit));
	}

	#[inline(always)]
	fn set<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() | *C::mask(bit));
	}

	#[inline(always)]
	fn invert<C>(&self, bit: BitIdx<Self::Fundamental>)
	where C: Cursor {
		self.set(self.get() ^ *C::mask(bit));
	}

	#[inline(always)]
	fn get(&self) -> u64 {
		self.get()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		cursor::LittleEndian,
		store::IntoBitIdx,
	};

	#[test]
	fn cell_u8() {
		let cell = Cell::<u8>::new(0);

		Cellular::set::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 1);

		Cellular::clear::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 0);

		Cellular::invert::<LittleEndian>(&cell, 1.idx());
		assert_eq!(Cellular::get(&cell), 2);
	}

	#[test]
	fn cell_u16() {
		let cell = Cell::<u16>::new(0);

		Cellular::set::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 1);

		Cellular::clear::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 0);

		Cellular::invert::<LittleEndian>(&cell, 1.idx());
		assert_eq!(Cellular::get(&cell), 2);
	}

	#[test]
	fn cell_u32() {
		let cell = Cell::<u32>::new(0);

		Cellular::set::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 1);

		Cellular::clear::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 0);

		Cellular::invert::<LittleEndian>(&cell, 1.idx());
		assert_eq!(Cellular::get(&cell), 2);
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn cell_u64() {
		let cell = Cell::<u64>::new(0);

		Cellular::set::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 1);

		Cellular::clear::<LittleEndian>(&cell, 0.idx());
		assert_eq!(Cellular::get(&cell), 0);

		Cellular::invert::<LittleEndian>(&cell, 1.idx());
		assert_eq!(Cellular::get(&cell), 2);
	}
}
