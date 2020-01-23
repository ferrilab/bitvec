/*! Heavy bit reference.

Regrettably, while producing a read reference to a bit inside a `BitSlice` is
relatively easy to do, Rust’s rules make it impossible to produce a write
reference to one. This is because references must be addresses that the holder
can derefence without type consideration. Read references inspect the `BitSlice`
data sequence, and then produce references to static `true` and `false` values
as appropriate; the returned address does not need to be actually within the
referent memory region.

A write reference, however, is required to be the address of a `bool` within the
`BitSlice`, which can have `0u8` or `1u8` written into it. This rule makes
production of any `&mut bool` from any `&mut BitSlice` impossible. Instead, the
`BitMut` structure serves as a heavy-weight referential object, that cannot be
used in the `&mut` write reference system, as a good-enough substitute.
!*/

use crate::{
	access::BitAccess,
	indices::BitIdx,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	marker::PhantomData,
	ops::{
		Deref,
		DerefMut,
	},
	ptr::NonNull,
};

/** Proxy referential type, equivalent to `&mut bool`.

This structure is three words wide, and cannot ever fit into the existing Rust
language and library infrastructure in the way `&BitSlice` does. While `&mut`
write references are themselves an affine type, with a guaranteed single point
of destruction and no duplication, the language forbids writing finalization
logic for them.

This means that a custom reference type which implements `Deref` and `DerefMut`
to a location within the canonical handle, and on `Drop` writes the `Deref`
location into referent memory, is impossible. Short of that, a C++-style thick
reference-like type is as close as Rust will allow.
**/
pub struct BitMut<'a, O, T>
where O: BitOrder, T: 'a + BitStore {
	/// Inform the compiler that this has an exclusive borrow of a `BitSlice`
	pub(super) _parent: PhantomData<&'a mut BitSlice<O, T>>,
	/// Typed pointer to the memory element containing the proxied bit.
	pub(super) data: NonNull<T::Access>,
	/// Index of the proxied bit inside the targeted memory element.
	pub(super) head: BitIdx<T>,
	/// A local cache for `Deref` usage.
	pub(super) bit: bool,
}

impl<O, T> Deref for BitMut<'_, O, T>
where O: BitOrder, T: BitStore {
	type Target = bool;

	fn deref(&self) -> &Self::Target {
		&self.bit
	}
}

impl<O, T> DerefMut for BitMut<'_, O, T>
where O: BitOrder, T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.bit
	}
}

impl<O, T> Drop for BitMut<'_, O, T>
where O: BitOrder, T: BitStore {
	fn drop(&mut self) {
		unsafe { (*self.data.as_ptr()).set::<O>(self.head, self.bit) }
	}
}
