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
	cursor::Cursor,
	slice::BitSlice,
	store::BitStore,
};

use core::ops::{
	Deref,
	DerefMut,
};

/** Heavy-weight equivalent to `&mut bool`.

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
pub struct BitMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// A reference to a single bit in memory.
	pub(super) slot: &'a mut BitSlice<C, T>,
	/// A local cache for `Deref` usage.
	pub(super) data: bool,
}

impl<C, T> Deref for BitMut<'_, C, T>
where C: Cursor, T: BitStore {
	type Target = bool;

	fn deref(&self) -> &Self::Target {
		&self.data
	}
}

impl<C, T> DerefMut for BitMut<'_, C, T>
where C: Cursor, T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.data
	}
}

impl<C, T> Drop for BitMut<'_, C, T>
where C: Cursor, T: BitStore {
	fn drop(&mut self) {
		unsafe { self.slot.set_unchecked(0, self.data) }
	}
}
