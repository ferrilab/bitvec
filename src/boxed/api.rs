//! Reimplementation of the `Box` type’s inherent method API.

use super::*;

use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	marker::{
		PhantomData,
		Unpin,
	},
	mem,
	pin::Pin,
};

impl<O, T> BitBox<O, T>
where O: BitOrder, T: BitStore {
	/// Allocates memory on the heap and then places `bits` into it.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let boxed = BitBox::new(0u8.bits::<Lsb0>());
	/// ```
	pub fn new(bits: &BitSlice<O, T>) -> Self {
		Self::from_bitslice(bits)
	}

	/// Constructs a new `Pin<BitBox<O, T>>`.
	///
	/// `BitSlice` is always `Unpin`, so this has no actual immobility effect.
	pub fn pin(bits: &BitSlice<O, T>) -> Pin<Self>
	where O: Unpin, T: Unpin {
		Pin::new(Self::new(bits))
	}

	/// Constructs a bit box from a raw bit pointer.
	///
	/// After calling this function, the raw pointer is owned by the resulting
	/// `BitBox`. Specifically, the `BitBox` destructor will free the allocated
	/// memory. For this to be safe, the memory must have been allocated by
	/// `BitBox` earlier in the program.
	///
	/// # Safety
	///
	/// This function is unsafe because improper use may lead to memory
	/// problems. For example, a double-free may occurr if the function is
	/// called twice on the same raw pointer.
	///
	/// # Examples
	///
	/// Recreate a `BitBox` which was previously converted to a raw pointer
	/// using [`BitBox::into_raw`]:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let b = BitBox::new(0u8.bits::<Lsb0>());
	/// let ptr = BitBox::into_raw(b);
	/// let b = unsafe { BitBox::<Msb0, _>::from_raw(ptr) };
	/// ```
	pub unsafe fn from_raw(raw: BitPtr<T>) -> Self {
		Self {
			_order: PhantomData,
			pointer: raw,
		}
	}

	/// Consumes the `BitBox`, returning a wrapped raw pointer.
	///
	/// The pointer will be properly aligned and non-null.
	///
	/// After calling this function, the caller is responsible for the memory
	/// previously managed by the `BitBox`. In particular, the caller should
	/// properly release the memory, by converting the pointer back into a
	/// `BitBox` with the [`BitBox::from_raw`] function, allowing the `BitBox`
	/// destructor to perform the cleanup.
	///
	/// Note: this is an associated function, which means that you have to call
	/// it as `BitBox::into_raw(b)` instead of `b.into_raw()`. This is to match
	/// layout with the standard library’s `Box` API; there will never be a name
	/// conflict with `BitSlice`.
	///
	/// # Examples
	///
	/// Converting the raw pointer back into a `BitBox` with
	/// [`BitBox::from_raw`] for automatic cleanup:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let b = BitBox::new(0u64.bits::<Local>());
	/// let ptr = BitBox::into_raw(b);
	/// let b = unsafe { BitBox::<Msb0, _>::from_raw(ptr) };
	/// ```
	///
	/// [`BitBox::from_raw`]: #fn.from_raw
	pub fn into_raw(b: Self) -> BitPtr<T> {
		let out = b.pointer;
		mem::forget(b);
		out
	}

	/// Consumes and leaks the `BitBox`, returning a mutable reference,
	/// `&'a mut BitSlice<O, T>`. Note that the memory region `[T]` must outlive
	/// the chosen lifetime `'a`.
	///
	/// This function is mainly useful for bit regions that live for the
	/// remainder of the program’s life. Dropping the returned reference will
	/// cause a memory leak. If this is not acceptable, the reference should
	/// first be wrapped with the [`Box::from_raw`] function, producing a
	/// `BitBox`. This `BitBox` can then be dropped which will properly
	/// deallocate the memory.
	///
	/// Note: this is an associated function, which means that you have to call
	/// it as `BitBox::leak(b)` instead of `b.leak()`. This is to match layout
	/// with the standard library’s `Box` API; there will never be a name
	/// conflict with `BitSlice`.
	///
	/// # Examples
	///
	/// Simple usage:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let b = BitBox::new(0u64.bits::<Local>());
	/// let static_ref: &'static mut BitSlice<Local, u64> = BitBox::leak(b);
	/// static_ref.set(0, true);
	/// assert_eq!(static_ref.count_ones(), 1);
	/// ```
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub fn leak<'a>(self) -> &'a mut BitSlice<O, T> {
		let out = self.bitptr();
		mem::forget(self);
		out.into_bitslice_mut()
	}
}
