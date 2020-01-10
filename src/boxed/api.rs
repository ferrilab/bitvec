/*! Reïmplementation of the `Box<[T]>` API.

This module tracks the [`alloc::boxed::Box`] module in the version of Rust
specified in the `rust-toolchain` file. It is required to provide an exact or
equivalent API surface matching the `Box<[T]>` type, to the extent that it is
possible in the language. Where differences occur, they must be documented in a
section called `API Differences`.

[`alloc::boxed::Box`]: https://doc.rust-lang.org/alloc/boxed/struct.Boxed.html
!*/

use crate::{
	boxed::BitBox,
	order::BitOrder,
	pointer::BitPtr,
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
	/// # API Differences
	///
	/// [`Box::new`] takes a `T` by direct value, and is not implemented as a
	/// means of cloning slices. As `BitSlice` cannot be held by value, this
	/// function clones the referent slice region into a new fixed-size heap
	/// buffer.
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
	/// # Notes
	///
	/// This function, and `into_raw`, exchange ordinary raw pointers
	/// `*mut BitSlice<O, T>`. Values of these types can be created from, and
	/// converted to, other region pointers such as `*mut [T]` through ordinary
	/// `as`-casting.
	///
	/// This is valid in the Rust type system, but is incorrect at runtime. You
	/// must not, ever, use `as` to cast in either direction to or from a
	/// `BitSlice` pointer.
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
	/// let b = unsafe { BitBox::<Lsb0, _>::from_raw(ptr) };
	/// ```
	///
	/// [`BitBox::into_raw`]: #method.into_raw
	pub unsafe fn from_raw(raw: *mut BitSlice<O, T>) -> Self {
		Self {
			_order: PhantomData,
			pointer: BitPtr::from_mut_ptr(raw),
		}
	}

	/// Consumes the `BitBox`, returning a wrapped raw pointer.
	///
	/// The pointer will be properly aligned and non-null.
	///
	/// After calling this function, the caller is responsible for the memory
	/// previously managed by the `BitBox`. In particular, the caller should
	/// properly release the memory by converting the pointer back into a
	/// `BitBox` with the [`BitBox::from_raw`] function, allowing the `BitBox`
	/// destructor to perform the cleanup.
	///
	/// Note: this is an associated function, which means that you have to call
	/// it as `BitBox::into_raw(b)` instead of `b.into_raw()`. This is to match
	/// layout with the standard library’s `Box` API; there will never be a name
	/// conflict with `BitSlice`.
	///
	/// # Notes
	///
	/// As with `::from_raw`, the pointer returned by this function must not
	/// ever have its type or value changed or inspected in any way. It may only
	/// be held and then passed into `::from_raw` in the future.
	///
	/// # Examples
	///
	/// Converting the raw pointer back into a `BitBox` with
	/// [`BitBox::from_raw`] for automatic cleanup:
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let b = BitBox::new(0u64.bits::<Msb0>());
	/// let ptr = BitBox::into_raw(b);
	/// let b = unsafe { BitBox::<Msb0, _>::from_raw(ptr) };
	/// ```
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub fn into_raw(b: Self) -> *mut BitSlice<O, T> {
		let out = b.pointer.as_mut_ptr();
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
	/// first be wrapped with the [`BitBox::from_raw`] function, producing a
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
