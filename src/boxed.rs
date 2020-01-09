/*! `BitBox` structure

This module holds the type for an owned but ungrowable bit sequence. `BitVec` is
the more appropriate and useful type for most collections.
!*/

#![cfg(feature = "alloc")]

use crate::{
	order::{
		BitOrder,
		Local,
	},
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

use alloc::{
	boxed::Box,
	vec::Vec,
};

use core::{
	marker::PhantomData,
	mem,
};

/** A pointer type for owned bit sequences.

This type is essentially a `&BitSlice` that owns its own memory. It can change
the contents of its domain, but it cannot change its own domain like `BitVec`
can. It is useful for fixed-size collections without lifetime tracking.

# Type Parameters

- `O: BitOrder`: An implementor of the [`BitOrder`] trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the [`BitStore`] trait: `u8`, `u16`, `u32`,
  or `u64` (64-bit systems only). This is the actual type in memory that the box
  will use to store data.

# Safety

The `BitBox` handle has the same *size* as standard Rust `Box<[T]>` handles, but
it is ***extremely binary incompatible*** with them. Attempting to treat
`BitBox<_, T>` as `Box<[T]>` in any manner except through the provided APIs is
***catastrophically*** unsafe and unsound.

# Trait Implementations

`BitBox<O, T>` implements all the traits that `BitSlice<O, T>` does, by
deferring to the `BitSlice` implementation. It also implements conversion traits
to and from `BitSlice`, and to/from `BitVec`.
**/
#[repr(C)]
pub struct BitBox<O = Local, T = usize>
where O: BitOrder, T: BitStore {
	_order: PhantomData<O>,
	pointer: BitPtr<T>,
}

impl<O, T> BitBox<O, T>
where O: BitOrder, T: BitStore {
	/// Constructs an empty boxed bitslice.
	///
	/// # Returns
	///
	/// An empty `BitBox` at an arbitrary location.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox = BitBox::empty();
	/// assert!(bb.is_empty());
	/// ```
	pub fn empty() -> Self {
		Self {
			_order: PhantomData,
			pointer: BitPtr::empty(),
		}
	}

	/// Produces a `BitBox` from a single element.
	///
	/// # Parameters
	///
	/// - `elt`: The source element from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox<Msb0, u16> = BitBox::from_element(!0);
	/// assert!(bb.all());
	/// ```
	pub fn from_element(elt: T) -> Self {
		BitSlice::<O, T>::from_element(&elt).into()
	}

	/// Builds a `BitBox` from a borrowed slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the (cloned) provided slice.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [5, 10];
	/// let bb: BitBox<Msb0, u8> = BitBox::from_slice(&src[..]);
	/// assert!(bb[5]);
	/// assert!(bb[7]);
	/// assert!(bb[12]);
	/// assert!(bb[14]);
	/// ```
	pub fn from_slice(slice: &[T]) -> Self {
		BitVec::from_slice(slice).into_boxed_bitslice()
	}

	/// Clones a `&BitSlice` into a `BitBox`.
	///
	/// # Parameters
	///
	/// - `slice`: The bit slice to clone into a bit box.
	///
	/// # Returns
	///
	/// A `BitBox` containing the same bits as the source slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, !0];
	/// let bb = BitBox::<Msb0, _>::from_bitslice(src.bits());
	/// assert_eq!(bb.len(), 16);
	/// assert!(bb.some());
	/// ```
	pub fn from_bitslice(slice: &BitSlice<O, T>) -> Self {
		BitVec::from_bitslice(slice).into_boxed_bitslice()
	}

	/// Produces a `BitBox` from an owned slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source boxed slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` governing the same slice that was passed in. This function
	/// does not reallocate.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<Lsb0, _>::from_boxed_slice(slice);
	/// assert!(bb.some());
	/// assert_eq!(bb.len(), 32);
	/// ```
	pub fn from_boxed_slice(boxed: Box<[T]>) -> Self {
		let len = boxed.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitBox cannot address {} elements",
			len,
		);

		let bs = BitSlice::<O, T>::from_slice(&boxed[..]);
		let pointer = bs.bitptr();
		let out = Self {
			_order: PhantomData,
			pointer,
		};
		mem::forget(boxed);
		out
	}

	/// Removes the `BitBox` wrapper from a `Box<[T]>`.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The `Box<[T]>` underneath `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<Lsb0, _>::from_boxed_slice(slice);
	/// assert_eq!(bb.len(), 32);
	/// let slice = bb.into_boxed_slice();
	/// assert_eq!(slice.len(), 2);
	/// ```
	pub fn into_boxed_slice(self) -> Box<[T]> {
		let slice = self.pointer.as_mut_slice();
		let (data, elts) = (slice.as_mut_ptr(), slice.len());
		let out = unsafe { Vec::from_raw_parts(data, elts, elts) }
			.into_boxed_slice();
		mem::forget(self);
		out
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This delegates to `BitSlice::add_assign_reverse`.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `addend: impl IntoIterator<Item=bool>`: A bitstream to add to `self`.
	///
	/// # Returns
	///
	/// The sum of `self` and `addend`.
	pub fn add_reverse<I>(mut self, addend: I) -> Self
	where I: IntoIterator<Item=bool> {
		self.add_assign_reverse(addend);
		self
	}

	/// Changes the order on a box handle, without changing the data it
	/// governs.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An equivalent handle to the same data, with a new order parameter.
	pub fn change_order<P>(self) -> BitBox<P, T>
	where P: BitOrder {
		let bp = self.bitptr();
		mem::forget(self);
		unsafe { BitBox::from_raw(bp.as_mut_ptr()) }
	}

	/// Accesses the `BitSlice<O, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_bitslice(&self) -> &BitSlice<O, T> {
		self.pointer.into_bitslice()
	}

	/// Accesses the `BitSlice<O, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, T> {
		self.pointer.into_bitslice_mut()
	}

	/// Accesses the vector’s backing store as an element slice.
	///
	/// Unlike `BitSlice`’s method of the same name, this includes the partial
	/// edges, as `BitBox` forbids fragmentation that leads to contention.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The slice of all live elements in the backing storage, including the
	/// partial edges if present.
	pub fn as_slice(&self) -> &[T] {
		self.bitptr().as_slice()
	}

	/// Accesses the vector’s backing store as an element slice.
	///
	/// Unlike `BitSlice`’s method of the same name, this includes the partial
	/// edges, as `BitBox` forbids fragmentation that leads to contention.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The slice of all live elements in the backing storage, including the
	/// partial edges if present.
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		self.bitptr().as_mut_slice()
	}

	/// Gives read access to the `BitPtr<T>` structure powering the box.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A copy of the interior `BitPtr<T>`.
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.pointer
	}

	/// Allows a function to access the `Box<[T]>` that the `BitBox` is using
	/// under the hood.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `func`: A function which works with a borrowed `Box<[T]>` representing
	///   the actual memory held by the `BitBox`.
	///
	/// # Type Parameters
	///
	/// - `F: FnOnce(&Box<[T]>) -> R`: A function which borrows a box.
	/// - `R`: The return value of the function.
	///
	/// # Returns
	///
	/// The return value of the provided function.
	fn do_with_box<F, R>(&self, func: F) -> R
	where F: FnOnce(&Box<[T]>) -> R {
		let slice = self.pointer.as_mut_slice();
		let (data, elts) = (slice.as_mut_ptr(), slice.len());
		let b: Box<[T]> = unsafe {
			Vec::from_raw_parts(data, elts, elts)
		}.into_boxed_slice();
		let out = func(&b);
		mem::forget(b);
		out
	}
}

mod api;
mod iter;
mod ops;
mod traits;

pub use api::*;
pub use iter::*;
