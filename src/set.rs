#![doc = include_str!("../doc/set.md")]
#![cfg(feature = "alloc")]

#[cfg(not(feature = "std"))]
use alloc::vec;
use core::ops;

use wyz::comu::{
	Const,
	Mut,
};

use crate::{
	boxed::BitBox,
	order::{
		BitOrder,
		Lsb0,
	},
	ptr::BitPtr,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

mod api;
mod iter;
mod traits;

pub use iter::Range;

#[repr(transparent)]
#[doc = include_str!("../doc/set/BitSet.md")]
pub struct BitSet<T = usize, O = Lsb0>
where
	T: BitStore,
	O: BitOrder,
{
	inner: BitVec<T, O>,
}

/// Constructors.
impl<T, O> BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	/// An empty bit-set with no backing allocation.
	pub const EMPTY: Self = Self {
		inner: BitVec::EMPTY,
	};

	/// Creates a new bit-set for a range of indices.
	#[inline]
	pub fn from_range(range: ops::Range<usize>) -> Self {
		let mut inner = BitVec::with_capacity(range.end);
		unsafe {
			inner.set_len(range.end);
			inner[.. range.start].fill(false);
			inner[range.start ..].fill(true);
		}
		Self { inner }
	}

	/// Constructs a new bit-set from an existing bit-vec.
	#[inline]
	pub fn from_bitvec(inner: BitVec<T, O>) -> Self {
		Self { inner }
	}
}

/// Converters.
impl<T, O> BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	/// Explicitly views the bit-set as a bit-slice.
	#[inline]
	pub fn as_bitslice(&self) -> &BitSlice<T, O> {
		self.inner.as_bitslice()
	}

	/// Explicitly views the bit-set as a mutable bit-slice.
	#[inline]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<T, O> {
		self.inner.as_mut_bitslice()
	}

	/// Explicitly views the bit-set as a bit-vec.
	#[inline]
	pub fn as_bitvec(&self) -> &BitVec<T, O> {
		&self.inner
	}

	/// Explicitly views the bit-set as a mutable bit-vec.
	#[inline]
	pub fn as_mut_bitvec(&mut self) -> &mut BitVec<T, O> {
		&mut self.inner
	}

	/// Views the bit-set as a slice of its underlying memory elements.
	#[inline]
	pub fn as_raw_slice(&self) -> &[T] {
		self.inner.as_raw_slice()
	}

	/// Views the bit-set as a mutable slice of its underlying memory
	/// elements.
	#[inline]
	pub fn as_raw_mut_slice(&mut self) -> &mut [T] {
		self.inner.as_raw_mut_slice()
	}

	/// Creates an unsafe shared bit-pointer to the start of the buffer.
	///
	/// ## Original
	///
	/// [`Vec::as_ptr`](alloc::vec::Vec::as_ptr)
	///
	/// ## Safety
	///
	/// You must initialize the contents of the underlying buffer before
	/// accessing memory through this pointer. See the `BitPtr` documentation
	/// for more details.
	#[inline]
	pub fn as_bitptr(&self) -> BitPtr<Const, T, O> {
		self.inner.as_bitptr()
	}

	/// Creates an unsafe writable bit-pointer to the start of the buffer.
	///
	/// ## Original
	///
	/// [`Vec::as_mut_ptr`](alloc::vec::Vec::as_mut_ptr)
	///
	/// ## Safety
	///
	/// You must initialize the contents of the underlying buffer before
	/// accessing memory through this pointer. See the `BitPtr` documentation
	/// for more details.
	#[inline]
	pub fn as_mut_bitptr(&mut self) -> BitPtr<Mut, T, O> {
		self.inner.as_mut_bitptr()
	}

	/// Converts a bit-set into a boxed bit-slice.
	///
	/// This may cause a reällocation to drop any excess capacity.
	///
	/// ## Original
	///
	/// [`Vec::into_boxed_slice`](alloc::vec::Vec::into_boxed_slice)
	#[inline]
	pub fn into_boxed_bitslice(self) -> BitBox<T, O> {
		self.inner.into_boxed_bitslice()
	}

	/// Converts a bit-set into a bit-vec.
	#[inline]
	pub fn into_bitvec(self) -> BitVec<T, O> {
		self.inner
	}
}

/// Utilities.
impl<T, O> BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	/// Shrinks the inner vector to the minimum size, without changing capacity.
	#[inline]
	fn shrink_inner(&mut self) {
		match self.inner.last_one() {
			Some(idx) => self.inner.truncate(idx + 1),
			None => self.inner.clear(),
		}
	}

	/// Immutable shrink as a bitslice.
	#[inline]
	fn shrunken(&self) -> &BitSlice<T, O> {
		match self.inner.last_one() {
			Some(idx) => &self.inner[.. idx + 1],
			None => Default::default(),
		}
	}
}
