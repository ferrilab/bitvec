use alloc::{
	boxed::Box,
	vec::Vec,
};
use core::{
	marker::PhantomData,
	mem,
	slice,
	sync::atomic::Ordering,
};

use radium::Radium;
use tap::Pipe;

use crate::{
	order::BitOrder,
	ptr::{
		BitSpan,
		Mut,
	},
	slice::BitSlice,
	store::BitStore,
};

/// The reference counters in a buffer.
#[repr(C)]
#[derive(Clone, Debug)]
pub(super) struct BitRefCounts<R>
where R: Radium<Item = usize>
{
	/// The count of all strong handles to the buffer.
	pub(super) strong: R,
	/// The count of all weak handles to the buffer, plus one if *any* strong
	/// handles exist. All strong handles are collectively also a weak handle.
	///
	/// This explicit plus-one is present to ensure that running a strong-handle
	/// destructor never accidentally triggers a weak-handle destructor also.
	pub(super) weak: R,
}

impl<R> BitRefCounts<R>
where R: Radium<Item = usize>
{
	#[inline]
	pub(super) fn get_strong(&self) -> usize {
		self.strong.load(Ordering::Acquire)
	}

	#[inline]
	pub(super) fn incr_strong(&self) -> usize {
		self.strong.fetch_add(1, Ordering::SeqCst)
	}

	#[inline]
	pub(super) fn decr_strong(&self) -> usize {
		self.strong.fetch_sub(1, Ordering::SeqCst)
	}

	#[inline]
	pub(super) fn get_weak(&self) -> usize {
		self.weak.load(Ordering::Acquire)
	}

	#[inline]
	pub(super) fn incr_weak(&self) -> usize {
		self.weak.fetch_add(1, Ordering::SeqCst)
	}

	#[inline]
	pub(super) fn decr_weak(&self) -> usize {
		self.weak.fetch_sub(1, Ordering::SeqCst)
	}
}

/** The layout of the allocated buffer.

This is layout-equivalent to the `RcBox` structure defined in the standard
library. It consists of two words (the refcounts), followed by a
`BitSlice<O, T>` region.
**/
#[repr(C)]
#[derive(Debug)]
pub(super) struct BitRefBox<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// The refcounts.
	pub(super) count: BitRefCounts<R>,
	/// The bits.
	pub(super) slice: BitSlice<O, T>,
}

/** A pointer to a ref-counted bit-slice allocation.

The bit value of this structure is always the descriptor of the contained
`BitSlice`. This grants it fast access to the data, but slows down access to the
refcounts slightly.
**/
#[repr(transparent)]
#[derive(Debug)]
pub(super) struct BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// The descriptor of the contained `BitSlice` region.
	///
	/// The allocation’s `BitRefCounts` exist immediately lower than
	/// `ptr.address()` in memory.
	pub(super) ptr: BitSpan<Mut, O, T>,
	/// Semantically, the handle has ownership stakes in an allocated box.
	pub(super) _rc: PhantomData<BitRefBox<R, O, T>>,
}

impl<R, O, T> BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Allocates a new buffer and fills it with the contents of a `BitSlice`.
	///
	/// # Parameters
	///
	/// - `bits`: A source `BitSlice`, used to allocate and fill a new buffer.
	///
	/// # Returns
	///
	/// A handle to a newly-allocated and initialized buffer.
	///
	/// The buffer is initialized with 1 strong count, 1 weak count, and the
	/// exact contents of `bits`.
	pub(super) fn alloc(bits: &BitSlice<O, T>) -> Self {
		let mut bitspan = bits.as_bitspan();
		let elts = bitspan.elements();
		let (ratio, words) = elts_to_words::<T::Mem>(elts);

		let mut alloc = Vec::with_capacity(2 + words);
		alloc.push(1);
		alloc.push(1);
		alloc.resize(2 + words, 0usize);
		let alloc = alloc.into_boxed_slice().pipe(Box::leak);

		let ptr = alloc[2 ..].as_mut_ptr().cast::<T::Mem>();
		let len = alloc[2 ..].len() * ratio;
		debug_assert!(
			len >= elts,
			"Failed to allocate enough space for {} elements",
			elts
		);
		let mut src = bits.domain();
		//  TODO(myrrlyn): Replace with memcpy
		for (to, from) in unsafe { slice::from_raw_parts_mut(ptr, len) }
			.iter_mut()
			.zip(src.by_ref())
		{
			*to = from;
		}
		debug_assert!(
			src.next().is_none(),
			"Failed to copy the entire source `BitSlice` into the \
			 `BitRefHandle` buffer"
		);

		unsafe {
			bitspan.set_address(ptr as *const _);
		}
		bitspan.cast::<T>().to_bitslice_ptr().pipe(Self::from_raw)
	}

	/// Deällocates the buffer to which this handle points.
	pub(super) fn dealloc(&mut self) {
		let addr = self.get_counters() as *const _ as *const usize;
		let elts = self.ptr.elements();
		let (_, words) = elts_to_words::<T::Mem>(elts);

		unsafe {
			let slice = slice::from_raw_parts_mut(addr as *mut usize, 2 + words);
			let boxed = Box::from_raw(slice);
			drop(boxed);
		};
	}

	/// Produces a `BitRefHandle` from a `BitSlice` pointer.
	#[inline]
	pub(super) fn from_raw(ptr: *const BitSlice<O, T>) -> Self {
		Self {
			ptr: BitSpan::from_bitslice_ptr_mut(ptr as *mut _),
			_rc: PhantomData,
		}
	}

	/// Gets access to the refcount metadata block.
	pub(super) fn get_counters(&self) -> &BitRefCounts<R> {
		let data_ptr = self.ptr.address().to_const();
		let bump = data_ptr.align_offset(mem::align_of::<usize>());
		let next_word = unsafe { data_ptr.add(bump).cast::<usize>() };
		let base_ptr = unsafe { next_word.sub(2).sub((bump > 0) as usize) };
		unsafe { &*(base_ptr.cast()) }
	}
}

impl<R, O, T> Clone for BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		*self
	}
}

impl<R, O, T> Eq for BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}

impl<R, O, T> PartialEq<Self> for BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		self.ptr == other.ptr
	}
}

impl<R, O, T> Copy for BitRefHandle<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}

/// Computes the `N` in `[usize; N]` required to hold `elts` elements of `T`.
///
/// # Type Parameters
///
/// - `T`: Some integer primitive not wider than `usize`
///
/// # Parameters
///
/// - `elts`: The number of elements `T` in the `[T]` being transformed to
///   `[usize]`
///
/// # Returns
///
/// - `.0`: The number of elements `T` in a `usize`
/// - `.1`: The number of `usize`s needed to hold `elts` elements of type `T`.
const fn elts_to_words<T>(elts: usize) -> (usize, usize) {
	let ratio = mem::size_of::<usize>() / mem::size_of::<T>();
	(ratio, elts / ratio + (elts % ratio != 0) as usize)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn alloc_size() {
		let (_, words) = elts_to_words::<u8>(4);
		assert_eq!(words, 1);
	}
}
