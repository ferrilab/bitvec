//! Okay, this immutable iterator doesn't use any `Access` types, and thus could not be used
//! on any element with possible mutable access at the same time (or could, but it's a subtle UB).
//! It could be used without UB only with unaliased memory, and due to this, `.iter()` should produce
//! a group of `(AliasedIter, UnAliasedIter, AliasedIter)` or use AliasedIter for every `.next()`.

// This should be deleted when all unsafe blocks are used or deleted.
#![allow(unused_unsafe)]

#[cfg(feature = "std")]
use std::{
	iter::{
		Chain, DoubleEndedIterator, ExactSizeIterator, FusedIterator, Iterator,
	},
	marker::PhantomData,
	mem,
	ptr::NonNull,
};

#[cfg(not(feature = "std"))]
use core::{
	iter::{
		Chain, DoubleEndedIterator, ExactSizeIterator, FusedIterator, Iterator,
	},
	marker::PhantomData,
	mem,
	ptr::NonNull,
};

use crate::{
	access::BitAccess,
	index::{BitIdx, BitSel},
	mem::BitMemory,
	order::BitOrder,
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
};

macro_rules! unchecked_add {
	($x:expr, $y:expr) => {{
		$x + $y
		}};
}

macro_rules! unchecked_sub {
	($x:expr, $y:expr) => {{
		$x - $y
		}};
}

/// Immutable bitslice iterator
///
/// This struct is created by the [`iter`] method on [bitslices].
///
/// [`iter`]: todo!()
/// [bitslices]: todo!()
pub struct Iter<'a, T: 'a + BitMemory, O> {
	ptr: NonNull<T>,
	end: *const T,
	// Bit masks with only one bit set. Those are never zero.
	bit_ptr: BitSel<T>,
	bit_end: BitSel<T>,

	_marker: PhantomData<&'a T>,
	_order: PhantomData<O>,
}

// NonNull<T>.as_ptr() produces `*mut T`, but `$self.end` is `*const T`.
macro_rules! ptrs_eq {
	($self:ident) => {{
		$self.ptr.as_ptr() as *const _ == $self.end
		}};
}

macro_rules! bitptrs_eq {
	($self:ident) => {{
		$self.bit_ptr == $self.bit_end
		}};
}

macro_rules! is_empty {
	($self:ident) => {{
		ptrs_eq!($self) && bitptrs_eq!($self)
		}};
}

// As with slice iterators, emptyness check takes less time, then getting length.
macro_rules! len {
	($self:ident) => {{
		let start = $self.ptr.as_ptr();
		// We know that `start <= end`, so can do better than `offset_from`,
		// which needs to deal in signed.  By setting appropriate flags here
		// we can tell LLVM this, which helps it remove bounds checks.
		// But unlike slice iterator, we don't need to divide the result by
		// the size of item; length in bytes is enough to calculate length in bits./
		// SAFETY: By the type invariant, `start <= end`
		let bytes_len: usize =
			unsafe { unchecked_sub!($self.end as usize, start as usize) };
		// Since length in those bitslices has hard cap at `usize::MAX / 8`
		// for _bits_ (thus length in bytes is capped at `usize::MAX / 8 / 8`)
		// not only `bytes_len * 8` could never overflow,
		// but `bits_len + cttz(bit_end)` could not overflow too.
		let bits_len = bytes_len << 3; // just fancy multiple by 8
		unsafe {
			// Addition safety guarantees are described three lines higher.
			let plus_rear: usize = unchecked_add!(
				bits_len,
				*O::idx_from_sel($self.bit_end) as usize
			);
			// SAFETY: `bit_end` is always >= `bit_ptr` if pointers are equal
			// by the type invariant.
			// If pointers aren't eq, `bits_len` is always bigger than `cttz(bit_ptr)`;
			// and so `plus_rear` is always >= `bits_len`.
			unchecked_sub!(plus_rear, *O::idx_from_sel($self.bit_ptr) as usize)
			}
		}};
}

// Shifts `bit_ptr` to the left by one and returns the bit at old position as bool.
// It is not unsafe by itself, but when called onto `bit_ptr` with only last bit set,
// it *could* wreck havoc.
macro_rules! next_bit_unchecked {
	($self:ident, $store:expr) => {{
		let old = $self.bit_ptr & $store != 0;
		$self.bit_ptr <<= 1;
		old
		}};
}

// Rotates `bit_end` to the right by one and returns the bit at new position as bool.
// It is the best solution I could come up with.
macro_rules! next_back_bit_unchecked {
	($self:ident, $store:expr, $t:ty) => {{
		// $self.bit_end = $self.bit_end.rotate_right(1);
		$self.bit_end = O::rot_backward($self.bit_end, 1);
		*$self.bit_end & $store != <$t>::ZERO
		}};
}

// // Offsets `ptr` pointer by 1 and sets `bit_ptr` to the FIRST_BIT.
// No more. Now this rotates too and need no setting.
macro_rules! forward_ptr_unchecked {
	($self:ident) => {{
		// $self.bit_ptr = <$t as BitMemory>::ONE;
		$self.ptr = NonNull::new_unchecked($self.ptr.as_ptr().offset(1));
		}};
}

// Offsets `end` pointer by -1. Yes, that's all.
// That's 'cuz `bit_end` rotates, not shifts.
macro_rules! backward_end_unchecked {
	($self:ident) => {{
		$self.end = $self.end.offset(-1);
		}};
}

impl<'a, T: BitMemory, O: BitOrder> Iter<'a, T, O> {
	// /// Number of bits in the `$store_type`. Very useful for many bit operations.
	// const BITS: u8 = mem::size_of::<T>() as u8 * 8;

	/// Constant with only last bit set.
	///
	/// It could've been simple `1.rotate_right(1)`,
	/// but stabilized version can't infer type.
	///
	/// This could never overflow when used with numeric primitives,
	/// because `T` could always hold `size_of::<Self>() * 8`.
	/// This could underflow with ZST, but ZSTs don't work as bitstores.
	// const LAST_BIT: T = T::ONE << (Self::BITS - 1);
	// const LAST_BIT: T = T::ONE << T::MASK;
	// Ffuuuuuu... I can't do this without intri.
	// const LAST_BIT: T = intrinsics::bitreverse(T::ONE);

	// /// Returns true if the iterator is empty. This is faster than `[`len()`] == 0`
	// ///
	// /// [`len()`]: https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html#method.len
	// #[inline]
	// pub fn is_empty(&self) -> bool {
	// 	is_empty!(self)
	// }

	#[inline]
	fn start_bit() -> BitSel<T> {
		O::at(unsafe { BitIdx::new_unchecked(0) }).select()
	}

	#[inline]
	fn last_bit() -> BitSel<T> {
		O::at(unsafe { BitIdx::new_unchecked(T::BITS - 1) }).select()
	}
}

impl<T: BitMemory, O: BitOrder> ExactSizeIterator for Iter<'_, T, O> {
	#[inline]
	fn len(&self) -> usize {
		len!(self)
	}

	// // nightly-only feature
	// #[inline]
	// fn is_empty(&self) -> bool {
	// 	is_empty!(self)
	// }
}

impl<'a, T: BitMemory, O: BitOrder> Iterator for Iter<'a, T, O> {
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		if is_empty!(self) {
			None
		} else {
			let old = unsafe {
				let old = (*self.ptr.as_ptr() & *self.bit_ptr) != T::ZERO;

				if self.bit_ptr == Self::last_bit() {
					forward_ptr_unchecked!(self);
				} else {
					// self.bit_ptr <<= 1;
					self.bit_ptr = O::rot_forward(self.bit_ptr, 1);
				}
				old
			};

			Some(old)
		}
	}

	#[inline]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let exact = len!(self);
		(exact, Some(exact))
	}

	#[inline]
	fn count(self) -> usize {
		len!(self)
	}

	#[inline]
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= len!(self) {
			// This iterator is now empty.
			unsafe {
				// End can't be 0 if T isn't ZST because ptr isn't 0 and end >= ptr
				self.ptr = NonNull::new_unchecked(self.end as *mut T);
				self.bit_ptr = self.bit_end;
			}
			return None;
		}
		// We are in bounds.
		//
		// `n` shows bits, not bytes, thus pointer should be moved by
		// `n / (size_of::<$store_type>() * 8)`
		// and bitmask should be rotated by `n & (BITS - 1)`, because
		// any number over those bits would simply do full circle.
		// How funny, that `BITS` is `(size_of::<$store_type>() * 8)`!
		unsafe {
			self.ptr = NonNull::new_unchecked(
				self.ptr.as_ptr().add(n / T::BITS as usize),
			);
		}
		self.bit_ptr =
			O::rot_forward(self.bit_ptr, (n & (T::BITS as usize - 1)) as u32);
		// Now pointers are set, time to call `next()` without emptyness check.
		let bit = unsafe {
			let old = (*self.ptr.as_ptr() & *self.bit_ptr) != T::ZERO;

			if self.bit_ptr == Self::last_bit() {
				forward_ptr_unchecked!(self);
			} else {
				// self.bit_ptr <<= 1;
				self.bit_ptr = O::rot_forward(self.bit_ptr, 1);
			}
			old
		};

		Some(bit)
	}

	#[inline]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<'a, T: BitMemory, O: BitOrder> DoubleEndedIterator for Iter<'a, T, O> {
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		if is_empty!(self) {
			return None;
		} else {
			if self.bit_end == Self::start_bit() {
				unsafe {
					backward_end_unchecked!(self);
				}
			}

			unsafe { Some(next_back_bit_unchecked!(self, *self.end, T)) }
		}
	}

	#[inline]
	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		if n >= len!(self) {
			// This iterator is now empty.
			self.end = self.ptr.as_ptr();
			self.bit_end = self.bit_ptr;
			return None;
		}
		// We are in bounds.
		//
		// `n` shows bits, not bytes, thus pointer should be moved by
		// `n / (size_of::<$store_type>() * 8)`
		// and bitmask should be rotated by `n & (BITS - 1)`, because
		// any number over those bits would simply do full circle.
		// How funny, that `BITS` is `(size_of::<$store_type>() * 8)`!
		//
		// SAFETY: `n` is usize, `BITS` >= 8, `usize / 8` is always less
		// than isize::MAX.
		self.end =
			unsafe { self.end.offset(-((n / T::BITS as usize) as isize)) };
		self.bit_end =
			O::rot_backward(self.bit_end, (n & (T::BITS as usize - 1)) as u32);
		// Now pointers are set, time to call `next()` without emptyness check.
		let bit = unsafe {
			if self.bit_end == Self::start_bit() {
				backward_end_unchecked!(self);
			}
			next_back_bit_unchecked!(self, *self.end, T)

			// (*self.end & self.bit_end) != 0
		};

		Some(bit)
	}
}

impl<T: BitMemory, O: BitOrder> FusedIterator for Iter<'_, T, O> {}

/*
/// Builder function for new iter.
pub fn new_iter<'a, T: BitStore + BitMemory, O: BitOrder>(
	s: &'a BitSlice<O, T>,
) -> Chain<Chain<LilIter<'a, T, O>, Iter<'a, T, O>>, LilIter<'a, T, O>> {
	// Little helper function.
	fn big_iter<'a, T: BitStore + BitMemory, O: BitOrder>(
		ptr: NonNull<T>,
		end: *const T,
		bit_ptr: BitSel<T>,
		bit_end: BitSel<T>,
	) -> Iter<'a, T, O> {
		Iter {
			ptr,
			end,

			bit_ptr,
			bit_end,

			_marker: PhantomData,
			_order: PhantomData,
		}
	}

	// Little helper function.
	fn lil_iter<'a, T: BitStore + BitMemory, O: BitOrder>(
		start: BitSel<T>,
		end: BitSel<T>,
		element: T,
	) -> LilIter<'a, T, O> {
		LilIter {
			start,
			end,
			element,
			_marker: PhantomData,
			_order: PhantomData,
		}
	}

	let (mut ptr_to_first_element, head_idx, mut len_bits) =
		BitPtr::from_bitslice(s).raw_parts();

	let zero = BitIdx::ZERO;
	let head_iter = if head_idx != zero {
		if len_bits < (T::BITS - *head_idx) as usize {
			// then there's only one element...
			let iter =
				lil_iter(head_idx.select(), *head_idx + len_bits as _, unsafe {
					*(ptr_to_first_element.a())
				});

			// ... and it gets returned.
			return iter
				.chain(big_iter(
					NonNull::new_unchecked(1 as _),
					1 as _,
					Iter::start_bit(),
					Iter::start_bit(),
				))
				.chain(lil_iter(Iter::start_bit(), Iter::start_bit(), T::ZERO));
		} else {
			let iter = lil_iter(head_idx.select(), Iter::start_bit(), unsafe {
				*(ptr_to_first_element.a())
			});
			ptr_to_first_element =
				crate::pointer::Address::from(ptr_to_first_element.r().add(1));
			len_bits -= (T::BITS - (*head_idx + 1)) as usize;

			iter
		}
	} else {
		// If index is 0, the first element is a part of middle iter or last iter,
		// so head iter is empty.
		lil_iter(Iter::start_bit(), Iter::start_bit(), T::ZERO)
	};

	let tail_ptr = crate::pointer::Address::from(
		ptr_to_first_element.r().add(len_bits / T::BITS as _),
	);
	let middle_iter = big_iter(
		unsafe { NonNull::new_unchecked(ptr_to_first_element.w()) },
		tail_ptr.r(),
		Iter::start_bit(),
		Iter::start_bit(),
	);

	let tail_iter = lil_iter(
		Iter::start_bit(),
		BitIdx::new_unchecked(len_bits as _ % T::BITS).select(),
		*tail_ptr.a(),
	);

	head_iter.chain(middle_iter).chain(tail_iter)
}
*/

/// Little iterator over one aliased element.
///
/// It could be merged into big Iter, but `Chain<LilIter, Iter>` allows
/// effective folding in stable, because stdlib can do what others can't. /
/// And since this thing iterates over immutable bitslice, it just copies
/// the element, cuz this element should not change while iterator is alive.
/// If the element changes, that's UB, and we can do anything in this case.
struct LilIter<'a, T: 'a + BitMemory, O> {
	start: BitSel<T>,
	end: BitSel<T>,

	element: T,

	_marker: PhantomData<&'a T>,
	_order: PhantomData<O>,
}

macro_rules! lil_is_empty {
	($self:ident) => {{
		*$self.start == *$self.end
		}};
}

impl<'a, T: BitMemory, O: BitOrder> ExactSizeIterator
	for LilIter<'a, T, O>
{
	#[inline]
	fn len(&self) -> usize {
		unchecked_sub!(*O::idx_from_sel(self.end), *O::idx_from_sel(self.start))
			as usize
	}
}

impl<'a, T: BitMemory, O: BitOrder> Iterator for LilIter<'a, T, O> {
	type Item = bool;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		if lil_is_empty!(self) {
			None
		} else {
			let old = {
				let old = *self.start & self.element != T::ZERO;
				self.start = O::rot_forward(self.start, 1);
				old
			};
			Some(old)
		}
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn new_iter() {
		assert_eq!(1, 1);
	}
}