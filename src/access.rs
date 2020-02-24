/*! Governs access to underlying memory.

`bitvec` allows the logical capability of a program to produce aliased
references to memory elements which may have contended mutation. While `bitvec`
operations are guaranteed to not observe mutation outside the logical borders of
their domains, the production of aliased mutating access to memory is still
undefined behavior in the compiler.

As such, the crate must never produce references, either shared or unique,
references to memory as the bare fundamental types. Instead, this module
translates references to `BitSlice` into references to shared-mutable types as
appropriate for the crate build configuration: either `Cell` in non-atomic
builds, or `AtomicT` in atomic builds.
!*/

use crate::{
	index::BitIdx,
	mem::BitMemory,
	order::BitOrder,
};

use core::{
	fmt::Debug,
	sync::atomic::Ordering,
};

use radium::Radium;

/** Access interface for shared/mutable memory access.

`&BitSlice` and `&mut BitSlice` contexts must route through their `Access`
associated type, which implements this trait, in order to perform *any* access
to underlying memory. This trait extends the `Radium` element-wise shared
mutable access with single-bit operations suited for use by `BitSlice`.
**/
pub trait BitAccess<M>: Debug + Radium<M> + Sized
where M: BitMemory
{
	/// Set a single bit in an element low.
	///
	/// `BitAccess::set` calls this when its `value` is `false`; it
	/// unconditionally writes a `0` bit into the electrical position that
	/// `place` controls according to the `BitOrder` parameter `O`.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation which translates `place` into a
	///   usable bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn clear_bit<O>(&self, place: BitIdx<M>)
	where O: BitOrder {
		self.fetch_and(!*O::select(place), Ordering::Relaxed);
	}

	/// Writes the low bits of the mask into the underlying element.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: Any value. The low bits of the mask will be written into
	///   `*self`; the high bits will preserve their value in `*self`.
	fn clear_bits(&self, mask: M) {
		self.fetch_and(mask, Ordering::Relaxed);
	}

	/// Set a single bit in an element high.
	///
	/// `BitAccess::set` calls this when its `value` is `true`; it
	/// unconditionally writes a `1` bit into the electrical position that
	/// `place` controls according to the `BitOrder` parameter `O`.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation which translates `place` into a
	///   usable bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn set_bit<O>(&self, place: BitIdx<M>)
	where O: BitOrder {
		self.fetch_or(*O::select(place), Ordering::Relaxed);
	}

	/// Writes the high bits of the mask into the underlying element.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mask`: Any value. The high bits of the mask will be written into
	///   `*self`; the low bits will preserve their value in `*self`.
	fn set_bits(&self, mask: M) {
		self.fetch_or(mask, Ordering::Relaxed);
	}

	/// Invert a single bit in an element.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation which translates `place` into a
	///   usable bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn invert_bit<O>(&self, place: BitIdx<M>)
	where O: BitOrder {
		self.fetch_xor(*O::select(place), Ordering::Relaxed);
	}

	/// Retrieve a single bit from an element.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation which translates `place` into a
	///   usable bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline]
	fn get<O>(&self, place: BitIdx<M>) -> bool
	where O: BitOrder {
		<Self as BitAccess<M>>::load(&self) & *O::select(place) != M::ZERO
	}

	/// Set a single bit in an element to some value.
	///
	/// # Type Parameters
	///
	/// - `O`: A `BitOrder` implementation which translates `place` into a
	///   usable bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	/// - `value`: The value to which the bit controlled by `place` shall be
	///   set.
	#[inline]
	fn set<O>(&self, place: BitIdx<M>, value: bool)
	where O: BitOrder {
		if value {
			self.set_bit::<O>(place);
		}
		else {
			self.clear_bit::<O>(place);
		}
	}

	/// Read a value out of a contended memory element and into a local scope.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	///
	/// # Returns
	///
	/// The value of `*self`. This value is only useful when access is
	/// uncontended by multiple `BitSlice` regions.
	fn load(&self) -> M {
		Radium::load(self, Ordering::Relaxed)
	}

	/// Stores a value into a contended memory element.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `value`: The new value to write into `*self`.
	fn store(&self, value: M) {
		Radium::store(self, value, Ordering::Relaxed)
	}

	/// Converts a slice of `BitAccess` to a mutable slice of `BitStore`.
	///
	/// # Safety
	///
	/// This can only be called on wholly owned, uncontended, regions.
	#[allow(clippy::mut_from_ref)] // I *am* the law, Clippy
	unsafe fn as_slice_mut(this: &[Self]) -> &mut [M] {
		&mut *(this as *const [Self] as *const [M] as *mut [M])
	}
}

impl<M, R> BitAccess<M> for R
where
	M: BitMemory,
	R: Debug + Radium<M>,
{
}
