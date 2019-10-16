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
	cursor::Cursor,
	indices::BitIdx,
	store::BitStore,
};

use core::sync::atomic::Ordering;

use radium::{
	Radium,
	marker::BitOps,
};

/** Access interface for shared/mutable memory access.

`&BitSlice` and `&mut BitSlice` contexts must route through their `Access`
associated type, which implements this trait, in order to perform *any* access
to underlying memory. This trait extends the `Radium` element-wise shared
mutable access with single-bit operations suited for use by `BitSlice`.
**/
pub trait BitAccess<T>: Radium<T>
where T: BitStore + BitOps {
	/// Set a single bit in an element low.
	///
	/// `BitAccess::set` calls this when its `value` is `false`; it
	/// unconditionally writes a `0` bit into the electrical position that
	/// `place` controls according to the `Cursor` parameter `C`.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation which translates `place` into a usable
	///   bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn clear_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor {
		self.fetch_and(!*C::mask(place), Ordering::Relaxed);
	}

	/// Set a single bit in an element high.
	///
	/// `BitAccess::set` calls this when its `value` is `true`; it
	/// unconditionally writes a `1` bit into the electrical position that
	/// `place` controls according to the `Cursor` parameter `C`.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation which translates `place` into a usable
	///   bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn set_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor {
		self.fetch_or(*C::mask(place), Ordering::Relaxed);
	}

	/// Invert a single bit in an element.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation which translates `place` into a usable
	///   bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline(always)]
	fn invert_bit<C>(&self, place: BitIdx<T>)
	where C: Cursor {
		self.fetch_xor(*C::mask(place), Ordering::Relaxed);
	}

	/// Retrieve a single bit from an element.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation which translates `place` into a usable
	///   bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	#[inline]
	fn get<C>(&self, place: BitIdx<T>) -> bool
	where C: Cursor {
		<Self as BitAccess<T>>::load(&self) & *C::mask(place) != T::bits(false)
	}

	/// Set a single bit in an element to some value.
	///
	/// # Type Parameters
	///
	/// - `C`: A `Cursor` implementation which translates `place` into a usable
	///   bit-mask.
	///
	/// # Parameters
	///
	/// - `&self`: A shared reference to underlying memory.
	/// - `place`: A semantic bit index in the `self` element.
	/// - `value`: The value to which the bit controlled by `place` shall be
	///   set.
	#[inline]
	fn set<C>(&self, place: BitIdx<T>, value: bool)
	where C: Cursor {
		if value {
			self.set_bit::<C>(place);
		}
		else {
			self.clear_bit::<C>(place);
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
	fn load(&self) -> T {
		Radium::load(self, Ordering::Relaxed)
	}
}

impl<T, R> BitAccess<T> for R
where T: BitStore + BitOps, R: Radium<T> {}
