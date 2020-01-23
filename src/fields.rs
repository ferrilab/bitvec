/*! Parallel bitfield access.

This module provides parallel, multiple-bit, access to a `BitSlice`. This
functionality permits the use of `BitSlice` as a library-level implementation of
the bitfield language feature found in C and C++.

The `BitField` trait is not sealed against client implementation, as there is no
useful way to automatically use a `Cursor` implementation to provide a universal
behavior. As such, the trait has some requirements that the compiler cannot
enforce for client implementations.

# Batch Behavior

The purpose of this trait is to provide access to arbitrary bit regions as if
they were an ordinary memory location. As such, it is important for
implementations of this trait to provide shift/mask register transfer behavior
where possible, for as wide a span as possible in each action. Implementations
of this trait should *not* use bit-by-bit iteration.

# Register Bit Order Preservation

As a default assumption – user orderings *may* violate this, but *should* not –
each element of slice memory used to store part of a value should not reorder
the value bits. Transfer between slice memory and a CPU register should solely
be an ordinary value load or store between memory and the register, and a
shift/mask operation to select the part of the value that is live.

# Endianness

The `_le` and `_be` methods of `BitField` refer to the order in which
`T: BitStore` elements of the slice are assigned significance when containing
fragments of a stored data value. Within any `T` element, the order of its
constituent bytes is *not* governed by the `BitField` trait method.

The provided `BitOrder` implementors `Lsb0` and `Msb0` use the local machine’s
byte ordering. Other cursors *may* implement ordering of bytes within `T`
elements differently, for instance by calling `.to_be_bytes` before store and
`from_be_bytes` after load,
!*/

use crate::{
	access::BitAccess,
	order::{
		Lsb0,
		Msb0,
	},
	slice::BitSlice,
	store::BitStore,
};

use core::{
	cmp,
	mem,
	ptr,
};

use either::Either;

#[cfg(feature = "alloc")]
use crate::{
	boxed::BitBox,
	order::BitOrder,
	vec::BitVec,
};

/** Permit a specific `BitSlice` to be used for C-style bitfield access.

Orders that permit batched access to regions of memory are enabled to load data
from a `BitSlice` and store data to a `BitSlice` with faster behavior than the
default bit-by-bit traversal.

This trait transfers data between a `BitSlice` and an element. The trait
functions always place the live bit region against the least significant bit
edge of the transfer element (return value for `load`, argument for `store`).

Implementations are encouraged to preserve in-memory bit ordering, so that call
sites can provide a value pattern that the user can clearly see matches what
they expect for memory ordering. These methods merely move data from a fixed
location in an element to a variable location in the slice.

Methods should be called as `bits[start .. end].load_or_store()`, where the
range subslice selects up to but no more than the `U::BITS` element width.
**/
pub trait BitField {
	/// Load the sequence of bits from `self` into the least-significant bits of
	/// an element.
	///
	/// This can load any fundamental type which implements `BitStore`. Other
	/// Rust fundamental types which do not implement it must be recast
	/// appropriately by the user.
	///
	/// The default implementation of this function calls [`load_le`] on
	/// little-endian byte-ordered CPUs, and [`load_be`] on big-endian
	/// byte-ordered CPUs.
	///
	/// # Parameters
	///
	/// - `&self`: A read reference to some bits in memory. This slice must be
	///   trimmed to have a width no more than the `U::BITS` width of the type
	///   being loaded. This can be accomplished with range indexing on a larger
	///   slice.
	///
	/// # Returns
	///
	/// A `U` value whose least `self.len()` significant bits are filled with
	/// the bits of `self`.
	///
	/// # Panics
	///
	/// If `self` is empty, or wider than a single `U` element, this panics.
	///
	/// [`load_be`]: #tymethod.load_be
	/// [`load_le`]: #tymethod.load_le
	fn load<U>(&self) -> U
	where U: BitStore {
		#[cfg(target_endian = "little")]
		return self.load_le();

		#[cfg(target_endian = "big")]
		return self.load_be();
	}

	/// Load from `self`, using little-endian element ordering.
	///
	/// This function interprets a multi-element slice as having its least
	/// significant chunk in the low memory address, and its most significant
	/// chunk in the high memory address. Each element `T` is still interpreted
	/// from individual bytes according to the local CPU ordering.
	///
	/// # Parameters
	///
	/// - `&self`: A read reference to some bits in memory. This slice must be
	///   trimmed to have a width no more than the `U::BITS` width of the type
	///   being loaded. This can be accomplished with range indexing on a larger
	///   slice.
	///
	/// # Returns
	///
	/// A `U` value whose least `self.len()` significant bits are filled with
	/// the bits of `self`. If `self` spans multiple `T` elements, then the
	/// lowest-address `T` is interpreted as containing the least significant
	/// bits of the `U` return value, and the highest-address `T` is interpreted
	/// as containing its most significant bits.
	///
	/// # Panics
	///
	/// If `self` is empty, or wider than a single `U` element, this panics.
	fn load_le<U>(&self) -> U
	where U: BitStore;

	/// Load from `self`, using big-endian element ordering.
	///
	/// This function interprets a multi-element slice as having its most
	/// significant chunk in the low memory address, and its least significant
	/// chunk in the high memory address. Each element `T` is still interpreted
	/// from individual bytes according to the local CPU ordering.
	///
	/// # Parameters
	///
	/// - `&self`: A read reference to some bits in memory. This slice must be
	///   trimmed to have a width no more than the `U::BITS` width of the type
	///   being loaded. This can be accomplished with range indexing on a larger
	///   slice.
	///
	/// # Returns
	///
	/// A `U` value whose least `self.len()` significant bits are filled with
	/// the bits of `self`. If `self` spans multiple `T` elements, then the
	/// lowest-address `T` is interpreted as containing the most significant
	/// bits of the `U` return value, and the highest-address `T` is interpreted
	/// as containing its least significant bits.
	fn load_be<U>(&self) -> U
	where U: BitStore;

	/// Stores a sequence of bits from the user into the domain of `self`.
	///
	/// This can store any fundamental type which implements `BitStore`. Other
	/// Rust fundamental types which do not implement it must be recast
	/// appropriately by the user.
	///
	/// The default implementation of this function calls [`store_le`] on
	/// little-endian byte-ordered CPUs, and [`store_be`] on big-endian
	/// byte-ordered CPUs.
	///
	/// # Parameters
	///
	/// - `&mut self`: A write reference to some bits in memory. This slice must
	///   be trimmed to have a width no more than the `U::BITS` width of the
	///   type being stored. This can be accomplished with range indexing on a
	///   larger slice.
	/// - `value`: A value, whose `self.len()` least significant bits will be
	///   stored into `self`.
	///
	/// # Behavior
	///
	/// The `self.len()` least significant bits of `value` are written into the
	/// domain of `self`.
	///
	/// # Panics
	///
	/// If `self` is empty, or wider than a single `U` element, this panics.
	///
	/// [`store_be`]: #tymethod.store_be
	/// [`store_le`]: #tymethod.store_le
	fn store<U>(&mut self, value: U)
	where U: BitStore {
		#[cfg(target_endian = "little")]
		self.store_le(value);

		#[cfg(target_endian = "big")]
		self.store_be(value);
	}

	/// Store into `self`, using little-endian element ordering.
	///
	/// This function interprets a multi-element slice as having its least
	/// significant chunk in the low memory address, and its most significant
	/// chunk in the high memory address. Each element `T` is still interpreted
	/// from individual bytes according to the local CPU ordering.
	///
	/// # Parameters
	///
	/// - `&mut self`: A write reference to some bits in memory. This slice must
	///   be trimmed to have a width no more than the `U::BITS` width of the
	///   type being stored. This can be accomplished with range indexing on a
	///   larger slice.
	/// - `value`: A value, whose `self.len()` least significant bits will be
	///   stored into `self`.
	///
	/// # Behavior
	///
	/// The `self.len()` least significant bits of `value` are written into the
	/// domain of `self`. If `self` spans multiple `T` elements, then the
	/// lowest-address `T` is interpreted as containing the least significant
	/// bits of the `U` return value, and the highest-address `T` is interpreted
	/// as containing its most significant bits.
	///
	/// # Panics
	///
	/// If `self` is empty, or wider than a single `U` element, this panics.
	fn store_le<U>(&mut self, value: U)
	where U: BitStore;

	/// Store into `self`, using big-endian element ordering.
	///
	/// This function interprets a multi-element slice as having its most
	/// significant chunk in the low memory address, and its least significant
	/// chunk in the high memory address. Each element `T` is still interpreted
	/// from individual bytes according to the local CPU ordering.
	///
	/// # Parameters
	///
	/// - `&mut self`: A write reference to some bits in memory. This slice must
	///   be trimmed to have a width no more than the `U::BITS` width of the
	///   type being stored. This can be accomplished with range indexing on a
	///   larger slice.
	/// - `value`: A value, whose `self.len()` least significant bits will be
	///   stored into `self`.
	///
	/// # Behavior
	///
	/// The `self.len()` least significant bits of `value` are written into the
	/// domain of `self`. If `self` spans multiple `T` elements, then the
	/// lowest-address `T` is interpreted as containing the most significant
	/// bits of the `U` return value, and the highest-address `T` is interpreted
	/// as containing its least significant bits.
	///
	/// # Panics
	///
	/// If `self` is empty, or wider than a single `U` element, this panics.
	fn store_be<U>(&mut self, value: U)
	where U: BitStore;
}

impl<T> BitField for BitSlice<Lsb0, T>
where T: BitStore {
	fn load_le<U>(&self) -> U
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot load {} bits from a {}-bit region", U::BITS, len);
		}

		match self.bitptr().domain().splat() {
			/* The live bits are in the interior of a single element.

			This path only needs to load the element, shift it right by the
			distance from LSedge to the live region, and mask it for the length
			of `self`.
			*/
			Either::Right((head, elt, _)) =>
				resize((elt.load() >> *head) & mask_for::<T>(len)),
			/* The live region touches at least one element edge.

			This block reads chunks from the slice memory into an accumulator,
			from the most-significant chunk to the least-significant. Each read
			must collect the live section of the chunk into a temporary, then
			shift the accumulator left by the chunk’s bit width, then write the
			temporary into the newly-vacated least significant bits of the
			accumulator.
			*/
			Either::Left((head, body, tail)) => {
				let mut accum = 0usize;

				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  Load, mask, resize, and store. No other data is present.
					accum = resize(tail.load() & mask_for::<T>(*t as usize));
				}
				//  Read the body elements, from high address to low, into the
				//  accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the live region’s distance from the LSedge.
					let lsedge = *h;
					//  Find the region width (MSedge to head).
					let width = T::BITS - lsedge;
					//  Load the element, shift down to LSedge, and resize.
					let val: usize = resize(head.load() >> lsedge);
					accum <<= width;
					accum |= val;
				}

				resize(accum)
			},
		}
	}

	fn load_be<U>(&self) -> U
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot load {} bits from a {}-bit region", U::BITS, len);
		}

		match self.bitptr().domain().splat() {
			/* The live bits are in the interior of a single element.

			This path only needs to load the element, shift it right by the
			distance from LSedge to the live region, and mask it for the length
			of `self`.
			*/
			Either::Right((head, elt, _)) =>
				resize((elt.load() >> *head) & mask_for::<T>(len)),
			/* The live region touches at least one element edge.

			This block reads chunks from the slice memory into an accumulator,
			from the most-significant chunk to the least-significant. Each read
			must collect the live section of the chunk into a temporary, then
			shift the accumulator left by the chunk’s width, then write the
			temporary into the newly-vacated least significant bits of the
			accumulator.
			*/
			Either::Left((head, body, tail)) => {
				let mut accum = 0usize;

				//  If the head exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Load, move, resize, and store. No other data is present.
					accum = resize(head.load() >> *h);
				}
				//  Read the body elements, from low address to high, into the
				//  accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  Get the live region’s width.
					let width = *t as usize;
					//  Load, mask, and resize.
					let val: usize = resize(tail.load() & mask_for::<T>(width));
					//  Shift the accumulator by the live width, and store.
					accum <<= width;
					accum |= val;
				}

				resize(accum)
			},
		}
	}

	fn store_le<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);
		}

		let value = value & mask_for(len);
		match self.bitptr().domain().splat() {
			/* The live region is in the interior of a single element.

			The `value` is shifted left by the region’s distance from the
			LSedge, then written directly into place.
			*/
			Either::Right((head, elt, _)) => {
				//  Get the region’s distance from the LSedge.
				let lsedge = *head;
				//  Erase the live region.
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				//  Shift the value to fit the region, and write.
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			/* The live region touches at least one element edge.

			This block writes chunks from the value into slice memory, from the
			least-significant chunk to the most-significant. Each write moves
			a slice chunk’s width of bits from the LSedge of the value into
			memory, then shifts the value right by that width.
			*/
			Either::Left((head, body, tail)) => {
				let mut value: usize = resize(value);

				//  If the head exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the region distance from the LSedge.
					let lsedge = *h;
					//  Find the region width (MSedge to head).
					let width = T::BITS - lsedge;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					head.clear_bits(T::TRUE >> width);
					//  Shift the snippet to fit the region, and write.
					head.set_bits(resize::<usize, T>(val) << lsedge);
					//  Discard the now-written bits from the value.
					value >>= width;
				}
				//  Write into the body elements, from low address to high, from
				//  the value.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  Get the region width.
					let width = *t;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					tail.clear_bits(T::TRUE << width);
					//  Write the snippet into the region.
					tail.set_bits(resize(val));
				}
			},
		}
	}

	fn store_be<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);
		}

		let value = value & mask_for(len);
		match self.bitptr().domain().splat() {
			/* The live region is in the interior of a single element.

			The `value` is shifted left by the region’s distance from the
			LSedge, then written directly into place.
			*/
			Either::Right((head, elt, _)) => {
				//  Get the region’s distance from the LSedge.
				let lsedge = *head;
				//  Erase the live region.
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				//  Shift the value to fit the region, and write.
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			Either::Left((head, body, tail)) => {
				let mut value: usize = resize(value);

				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  Get the region width.
					let width = *t;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					tail.clear_bits(T::TRUE << width);
					//  Write the snippet into the region.
					tail.set_bits(resize(val));
					//  Discard the now-written bits from the value.
					value >>= width;
				}
				//  Write into the body elements, from high address to low, from
				//  the value.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the head exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the region distance from the LSedge.
					let lsedge = *h;
					//  Find the region width (MSedge to head).
					let width = T::BITS - lsedge;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					head.clear_bits(T::TRUE >> width);
					//  Shift the snippet to fit the region, and write.
					head.set_bits(resize::<usize, T>(val) << lsedge);
				}
			},
		}
	}
}

impl<T> BitField for BitSlice<Msb0, T>
where T: BitStore {
	fn load_le<U>(&self) -> U
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot load {} bits from a {}-bit region", U::BITS, len);
		}

		match self.bitptr().domain().splat() {
			/* The live bits are in the interior of a single element.

			This path only needs to load the element, shift it right by the
			distance from LSedge to the live region, and mask it for the length
			of `self`.
			*/
			Either::Right((_, elt, tail)) =>
				resize((elt.load() >> (T::BITS - *tail)) & mask_for::<T>(len)),
			/* The live region touches at least one element edge.

			This block reads chunks from the slice memory into an accumulator,
			from the most-significant chunk to the least-significant. Each read
			must collect the live section of the chunk into a temporary, then
			shift the accumulator left by the chunk’s bit width, then write the
			temporary into the newly-vacated least significant bits of the
			accumulator.
			*/
			Either::Left((head, body, tail)) => {
				let mut accum = 0usize;

				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					//  Find the live region’s distance from the LSedge.
					let lsedge = T::BITS - *t;
					//  Load, move, resize, and store. No other data is present.
					accum = resize(tail.load() >> lsedge);
				}
				//  Read the body elements, from high address to low, into the
				//  accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					//  Find the region width (head to LSedge).
					let width = (T::BITS - *h) as usize;
					//  Load the element, mask, and resize.
					let val: usize = resize(head.load() & mask_for::<T>(width));
					accum <<= width;
					accum |= val;
				}

				resize(accum)
			},
		}
	}

	fn load_be<U>(&self) -> U
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot load {} bits from a {}-bit region", U::BITS, len);
		}

		match self.bitptr().domain().splat() {
			/* The live bits are in the interior of a single element.

			This path only needs to load the element, shift it right by the
			distance from LSedge to the live region, and mask it for the length
			of `self`.
			*/
			Either::Right((_, elt, tail)) =>
				resize((elt.load() >> (T::BITS - *tail)) & mask_for::<T>(len)),
			/* The live region touches at least one element edge.

			This block reads chunks from the slice memory into an accumulator,
			from the most-significant chunk to the least-significant. Each read
			must collect the live section of the chunk into a temporary, then
			shift the accumulator left by the chunk’s bit width, then write the
			temporary into the newly-vacated least significant bits of the
			accumulator.
			*/
			Either::Left((head, body, tail)) => {
				let mut accum = 0usize;

				//  If the head exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					//  Find the region width (head to LSedge).
					let width = T::BITS - *h;
					//  Load, mask, resize, and store. No other data is present.
					accum = resize(head.load() & mask_for::<T>(width as usize));
				}
				//  Read the body elements, from low address to high, into the
				//  accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					//  Find the live region’s distance from LSedge.
					let lsedge = T::BITS - *t;
					//  Load the element, shift down to LSedge, and resize.
					let val: usize = resize(tail.load() >> lsedge);
					accum <<= *t;
					accum |= val;
				}

				resize(accum)
			},
		}
	}

	fn store_le<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);
		}

		let value = value & mask_for(len);
		match self.bitptr().domain().splat() {
			/* The live region is in the interior of a single element.

			The `value` is shifted left by the region’s distance from the
			LSedge, then written directly into place.
			*/
			Either::Right((_, elt, tail)) => {
				//  Get the region’s distance from the LSedge.
				let lsedge = T::BITS - *tail;
				//  Erase the live region.
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				//  Shift the value to fit the region, and write.
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			/* The live region touches at least one element edge.

			This block writes chunks from the value into slice memory, from the
			least-significant chunk to the most-significant. Each write moves a
			slice chunk’s width of bits from the LSedge of the value into
			memory, then shifts the value right by that width.
			*/
			Either::Left((head, body, tail)) => {
				let mut value: usize = resize(value);

				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					//  Get the region width (head to LSedge).
					let width = T::BITS - *h;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					head.clear_bits(T::TRUE << width);
					//  Write the snippet into the region.
					head.set_bits(resize(val));
					//  Discard the now-written bits from the value.
					value >>= width;
				}
				//  Write into the body elements, from low address to high, from
				//  the value.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					//  Get the region width.
					let width = *t;
					//  Find the region distance from the LSedge.
					let lsedge = T::BITS - width;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					tail.clear_bits(T::TRUE >> width);
					//  Shift the snippet to fit the region, and write.
					tail.set_bits(resize::<usize, T>(val) << lsedge);
				}
			},
		}
	}

	fn store_be<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);
		}

		let value = value & mask_for(len);
		match self.bitptr().domain().splat() {
			/* The live region is in the interior of a single element.

			The `value` is shifted left by the region’s distance from the
			LSedge, then written directly into place.
			*/
			Either::Right((_, elt, tail)) => {
				//  Get the region’s distance from the LSedge.
				let lsedge = T::BITS - *tail;
				//  Erase the live region.
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				//  Shift the value to fit the region, and write.
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			/* The live region touches at least one element edge.

			This block writes chunks from the value into slice memory, from the
			least-significant chunk to the most-significant. Each write moves a
			slice chunk’s width of bits from the LSedge of the value into
			memory, then shifts the value right by that width.
			*/
			Either::Left((head, body, tail)) => {
				let mut value: usize = resize(value);

				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					//  Get the region width (MSedge to tail).
					let width = *t;
					//  Find the region distance from the LSedge.
					let lsedge = T::BITS - width;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					tail.clear_bits(T::TRUE >> width);
					//  Shift the snippet to fit the region, and write.
					tail.set_bits(resize::<usize, T>(val) << lsedge);
					//  Discard the now-written bits from the value.
					value >>= width;
				}
				//  Write into the body elements, from high address to low, from
				//  the value.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the head exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					//  Find the region width.
					let width = T::BITS - *h;
					//  Take the region-width LSedge bits of the value.
					let val = value & mask_for::<usize>(width as usize);
					//  Erase the region.
					head.clear_bits(T::TRUE << width);
					//  Write the snippet into the region.
					head.set_bits(resize(val));
				}
			},
		}
	}
}

#[cfg(feature = "alloc")]
impl<O, T> BitField for BitBox<O, T>
where O: BitOrder, T: BitStore, BitSlice<O, T>: BitField {
	fn load_le<U>(&self) -> U
	where U: BitStore {
		self.as_bitslice().load_le()
	}

	fn load_be<U>(&self) -> U
	where U: BitStore {
		self.as_bitslice().load_be()
	}

	fn store_le<U>(&mut self, value: U)
	where U: BitStore {
		self.as_mut_bitslice().store_le(value)
	}

	fn store_be<U>(&mut self, value: U)
	where U: BitStore {
		self.as_mut_bitslice().store_be(value)
	}
}

#[cfg(feature = "alloc")]
impl<O, T> BitField for BitVec<O, T>
where O: BitOrder, T: BitStore, BitSlice<O, T>: BitField {
	fn load_le<U>(&self) -> U
	where U: BitStore {
		self.as_bitslice().load_le()
	}

	fn load_be<U>(&self) -> U
	where U: BitStore {
		self.as_bitslice().load_be()
	}

	fn store_le<U>(&mut self, value: U)
	where U: BitStore {
		self.as_mut_bitslice().store_le(value)
	}

	fn store_be<U>(&mut self, value: U)
	where U: BitStore {
		self.as_mut_bitslice().store_be(value)
	}
}

/** Safely computes an LS-edge bitmask for a value of some length.

The shift operators panic when the shift amount equals or exceeds the type
width, but this module must be able to produce a mask for exactly the type
width. This function correctly handles that case.

# Parameters

- `len`: The width in bits of the value stored in an element `T`.

# Type Parameters

- `T`: The element type for which the mask is computed.

# Returns

An LS-edge-aligned bitmask of `len` bits. All bits higher than the `len`th are
zero.
**/
#[inline]
fn mask_for<T>(len: usize) -> T
where T: BitStore {
	let len = len as u8;
	if len >= T::BITS {
		T::TRUE
	}
	else {
		!(T::TRUE << len)
	}
}

/** Resizes a value from one fundamental type to another.

This function uses `usize` as the intermediate type (as it is the largest
`BitStore` implementor on all supported targets), and either zero-extends or
truncates the source value to be valid as the destination type. This is
essentially a generic-aware version of the `as` operator.

# Parameters

- `value`: Any value to be resized.

# Type Parameters

- `T`: The source type of the value to be resized.
- `U`: The destination type to which the value will be resized.

# Returns

The result of transforming `value as U`. Where `U` is wider than `T`, this
zero-extends; where `U` is narrower, it truncates.
**/
fn resize<T, U>(value: T) -> U
where T: BitStore, U: BitStore {
	let mut out = U::FALSE;
	let bytes_t = mem::size_of::<T>();
	let bytes_u = mem::size_of::<U>();

	unsafe {
		/* On big-endian targets, the significant bytes of a value are in the
		high portion of its memory slot. Truncation reads only from the high
		bytes; extension writes only into the high bytes.

		Note: attributes are not currently supported on `if`-expressions, so
		this must use the form `if cfg!` instead. `cfg!` is a compile-time macro
		that expands to a constant `true` or `false` depending on the flag, so
		this has the net effect of becoming either `if true {} else {}` or
		`if false {} else {}`, eliminating the branch from actual codegen.
		*/
		if cfg!(target_endian = "big") {
			//  Truncate by reading the high bytes of `value` into `out`.
			if bytes_t > bytes_u {
				ptr::copy_nonoverlapping(
					(&value as *const T as *const u8).add(bytes_t - bytes_u),
					&mut out as *mut U as *mut u8,
					bytes_u,
				);
			}
			//  Extend by writing `value` into the high bytes of `out`.
			else {
				ptr::copy_nonoverlapping(
					&value as *const T as *const u8,
					(&mut out as *mut U as *mut u8).add(bytes_u - bytes_t),
					bytes_t,
				);
			}
		}
		/* On little-endian targets, the significant bytes of a value are in the
		low portion of its memory slot. Truncation and extension are both plain
		copies into the start of a zero-buffer, for the smaller width.
		*/
		else {
			ptr::copy_nonoverlapping(
				&value as *const T as *const u8,
				&mut out as *mut U as *mut u8,
				cmp::min(bytes_t, bytes_u),
			);
		}
	}

	out
}

#[allow(clippy::inconsistent_digit_grouping)]
#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn lsb0() {
		let mut bytes = [0u8; 16];
		let bytes = bytes.bits_mut::<Lsb0>();

		bytes[1 ..][.. 4].store_le(0x0Au8);
		assert_eq!(bytes[1 ..][.. 4].load_le::<u8>(), 0x0Au8);
		assert_eq!(bytes.as_slice()[0], 0b000_1010_0u8);

		bytes[1 ..][.. 4].store_be(0x05u8);
		assert_eq!(bytes[1 ..][.. 4].load_be::<u8>(), 0x05u8);
		assert_eq!(bytes.as_slice()[0], 0b000_0101_0u8);

		bytes[1 ..][.. 4].store_le(0u8);

		//  expected byte pattern: 0x34 0x12
		//  bits: 0011_0100 __01_0010
		//  idx:  7654 3210 fedc ba98
		let u16b = u16::from_ne_bytes(0x1234u16.to_le_bytes());
		bytes[5 ..][.. 14].store_le(u16b);
		assert_eq!(bytes[5 ..][.. 14].load_le::<u16>(), 0x1234u16);
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b100_00000, 0b010_0011_0, 0b00000_01_0],
			//  210          a98 7654 3          dc b
		);
		//  the load/store orderings only affect the order of elements, not of
		//  bits within the element.
		bytes[5 ..][.. 14].store_be(u16b);
		assert_eq!(bytes[5 ..][.. 14].load_be::<u16>(), 0x1234u16);
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b01_0_00000, 0b010_0011_0, 0b00000_100],
			//  dc b          a98 7654 3          210
		);

		let mut shorts = [0u16; 8];
		let shorts = shorts.bits_mut::<Lsb0>();

		shorts[3 ..][.. 12].store_le(0x0123u16);
		assert_eq!(shorts[3 ..][.. 12].load_le::<u16>(), 0x0123u16);
		assert_eq!(shorts.as_slice()[0], 0b0_0001_0010_0011_000u16);

		shorts[3 ..][.. 12].store_be(0x0123u16);
		assert_eq!(shorts[3 ..][.. 12].load_be::<u16>(), 0x0123u16);
		assert_eq!(shorts.as_slice()[0], 0b0_0001_0010_0011_000u16);

		let mut ints = [0u32; 4];
		let ints = ints.bits_mut::<Lsb0>();

		ints[1 ..][.. 28].store_le(0x0123_4567u32);
		assert_eq!(ints[1 ..][.. 28].load_le::<u32>(), 0x0123_4567u32);
		assert_eq!(ints.as_slice()[0], 0b000_0001_0010_0011_0100_0101_0110_0111_0u32);

		ints[1 ..][.. 28].store_be(0x0123_4567u32);
		assert_eq!(ints[1 ..][.. 28].load_be::<u32>(), 0x0123_4567u32);
		assert_eq!(ints.as_slice()[0], 0b000_0001_0010_0011_0100_0101_0110_0111_0u32);

		/*
		#[cfg(target_pointer_width = "64")] {

		let mut longs = [0u64; 2];
		let longs = longs.bits_mut::<Lsb0>();

		}
		*/
	}

	#[test]
	fn msb0() {
		let mut bytes = [0u8; 16];
		let bytes = bytes.bits_mut::<Msb0>();

		bytes[1 ..][.. 4].store_le(0x0Au8);
		assert_eq!(bytes[1 ..][.. 4].load_le::<u8>(), 0x0Au8);
		assert_eq!(bytes.as_slice()[0], 0b0_1010_000u8);

		bytes[1 ..][.. 4].store_be(0x05u8);
		assert_eq!(bytes[1 ..][.. 4].load_be::<u8>(), 0x05u8);
		assert_eq!(bytes.as_slice()[0], 0b0_0101_000u8);

		bytes[1 ..][.. 4].store_le(0u8);

		//  expected byte pattern: 0x34 0x12
		//  bits: 0011_0100 __01_0010
		//  idx:  7654 3210 fedc ba98
		let u16b = u16::from_ne_bytes(0x1234u16.to_le_bytes());
		bytes[5 ..][.. 14].store_le(u16b);
		assert_eq!(bytes[5 ..][.. 14].load_le::<u16>(), 0x1234u16);
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b00000_100, 0b010_0011_0, 0b01_0_00000],
			//        210    a98 7654 3    dc b
		);
		//  the load/store orderings only affect the order of elements, not of
		//  bits within the element.
		bytes[5 ..][.. 14].store_be(u16b);
		assert_eq!(bytes[5 ..][.. 14].load_be::<u16>(), 0x1234u16);
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b00000_01_0, 0b010_0011_0, 0b100_00000],
			//        dc b    a98 7654 3    210
		);

		let mut shorts = [0u16; 8];
		let shorts = shorts.bits_mut::<Msb0>();

		shorts[3 ..][.. 12].store_le(0x0123u16);
		assert_eq!(shorts[3 ..][.. 12].load_le::<u16>(), 0x0123u16);
		assert_eq!(shorts.as_slice()[0], 0b000_0001_0010_0011_0u16);

		shorts[3 ..][.. 12].store_be(0x0123u16);
		assert_eq!(shorts[3 ..][.. 12].load_be::<u16>(), 0x0123u16);
		assert_eq!(shorts.as_slice()[0], 0b000_0001_0010_0011_0u16);

		let mut ints = [0u32; 4];
		let ints = ints.bits_mut::<Msb0>();

		ints[1 ..][.. 28].store_le(0x0123_4567u32);
		assert_eq!(ints[1 ..][.. 28].load_le::<u32>(), 0x0123_4567u32);
		assert_eq!(ints.as_slice()[0], 0b0_0001_0010_0011_0100_0101_0110_0111_000u32);

		ints[1 ..][.. 28].store_be(0x0123_4567u32);
		assert_eq!(ints[1 ..][.. 28].load_be::<u32>(), 0x0123_4567u32);
		assert_eq!(ints.as_slice()[0], 0b0_0001_0010_0011_0100_0101_0110_0111_000u32);

		/*
		#[cfg(target_pointer_width = "64")] {

		let mut longs = [0u64; 2];
		let longs = longs.bits_mut::<Msb0>();

		}
		*/
	}
}

#[cfg(test)]
mod permutation_tests;
