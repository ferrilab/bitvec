/*! Parallel bitfield access.

This module provides parallel, multiple-bit, access to a `BitSlice`. This
functionality permits the use of `BitSlice` as a library-level implementation of
the bitfield language feature found in C and C++.
!*/

use crate::{
	access::BitAccess,
	cursor::{
		BigEndian,
		LittleEndian,
	},
	slice::BitSlice,
	store::BitStore,
};

use core::mem;

use either::Either;

/** Permit a specific `BitSlice` to be used for C-style bitfield access.

Cursors that permit batched access to regions of memory are enabled to load data
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
range subslice selects up to but no more than the `T::BITS` width.
**/
pub trait BitField<T>
where T: BitStore {
	/// Load the sequence of bits from `self` into the least-significant bits of
	/// an element.
	///
	/// This can load any fundamental type which implements `BitStore`. Other
	/// Rust fundamental types which do not implement it must be recast
	/// appropriately by the user.
	///
	/// # Parameters
	///
	/// - `&self`: A read reference to some bits in memory. This slice must be
	///   trimmed to have a width no more than the `U::BITS` width of the
	///   type being loaded. This can be accomplished with range indexing on a
	///   larger slice.
	///
	/// # Returns
	///
	/// If `self` has a length greater than zero, but not greater than the `U`
	/// element width `U::BITS`, then this returns an element whose least
	/// `self.len()` significant bits are filled with the bits of `self`.
	///
	/// If `self` is empty, or wider than a single element, this returns `None`.
	fn load<U>(&self) -> Option<U>
	where U: BitStore;

	/// Stores a sequence of bits from the user into the domain of `self`.
	///
	/// This can store any fundamental type which implements `BitStore`. Other
	/// Rust fundamental types which do not implement it must be recast
	/// appropriately by the user.
	///
	/// # Parameters
	///
	/// - `&mut self`: A write reference to some bits in memory. This slice must
	///   be trimmed to have a width no more than the `U::BITS` width of the
	///   type being stored. This can be accomplished with range indexing on a
	///   larger slice.
	///
	/// # Behavior
	///
	/// If `self` is the empty slice, or wider than an element, then this exits
	/// without effect. Otherwise, the `self.len()` least significant bits of
	/// `value` are written into the domain of `self`.
	fn store<U>(&mut self, value: U)
	where U: BitStore;
}

impl<T> BitField<T> for BitSlice<LittleEndian, T>
where T: BitStore {
	fn load<U>(&self) -> Option<U>
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			return None;
		}

		match self.bitptr().domain().splat() {
			//  The live bits are in the interior of a single element.
			Either::Right((head, elt, _)) => {
				//  Get the distance from the LSedge.
				let lsedge = *head;
				//  Load the value, shift it to LSedge, and mask.
				let val = (elt.load() >> lsedge) & mask_for::<T>(len);
				Some(resize(val))
			},
			Either::Left((head, body, tail)) => {
				/* Read chunks, from most-significant to least-significant, into
				this value. Each successive read must left-shift by the read
				amount, then write the chunk into the now-free least significant
				bits.
				*/
				let mut accum = 0u64;

				//  Debug counter. Strip once the implementation is correct.
				let mut rem = len;

				/* In little-endian byte-order architectures, the LSelement is
				at the low address and the MSelement is at the high address.
				Read from high addresses to low into the accumulator.
				*/
				#[cfg(target_endian = "little")] {

				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  The live bits are at the LSedge of the element.
					let width = *t as usize;
					let val = tail.load() & mask_for::<T>(width);
					accum = resize(val);
					rem -= width;
				}
				//  Read the body, from high to low, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: u64 = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
						rem -= T::BITS as usize;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the distance from the LSedge.
					let lsedge = *h;
					//  Get the live chunk width.
					let width = T::BITS - lsedge;
					let val: u64 = resize(head.load() >> lsedge);
					accum <<= width;
					accum |= val;
					rem -= width as usize;
				}

				}

				/* In big-endian byte-order architectures, the MSelement is at
				the low address and the LSelement is at the high address.
				Read from low addresses to high into the accumulator.
				*/
				#[cfg(target_endian = "big")] {

				//  If the head exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the distance from the LSedge.
					let lsedge = *h;
					let val = head.load() >> lsedge;
					accum = resize(val);
					rem -= (T::BITS - lsedge) as usize;
				}
				//  Read the body, from low to high, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: u64 = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
						rem -= T::BITS as usize;
					}
				}
				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					//  The live bits are at the LSedge of the element.
					let width = *t as usize;
					let val = tail.load() & mask_for::<T>(width);
					accum <<= width;
					accum |= resize(val);
					rem -= width;
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");

				debug_assert!(rem == 0, "Bits remaining to load");
				Some(resize(accum))
			},
		}
	}

	fn store<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			#[cfg(debug_assertions)]
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);

			#[cfg(not(debug_assertions))]
			return;
		}

		/* Write chunks, from least-significant to most-significant, into the
		`self` domain elements. Each successive write must copy the write amount
		into memory, then right-shift the value by the write amount.
		*/
		match self.bitptr().domain().splat() {
			Either::Right((head, elt, _)) => {
				let value = value & mask_for(len);
				//  Get the distance from the LSedge.
				let lsedge = *head;
				//  Erase the destination slot.
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				//  Write the value into that slot.
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			Either::Left((head, body, tail)) => {
				let mut value = resize::<U, u64>(value) & mask_for::<u64>(len);
				let mut rem = len;

				/* In little-endian byte-order architectures, the MSelement is
				at the high address and the LSelement is at the low address.
				Write from low addresses to high into memory.
				*/
				#[cfg(target_endian = "little")] {

				//  If the head exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					let lsedge = *h;
					let width = T::BITS - lsedge;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the MSedge region.
					head.clear_bits(T::TRUE >> width);
					head.set_bits(resize::<u64, T>(val) << lsedge);
					value >>= width;
					rem -= width as usize;
				}
				//  Write the value, from low to high, into memory.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
						rem -= T::BITS as usize;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the LSedge region.
					tail.clear_bits(T::TRUE << width);
					tail.set_bits(resize(val));
					value >>= width;
					rem -= width as usize;
				}

				}

				/* In big-endian byte-order architectures, the MSelement is at
				the low address and the LSelement is at the high address. Write
				from high addresses to low into memory.
				*/
				#[cfg(target_endian = "big")] {

				//  If the tail exists, it holds the least significant chunk of
				//  the destination, on the LSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the LSedge region
					tail.clear_bits(T::TRUE << width);
					tail.set_bits(resize(val));
					value >>= width;
					rem -= width as usize;
				}
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(resize(value));
						value >>= bits;
						rem -= T::BITS as usize;
					}
				}
				//  If the head exists, it holds the most significant chunk of
				//  the value, on the MSedge side.
				if let Some((h, head)) = head {
					let lsedge = *h;
					let width = T::BITS - lsedge;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the MSedge region.
					head.clear_bits(T::TRUE >> width);
					head.set_bits(resize::<u64, T>(val) << lsedge);
					value >>= width;
					rem -= width as usize;
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");

				debug_assert!(value == 0, "Bits remaining to store");
				debug_assert!(rem == 0, "Bits remaining to store");
			},
		}
	}
}

impl<T> BitField<T> for BitSlice<BigEndian, T>
where T: BitStore {
	fn load<U>(&self) -> Option<U>
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			return None;
		}

		match self.bitptr().domain().splat() {
			Either::Right((_, elt, tail)) => {
				//  Get the distance from the LSedge.
				let lsedge = T::BITS - *tail;
				//  Load the value, shift it to LSedge, and mask.
				let val = (elt.load() >> lsedge) & mask_for::<T>(len);
				Some(resize(val))
			},
			Either::Left((head, body, tail)) => {
				/* Read chunks, from most-significant to least-significant, into
				this value. Each successive read must left-shift by the read
				amount, then write the chunk into the now-free least significant
				bits.
				*/
				let mut accum = 0u64;

				let mut rem = len;

				//  Same element ordering as in the LittleEndian implementation.
				#[cfg(target_endian = "little")] {

				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					//  Get the distance from the LSedge.
					let lsedge = T::BITS - width;
					let val: u64 = resize(tail.load() >> lsedge);
					accum |= val;
					rem -= width as usize;
				}
				//  Read the body, from high to low, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: u64 = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
						rem -= T::BITS as usize;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = (T::BITS - *h) as usize;
					let val = head.load() & mask_for::<T>(width);
					accum <<= width;
					accum |= resize::<T, u64>(val);
					rem -= width;
				}

				}

				//  Same element ordering as in the LittleEndian implementation.
				#[cfg(target_endian = "big")] {

				//  If the head exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = (T::BITS - *h) as usize;
					let val = head.load() & mask_for::<T>(width);
					accum |= resize::<T, u64>(val);
					rem -= width;
				}
				//  Read the body, from low to high, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: u64 = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
						rem -= T::BITS as usize;
					}
				}
				//  If the tail exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					//  Get the distance from the LSedge.
					let lsedge = T::BITS - *t;
					let width = *t as usize;
					let val = tail.load() >> lsedge;
					accum <<= width;
					accum |= resize(val);
					rem -= width;
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");

				debug_assert!(rem == 0, "Bits remaining to load");
				Some(resize(accum))
			},
		}
	}

	fn store<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			#[cfg(debug_assertions)]
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);

			#[cfg(not(debug_assertions))]
			return;
		}

		/* Write chunks, from least significant to most-significant, into the
		`self` domain elements. Each successive write must copy the write amount
		into memory, then right-shift the value by the write amount.
		*/
		match self.bitptr().domain().splat() {
			Either::Right((_, elt, tail)) => {
				let value = value & mask_for(len);
				let lsedge = T::BITS - *tail;
				elt.clear_bits(!(mask_for::<T>(len) << lsedge));
				elt.set_bits(resize::<U, T>(value) << lsedge);
			},
			Either::Left((head, body, tail)) => {
				let mut value = resize::<U, u64>(value) & mask_for::<u64>(len);
				dbg!(value);
				let mut rem = len;

				//  Same element ordering as in the LittleEndian implementation.
				#[cfg(target_endian = "little")] {

				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = T::BITS - *h;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the LSedge region.
					head.clear_bits(T::TRUE << width);
					head.set_bits(resize(val));
					value >>= width;
					rem -= width as usize;
				}
				//  Write the value, from low to high, into memory.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
						rem -= T::BITS as usize;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					let lsedge = T::BITS - width;
					let val = value & mask_for::<u64>(width as usize);
					//  Clear the MSedge region.
					tail.clear_bits(T::TRUE >> width);
					tail.set_bits(resize::<u64, T>(val) << lsedge);
					value >>= width;
					rem -= width as usize;
				}

				}


				//  Same element ordering as in the LittleEndian implementation.
				#[cfg(target_endian = "big")] {

				//

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");

				debug_assert!(value == 0, "Bits remaining to store");
				debug_assert!(rem == 0, "Bits remaining to store");
			},
		}
	}
}

/** Safely compute an LS-edge bitmask for a value of some length.

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

This function uses `u64` as the intermediate type (as it is the largest
`BitStore` implementor), and either zero-extends or truncates the source value
to be valid as the destination type. This is essentially a generic-aware version
of the `as` operator.

# Parameters

- `value`: Any value to be resized.

# Returns

The result of transforming `value as U`. Where `U` is wider than `T`, this
zero-extends; where `U` is narrower, it truncates.
**/
fn resize<T, U>(value: T) -> U
where T: BitStore, U: BitStore {
	let mut slab = 0u64.to_ne_bytes();
	let cursor = 0;

	/* Copy the source value into the correct region of the intermediate slab.

	The `BitStore::as_bytes` method returns the value as native-endian-order
	bytes. These bytes are then written into the correct location of the slab
	(low on little-endian, high on big-endian) to be interpreted as `u64`.
	*/
	match mem::size_of::<T>() {
		1 => {
			#[cfg(target_endian = "big")]
			let cursor = 7;

			slab[cursor ..][.. 1].copy_from_slice(value.as_bytes());
		},
		2 => {
			#[cfg(target_endian = "big")]
			let cursor = 6;

			slab[cursor ..][.. 2].copy_from_slice(value.as_bytes());
		},
		4 => {
			#[cfg(target_endian = "big")]
			let cursor = 4;

			slab[cursor ..][.. 4].copy_from_slice(value.as_bytes());
		},
		8 => slab[..].copy_from_slice(value.as_bytes()),
		_ => unreachable!("BitStore is not implemented on types of this size"),
	}
	let mid = u64::from_ne_bytes(slab);
	//  Truncate to the correct size, then wrap in `U` through the trait method.
	match mem::size_of::<U>() {
		1 => U::from_bytes(&(mid as u8).to_ne_bytes()[..]),
		2 => U::from_bytes(&(mid as u16).to_ne_bytes()[..]),
		4 => U::from_bytes(&(mid as u32).to_ne_bytes()[..]),
		8 => U::from_bytes(&mid.to_ne_bytes()[..]),
		_ => unreachable!("BitStore is not implemented on types of this size"),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn check_resize() {
		assert_eq!(resize::<u8, u8>(0xA5), 0xA5);
		assert_eq!(resize::<u8, u16>(0xA5), 0xA5);
		assert_eq!(resize::<u8, u32>(0xA5), 0xA5);

		assert_eq!(resize::<u16, u8>(0x1234), 0x34);
		assert_eq!(resize::<u16, u16>(0x1234), 0x1234);
		assert_eq!(resize::<u16, u32>(0x1234), 0x1234);

		assert_eq!(resize::<u32, u8>(0x1234_5678), 0x78);
		assert_eq!(resize::<u32, u16>(0x1234_5678), 0x5678);
		assert_eq!(resize::<u32, u32>(0x1234_5678), 0x1234_5678);

		#[cfg(target_pointer_width = "64")] {

		assert_eq!(resize::<u8, u64>(0xA5), 0xA5);
		assert_eq!(resize::<u16, u64>(0x1234), 0x1234);
		assert_eq!(resize::<u32, u64>(0x1234_5678), 0x1234_5678);

		assert_eq!(resize::<u64, u8>(0x0123_4567_89ab_cdef), 0xef);
		assert_eq!(resize::<u64, u16>(0x0123_4567_89ab_cdef), 0xcdef);
		assert_eq!(resize::<u64, u32>(0x0123_4567_89ab_cdef), 0x89ab_cdef);
		assert_eq!(resize::<u64, u64>(0x0123_4567_89ab_cdef), 0x0123_4567_89ab_cdef);

		}
	}

	#[test]
	fn le() {
		let mut data = [0u8; 2];
		let bits = data.bits_mut::<LittleEndian>();

		bits[.. 3].store(15u8);
		assert_eq!(bits[.. 4].load(), Some(7u8));
		assert_eq!(bits.as_slice(), [7, 0]);

		bits[6 .. 10].store(31u8);
		assert_eq!(bits[5 .. 11].load(), Some(30u8));
		assert_eq!(bits.as_slice(), [192 | 7, 3]);

		bits[13 ..].store(15u8);
		assert_eq!(bits[12 ..].load(), Some(14u8));
		assert_eq!(bits.as_slice(), [192 | 7, 224 | 3]);

		bits[10 .. 13].store(15u8);
		assert_eq!(bits.as_slice(), [192 | 7, 255]);
		assert_eq!(bits[8 ..].load(), Some(255u8));

		bits[.. 8].store(0u8);
		bits[8 ..].store(0u8);

		bits[.. 3].store(1u8);
		assert_eq!(bits[.. 3].load(), Some(1u8));
		bits[3 .. 6].store(4u8);
		assert_eq!(bits[3 .. 6].load(), Some(4u8));

		assert!(bits[5 .. 5].load::<u8>().is_none());
	}

	#[test]
	fn be() {
		let mut data = [0u8; 2];
		let bits = data.bits_mut::<BigEndian>();

		bits[.. 3].store(15u8);
		assert_eq!(bits[.. 4].load(), Some(14u8));
		assert_eq!(bits.as_slice(), [224, 0]);

		bits[6 .. 10].store(31u8);
		assert_eq!(bits[5 .. 11].load(), Some(30u8));
		assert_eq!(bits.as_slice(), [224 | 3, 192]);

		bits[13 ..].store(15u8);
		assert_eq!(bits[12 ..].load(), Some(7u8));
		assert_eq!(bits.as_slice(), [224 | 3, 192 | 7]);

		bits[10 .. 13].store(15u8);
		assert_eq!(bits[10 .. 13].load(), Some(7u8));
		assert_eq!(bits.as_slice(), [224 | 3, 255]);
		assert_eq!(bits[8 ..].load(), Some(255u8));

		bits[.. 8].store(0u8);
		bits[8 ..].store(0u8);

		bits[.. 3].store(1u8);
		assert_eq!(bits[.. 3].load(), Some(1u8));
		bits[.. 3].store(4u8);
		//  old set bits are erased
		assert_eq!(bits[.. 3].load(), Some(4u8));

		bits[3 .. 6].store(4u8);
		assert_eq!(bits[3 .. 6].load(), Some(4u8));

		assert!(bits[5 .. 5].load::<u8>().is_none());
	}

	#[test]
	fn le_u8() {
		let mut slab = [0u8; 8];
		let slice = slab.bits_mut::<LittleEndian>();
		let mut val = 1u32;
		for _ in 0 .. 20 {
			slice[5 ..][.. 20].store(val);
			assert_eq!(slice[5 ..][.. 20].load::<u32>().unwrap(), val);
			val <<= 1;
			val |= 1;
		}

		slice[5 ..][.. 20].store(18u32);
		eprintln!("{:?}", slice);
		let val: u32 = slice[5 ..][.. 20].load().unwrap();
		assert_eq!(val, 18);
		// panic!("{:x?}", slice.as_slice());
	}
}
