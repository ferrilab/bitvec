/*! Parallel bitfield access.

This module provides parallel, multiple-bit, access to a `BitSlice`. This
functionality permits the use of `BitSlice` as a library-level implementation of
the bitfield language feature found in C and C++.
!*/

use crate::{
	access::BitAccess,
	order::{
		Msb0,
		Lsb0,
	},
	slice::BitSlice,
	store::BitStore,
};

use core::mem;

use either::Either;

#[cfg(target_pointer_width = "32")]
type Usize = u32;

#[cfg(target_pointer_width = "64")]
type Usize = u64;

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_fail!("Bitfield access is not supported on this architecture");

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

impl<T> BitField<T> for BitSlice<Lsb0, T>
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
				let mut accum: Usize = 0;

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
				}
				//  Read the body, from high to low, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: Usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the MSedge side.
				if let Some((h, head)) = head {
					//  Get the distance from the LSedge.
					let lsedge = *h;
					//  Get the live chunk width.
					let width = T::BITS - lsedge;
					let val: Usize = resize(head.load() >> lsedge);
					accum <<= width;
					accum |= val;
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
				}
				//  Read the body, from low to high, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: Usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
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
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");

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
				let mut value = resize::<U, Usize>(value) & mask_for::<Usize>(len);

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
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the MSedge region.
					head.clear_bits(T::TRUE >> width);
					head.set_bits(resize::<Usize, T>(val) << lsedge);
					value >>= width;
				}
				//  Write the value, from low to high, into memory.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the LSedge region.
					tail.clear_bits(T::TRUE << width);
					tail.set_bits(resize(val));
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
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the LSedge region
					tail.clear_bits(T::TRUE << width);
					tail.set_bits(resize(val));
					value >>= width;
				}
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(resize(value));
						value >>= bits;
					}
				}
				//  If the head exists, it holds the most significant chunk of
				//  the value, on the MSedge side.
				if let Some((h, head)) = head {
					let lsedge = *h;
					let width = T::BITS - lsedge;
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the MSedge region.
					head.clear_bits(T::TRUE >> width);
					head.set_bits(resize::<Usize, T>(val) << lsedge);
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");
			},
		}
	}
}

impl<T> BitField<T> for BitSlice<Msb0, T>
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
				let mut accum: Usize = 0;

				//  Same element ordering as in the Lsb0 implementation.
				#[cfg(target_endian = "little")] {

				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					//  Get the distance from the LSedge.
					let lsedge = T::BITS - width;
					let val: Usize = resize(tail.load() >> lsedge);
					accum |= val;
				}
				//  Read the body, from high to low, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						let val: Usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
					}
				}
				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = (T::BITS - *h) as usize;
					let val = head.load() & mask_for::<T>(width);
					accum <<= width;
					accum |= resize::<T, Usize>(val);
				}

				}

				//  Same element ordering as in the Lsb0 implementation.
				#[cfg(target_endian = "big")] {

				//  If the head exists, it contains the most significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = (T::BITS - *h) as usize;
					let val = head.load() & mask_for::<T>(width);
					accum |= resize::<T, Usize>(val);
				}
				//  Read the body, from low to high, into the accumulator.
				if let Some(elts) = body {
					for elt in elts.iter() {
						let val: Usize = resize(elt.load());
						accum <<= T::BITS;
						accum |= val;
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
				}

				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");
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
				let mut value = resize::<U, Usize>(value) & mask_for::<Usize>(len);

				//  Same element ordering as in the Lsb0 implementation.
				#[cfg(target_endian = "little")] {

				//  If the head exists, it contains the least significant chunk
				//  of the value, on the LSedge side.
				if let Some((h, head)) = head {
					let width = T::BITS - *h;
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the LSedge region.
					head.clear_bits(T::TRUE << width);
					head.set_bits(resize(val));
					value >>= width;
				}
				//  Write the value, from low to high, into memory.
				if let Some(elts) = body {
					for elt in elts.iter() {
						elt.store(resize(value));
						value >>= T::BITS;
					}
				}
				//  If the tail exists, it contains the most significant chunk
				//  of the value, on the MSedge side.
				if let Some((tail, t)) = tail {
					let width = *t;
					let lsedge = T::BITS - width;
					let val = value & mask_for::<Usize>(width as usize);
					//  Clear the MSedge region.
					tail.clear_bits(T::TRUE >> width);
					tail.set_bits(resize::<Usize, T>(val) << lsedge);
				}

				}


				//  Same element ordering as in the Lsb0 implementation.
				#[cfg(target_endian = "big")] {

				if let Some((tail, t)) = tail {
					let lsedge = *t;
					let width = T::BITS - lsedge;
					let val = value & mask_for::<Usize>(width as usize);
					tail.clear_bits(T::TRUE >> width);
					tail.set_bits(resize::<Usize, T>(val) << lsedge);
					value >>= width;
				}
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(resize(value));
						value >>= bits;
					}
				}
				if let Some((h, head)) = head {}
					let width = *t;
					let val = value & mask_for::<Usize>(width as usize);
					head.clear_bits(T::TRUE << width);
					head.set_bits(resize(val));
				}

				#[cfg(not(any(
					target_endian = "bit",
					target_endian = "little",
				)))]
				compile_fail!("This architecture is not supported.");
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
	let zero: Usize = 0;
	let mut slab = zero.to_ne_bytes();
	let start = 0;

	/* Copy the source value into the correct region of the intermediate slab.

	The `BitStore::as_bytes` method returns the value as native-endian-order
	bytes. These bytes are then written into the correct location of the slab
	(low on little-endian, high on big-endian) to be interpreted as `u64`.
	*/
	match mem::size_of::<T>() {
		1 => {
			#[cfg(target_endian = "big")]
			let start = mem::size_of::<Usize>() - 1;

			slab[start ..][.. 1].copy_from_slice(value.as_bytes());
		},
		2 => {
			#[cfg(target_endian = "big")]
			let start = mem::size_of::<Usize>() - 2;

			slab[start ..][.. 2].copy_from_slice(value.as_bytes());
		},
		4 => {
			#[cfg(target_endian = "big")]
			let start = mem::size_of::<Usize>() - 4;

			slab[start ..][.. 4].copy_from_slice(value.as_bytes());
		},
		#[cfg(target_pointer_width = "64")]
		8 => slab[..].copy_from_slice(value.as_bytes()),
		_ => unreachable!("BitStore is not implemented on types of this size"),
	}
	let mid = Usize::from_ne_bytes(slab);
	//  Truncate to the correct size, then wrap in `U` through the trait method.
	match mem::size_of::<U>() {
		1 => U::from_bytes(&(mid as u8).to_ne_bytes()[..]),
		2 => U::from_bytes(&(mid as u16).to_ne_bytes()[..]),
		4 => U::from_bytes(&(mid as u32).to_ne_bytes()[..]),
		#[cfg(target_pointer_width = "64")]
		8 => U::from_bytes(&mid.to_ne_bytes()[..]),
		_ => unreachable!("BitStore is not implemented on types of this size"),
	}
}

#[allow(clippy::inconsistent_digit_grouping)]
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

	#[cfg(target_endian = "little")]
	#[test]
	fn le() {
		let mut bytes = [0u8; 16];
		let bytes = bytes.bits_mut::<Lsb0>();

		bytes[4 ..][.. 8].store(0xA5u8);
		assert_eq!(bytes[4 ..][.. 8].load(), Some(0xA5u8));
		assert_eq!(&bytes.as_slice()[.. 2], &[0b0101_0000, 0b0000_1010]);

		//  expected byte pattern: 0x34 0x12
		//  bits: 0011_0100 __01_0010
		//  idx:  7654 3210 fedc ba98
		bytes[6 ..][.. 14].store(0x1234u16);
		assert_eq!(bytes[6 ..][.. 14].load(), Some(0x1234u16));
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b00_010000, 0b10_0011_01, 0b0000_01_00],
		);
		//      10 xxxxxx    98 7654 32         dc ba

		//  bytes: 21        43        65        00
		//  bits:  0010 0001 0100 0011 0110 0101
		//  idx:   7654 3210 fedc ba98 nmlk jihg
		bytes[10 ..][.. 24].store(0x00_65_43_21u32);
		assert_eq!(bytes[10 ..][.. 24].load(), Some(0x00_65_43_21u32));
		assert_eq!(
			&bytes.as_slice()[1 .. 5],
			&[0b10_0001_01, 0b00_0011_00, 0b10_0101_01, 0b00000_01],
		);
		//      54 3210 xx    dc ba98 76    lk jihg fe   xxxxxx nm

		/*
		let mut shorts = [0u16; 8];
		let shorts = shorts.bits_mut::<Lsb0>();

		let mut ints = [0u32; 4];
		let ints = ints.bits_mut::<Lsb0>();

		#[cfg(target_pointer_width = "64")] {

		let mut longs = [0u64; 2];
		let longs = longs.bits_mut::<Lsb0>();

		}
		*/
	}

	#[cfg(target_endian = "little")]
	#[test]
	fn be() {
		let mut bytes = [0u8; 16];
		let bytes = bytes.bits_mut::<Msb0>();

		bytes[4 ..][.. 8].store(0xA5u8);
		assert_eq!(bytes[4 ..][.. 8].load(), Some(0xA5u8));
		assert_eq!(&bytes.as_slice()[.. 2], &[0b0000_0101, 0b1010_0000]);

		//  expected byte pattern: 0x34 0x12
		//  bits: 0011_0100 __01_0010
		//  idx:  7654 3210 fedc ba98
		bytes[6 ..][.. 14].store(0x1234u16);
		assert_eq!(bytes[6 ..][.. 14].load(), Some(0x1234u16));
		assert_eq!(
			&bytes.as_slice()[.. 3],
			&[0b000001_00, 0b10_0011_01, 0b01_00_0000],
		);
		//      xxxxxx 10    98 7654 32    dc ba

		//  bytes: 21        43        65        00
		//  bits:  0010 0001 0100 0011 0110 0101
		//  idx:   7654 3210 fedc ba98 nmlk jihg
		bytes[10 ..][.. 24].store(0x00_65_43_21u32);
		assert_eq!(bytes[10 ..][.. 24].load(), Some(0x00_65_43_21u32));
		assert_eq!(
			&bytes.as_slice()[1 .. 5],
			&[0b10_10_0001, 0b00_0011_00, 0b10_0101_01, 0b01_000000],
		);
		//  xxxxxx 54 3210    dc ba98 76    lk jihg fe    nm xxxxxx

		/*
		let mut shorts = [0u16; 8];
		let shorts = shorts.bits_mut::<Msb0>();

		let mut ints = [0u32; 4];
		let ints = ints.bits_mut::<Msb0>();

		#[cfg(target_pointer_width = "64")] {

		let mut longs = [0u64; 2];
		let longs = longs.bits_mut::<Msb0>();

		}
		*/
	}
}
