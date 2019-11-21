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
	domain::*,
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
	/// This can never load more than the width of `T` at a time.
	///
	/// # Parameters
	///
	/// - `&self`: A read reference to some bits in memory. This slice must be
	///   trimmed to have a width no more than the `T::BITS` width of the
	///   underlying type. This can be accomplished with range indexing on a
	///   larger slice.
	///
	/// # Returns
	///
	/// If `self` has a length greater than zero, but not greater than the `T`
	/// element width `T::BITS`, then this returns an element whose least
	/// `self.len()` significant bits are filled with the bits of `self`.
	///
	/// If `self` is empty, or wider than a single element, this returns `None`.
	fn load(&self) -> Option<T>;

	/// Stores a sequence of bits from the user into the domain of `self`.
	///
	/// This can never store more than the width of `T` at a time.
	///
	/// # Parameters
	///
	/// - `&mut self`: A write reference to some bits in memory. This slice must
	///   be trimmed to have a width no more than the `T::BITS` width of the
	///   underlying type. This can be accomplished with range indexing on a
	///   larger slice.
	///
	/// # Behavior
	///
	/// If `self` is the empty slice, or wider than an element, then this exits
	/// without effect. Otherwise, the `self.len()` least significant bits of
	/// `value` are written into the domain of `self`.
	fn store(&mut self, value: T);

	fn load_val<U>(&self) -> Option<U>
	where U: BitStore;

	fn store_val<U>(&mut self, value: U)
	where U: BitStore;
}

impl<T> BitField<T> for BitSlice<LittleEndian, T>
where T: BitStore {
	fn load(&self) -> Option<T> {
		let len = self.len();
		if !(1 ..= T::BITS as usize).contains(&len) {
			return None;
		}

		let low_mask = || mask_for(len);

		match self.bitptr().domain() {
			BitDomain::Empty => None,

			//  The live domain is in the middle of the element. The value must
			//  be shifted down by `h` (which counts upward from LSbit) and then
			//  masked for `len`.
			BitDomain::Minor(h, elt, _) => Some((elt.load() >> *h) & low_mask()),

			/* The live region of `self` is in the interior of a two-element
			span, touching neither outer edge but crossing the interior edge.
			Because of the `len` check above, the middle span is known to be
			empty, and the partially-filled `left` and `right` elements are
			adjacent.

			Consider this memory layout:

			M [ 7 6 5 4 3 2 1 0 ] L
			          v- tail
			1 [ _ _ _ _ h g f e ] <- right
			0 [ d c b a _ _ _ _ ] <- left
			          ^- head

			The load produces the value `0b_hgfedcba` by putting the high bits
			of `left` in the low bits of the output, and the low bits of `right`
			in the middle/high bits of the output.
			*/
			BitDomain::Major(head, left, [], right, _) => {
				let head = *head;

				//  Shift the left value down by the `head` amount, bringing the
				//  useful bit section of `left` to start at the `LSbit`.
				let low = left.load() >> head;

				//  Shift the right value up by the width of the remaining bits
				//  of `left`, bringing the useful bit section of `right` to
				//  start immediately after the end of the useful section of
				//  `left`.
				let high = right.load() << (T::BITS - head);

				//  Combine the two segments, then erase any high bits remaining
				//  in `right`.
				Some((high | low) & low_mask())
			},

			//  PartialHead and PartialTail will only occur if the slice touches
			//  one edge of an element, but not the other. Because of the
			//  requirements that `self` be no more than `T` bits wide, these
			//  domain types are guaranteed to not have any whole elements.
			BitDomain::PartialHead(head, elt, []) => Some(elt.load() >> *head),
			BitDomain::PartialTail([], elt, _) => Some(elt.load() & low_mask()),

			//  `self` fills an element, so that element is copied directly.
			BitDomain::Spanning([elt]) => Some(elt.load()),

			_ => unreachable!(
				"Invalid memory representation! File an issue at https://github.com/myrrlyn/bitvec, and include this information:\n\
				Pointer: {:?}\n\
				Domain : {:?}",
				self.bitptr(),
				self.bitptr().domain(),
			),
		}
	}

	fn store(&mut self, value: T) {
		let len = self.len();
		if !(1 ..= T::BITS as usize).contains(&len) {
			//  Panic in debug mode.
			#[cfg(debug_assertions)]
			panic!("Cannot store {} bits in a {}-bit region", T::BITS, len);

			#[cfg(not(debug_assertions))]
			return;
		}

		let mask = mask_for(len);

		//  Mask away unusable bits in the incoming `value`.
		let value = value & mask;

		match self.bitptr().domain() {
			BitDomain::Empty => {},

			BitDomain::Minor(head, elt, _) => {
				//  Erase the storage region, starting at `head` for `len`.
				elt.clear_bits(!(mask << *head));
				//  Write the truncated value into that region.
				elt.set_bits(value << *head);
			}

			//  See `load` for the memory model in effect here.
			BitDomain::Major(head, left, [], right, _) => {
				//  Split the value at the MSedge of `left`.
				let mid = T::BITS - *head;

				//  Separate the [.. mid] and [mid ..] parts of `value`.
				let low = value & !(T::bits(true) << mid);
				let high = value >> mid;

				//  Erase the most significant bits of the left element,
				left.clear_bits(T::bits(true) >> mid);
				//  And write the low bits of `value` into that slot.
				left.set_bits(low << *head);

				//  Erase the least lignificant bits of the right element,
				right.clear_bits(T::bits(true) << (len as u8 - mid));
				//  And write the high bits of `value` into that slot.
				right.set_bits(high);
			},

			//  The live region ends at the MSedge.
			BitDomain::PartialHead(head, elt, []) => {
				elt.clear_bits(T::bits(true) >> len as u8);
				elt.set_bits(value << *head);
			},

			//  The live region begins at the LSedge.
			BitDomain::PartialTail([], elt, _) => {
				elt.clear_bits(!mask);
				elt.set_bits(value);
			},

			BitDomain::Spanning([body]) => body.store(value),

			_ => unreachable!(
				"Invalid memory representation! File an issue at https://github.com/myrrlyn/bitvec, and include this information:\n\
				Pointer: {:?}\n\
				Domain : {:?}",
				self.bitptr(),
				self.bitptr().domain(),
			),

		}
	}

	fn load_val<U>(&self) -> Option<U>
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			return None;
		}

		//  Prepare eight bytes into which memory will be copied from `self`.
		let mut slab = 0u64.to_ne_bytes();
		//  Start the cursor from the right-most byte
		let mut cursor = 7;
		//  Save `self`’s bit pointer
		let bp = self.bitptr();
		//  In little-endian, the head is the distance from the first live bit
		//  to the LSedge.
		let shamt = *bp.head();
		//  Copy elements out of the total memory region covered by `self`, from
		//  right to left.
		for elt in bp.as_access_slice().iter().rev() {
			//  Copy bytes out of each element into the prepared slab, from
			//  right to left.
			for byte in elt.load().as_bytes().iter().rev() {
				slab[cursor] = *byte;
				dbg!(slab);
				cursor -= 1;
			}
		}
		//  After this loop, `slab`’s memory has live data in the rightmost
		//  elements. It needs to be recast into a `u64` as-is, then shifted
		//  right by `shamt` bits, then cast *back* into bytes.
		let bytes = (u64::from_be_bytes(slab) >> shamt).to_be_bytes();
		dbg!(bytes);
		//  The live bits are now touching the LSedge of `slab`. It must now be
		//  truncated to fit `U`.
		match mem::size_of::<U>() {
			1 => Some(U::from_bytes(&bytes[7 ..])),
			2 => Some(U::from_bytes(&bytes[6 ..])),
			4 => Some(U::from_bytes(&bytes[4 ..])),
			8 => Some(U::from_bytes(&bytes[..])),
			_ => unreachable!(
				"BitStore is not implemented on types of this size",
			),
		}
	}

	fn store_val<U>(&mut self, value: U)
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			//  Panic in debug mode.
			#[cfg(debug_assertions)]
			panic!("Cannot store {} bits in a {}-bit region", U::BITS, len);

			#[cfg(not(debug_assertions))]
			return;
		}

		let mut slab = expand::<U>(value);
		match self.bitptr().domain().splat() {
			Either::Right((head, elt, _)) => {
				let head = *head;
				//  Erase the storage region, from `head` for `len`
				elt.clear_bits(!(mask_for::<T>(len) << head));
				//  Truncate `value` to `T`, then for `len`, and write
				elt.set_bits(trunc::<T>(slab) << head);
			},
			Either::Left((head, body, tail)) => {
				let mut rem = len;
				//  Fill the partial tail, if present
				if let Some((tail, t)) = tail {
					//  `t` counts how many bits MSward from LSedge are live.
					let t = *t;
					//  Get the right-most `t` bits of `slab`
					let masked = slab & mask_for::<u64>(t as usize);
					//  Erase the right-most bits of `tail`.
					tail.clear_bits(T::bits(true) << t);
					//  Write the right chunk of `slab` into `tail`
					tail.set_bits(trunc(masked));
					//  And discard the written partial element.
					slab >>= t;
					rem -= t as usize;
				}
				//  Now, copy chunks of `slab` into `body`
				if let Some(elts) = body {
					for elt in elts.iter().rev() {
						elt.store(trunc(slab));
						slab >>= T::BITS;
						rem -= T::BITS as usize;
					}
				}
				//  Fill the partial head, if present
				if let Some((h, head)) = head {
					//  `h` counts how many bits MSward from LSedge are dead.
					let h = *h;
					//  Get the remaining right-most `t` bits of `slab`
					let masked = slab & mask_for::<u64>(rem);
					head.clear_bits(T::bits(true) >> (rem as u8));
					head.set_bits(trunc(masked << h));
					rem -= (T::BITS - h) as usize;
				}
				debug_assert!(rem == 0, "Bits still remain after filling `self`");
			},
		}

		fn expand<T>(val: T) -> u64
		where T: BitStore {
			let mut slab = 0u64.to_ne_bytes();
			let mut cursor = 0;

			match mem::size_of::<T>() {
				1 => {
					#[cfg(target_endian = "big")]
					let mut cursor = 7;

					for byte in val.as_bytes() {
						slab[cursor] = *byte;
						cursor += 1;
					}
				},
				2 => {
					#[cfg(target_endian = "big")]
					let mut cursor = 6;

					for byte in val.as_bytes() {
						slab[cursor] = *byte;
						cursor += 1;
					}
				},
				4 => {
					#[cfg(target_endian = "big")]
					let mut cursor = 4;

					for byte in val.as_bytes() {
						slab[cursor] = *byte;
						cursor += 1;
					}
				},
				8 => {
					for byte in val.as_bytes() {
						slab[cursor] = *byte;
						cursor += 1;
					}
				},
				_ => unreachable!(
					"BitStore is not implemented on types of this size",
				),
			}
			u64::from_ne_bytes(slab)
		}

		fn trunc<T>(src: u64) -> T
		where T: BitStore {
			match mem::size_of::<T>() {
				1 => T::from_bytes(&(src as u8).to_ne_bytes()[..]),
				2 => T::from_bytes(&(src as u16).to_ne_bytes()[..]),
				4 => T::from_bytes(&(src as u32).to_ne_bytes()[..]),
				8 => T::from_bytes(&src.to_ne_bytes()[..]),
				_ => unreachable!(
					"BitStore is not implemented on types of this size",
				),
			}
		}
	}
}

impl<T> BitField<T> for BitSlice<BigEndian, T>
where T: BitStore {
	fn load(&self) -> Option<T> {
		let len = self.len();
		if !(1 ..= T::BITS as usize).contains(&len) {
			return None;
		}

		let low_mask = || mask_for(len);

		match self.bitptr().domain() {
			BitDomain::Empty => None,

			//  `t` is towards the LSedge; move the value to LSedge, and mask
			//  the high excess.
			BitDomain::Minor(_, e, t) => {
				Some((e.load() >> (T::BITS - *t)) & low_mask())
			},

			/* The live region of `self` is in the interior of a two-element
			span, touching neither outer edge but crossing the interior edge
			between them. Because of the `len` check above, the middle span is
			known to be empty, and the partially-filled `left` and `right`
			elements are adjacent.

			Consider this memory layout:

			M [ 0 1 2 3 4 5 6 7 ] L
			            v- tail
			1 [ e f g h _ _ _ _ ] <- right
			0 [ _ _ _ _ a b c d ] <- left
			            ^- head

			The load produces the value `0b_abcdefgh` by putting the high bits
			of `right` in the low bits of the output, and the low bits of `left`
			in the middle/high bits of the output.
			*/
			BitDomain::Major(head, left, [], right, tail) => {
				//  There are `width - head` live bits on the LSedge of `left`,
				let left_bits = T::BITS - *head;
				//  And `len - left` live bits on the MSedge of `right`.
				let right_bits = len as u8 - left_bits;

				//  Move `left` from LSedge upwards by the rumber of live bits
				//  in `right`.
				let high = left.load() << right_bits;
				//  Move `right` from MSedge down to LSedge by the number of
				//  dead bits in `right`.
				let low = right.load() >> (T::BITS - *tail);

				//  Recombine, and mask away any excess.
				Some((high | low) & low_mask())
			},

			//  Touches the LSedge, so only the mask is needed.
			BitDomain::PartialHead(_, e, []) => Some(e.load() & low_mask()),

			//  Touches the MSedge, so only the shift is needed.
			BitDomain::PartialTail([], e, t) => Some(e.load() >> (T::BITS - *t)),

			BitDomain::Spanning([body]) => Some(body.load()),

			_ => unreachable!(
				"Invalid memory representation! File an issue at https://github.com/myrrlyn/bitvec, and include this information:\n\
				Pointer: {:?}\n\
				Domain : {:?}",
				self.bitptr(),
				self.bitptr().domain(),
			),

		}
	}

	fn store(&mut self, value: T) {
		let len = self.len();

		if !(1 ..= T::BITS as usize).contains(&len) {
			//  Panic in debug mode.
			#[cfg(debug_assertions)]
			panic!("Cannot store {} bits in a {}-bit region", T::BITS, len);

			#[cfg(not(debug_assertions))]
			return;
		}

		let mask = mask_for(len);
		let value = value & mask;

		match self.bitptr().domain() {
			BitDomain::Empty => {},

			BitDomain::Minor(_, elt, tail) => {
				//  Find the distance between the LSedge and the live region,
				let dead_low = T::BITS - *tail;
				//  Then erase `len` bits of live region, offset from LSedge.
				elt.clear_bits(!(mask << dead_low));
				//  Shift `value` away from LSedge, and write.
				elt.set_bits(value << dead_low);
			},

			//  See `load` for the memory model in effect here.
			BitDomain::Major(head, left, [], right, tail) => {
				//  The left element erases from the interior up to the LSedge.
				left.clear_bits(!(T::bits(true) >> *head));
				//  The least `*tail` bits of the value go in `right`; the
				//  remaining bits are written into the LSedge region of `left`.
				left.set_bits(value >> *tail);

				//  The right element erases from MSedge up to the interior.
				right.clear_bits(T::bits(true) >> *tail);
				//  Upshift `value` by the number of dead bits in `right`,
				//  discarding bits written into `left`, and write into `right`.
				right.set_bits(value << (T::BITS - *tail));
			},

			//  The live region touches LSedge but not MSedge.
			BitDomain::PartialHead(_, elt, []) => {
				//  Erase the `len` bits ending at LSedge.
				elt.clear_bits(T::bits(true) << len as u8);
				//  Write.
				elt.set_bits(value);
			},

			//  The live region touches MSedge but not LSedge.
			BitDomain::PartialTail([], elt, _) => {
				//  Erase the `len` bits starting from MSedge.
				elt.clear_bits(T::bits(true) >> len as u8);
				//  Shift the value up from LSedge to MSedge and write.
				elt.set_bits(value << (T::BITS - len as u8));
			},

			BitDomain::Spanning([body]) => body.store(value),

			_ => unreachable!(
				"Invalid memory representation! File an issue at https://github.com/myrrlyn/bitvec, and include this information:\n\
				Pointer: {:?}\n\
				Domain : {:?}",
				self.bitptr(),
				self.bitptr().domain(),
			),

		}
	}

	fn load_val<U>(&self) -> Option<U>
	where U: BitStore {
		let len = self.len();
		if !(1 ..= U::BITS as usize).contains(&len) {
			return None;
		}
		unimplemented!()
	}

	fn store_val<U>(&mut self, value: U)
	where U: BitStore {
		unimplemented!()
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
		T::bits(true)
	}
	else {
		!(T::bits(true) << len)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::prelude::*;

	#[test]
	fn le() {
		let mut data = [0u8; 2];
		let bits = data.bits_mut::<LittleEndian>();

		bits[.. 3].store(15);
		assert_eq!(bits[.. 4].load(), Some(7));
		assert_eq!(bits.as_slice(), [7, 0]);

		bits[6 .. 10].store(31);
		assert_eq!(bits[5 .. 11].load(), Some(30));
		assert_eq!(bits.as_slice(), [192 | 7, 3]);

		bits[13 ..].store(15);
		assert_eq!(bits[12 ..].load(), Some(14));
		assert_eq!(bits.as_slice(), [192 | 7, 224 | 3]);

		bits[10 .. 13].store(15);
		assert_eq!(bits.as_slice(), [192 | 7, 255]);
		assert_eq!(bits[8 ..].load(), Some(255));

		bits[.. 8].store(0);
		bits[8 ..].store(0);

		bits[.. 3].store(1);
		assert_eq!(bits[.. 3].load(), Some(1));
		bits[3 .. 6].store(4);
		assert_eq!(bits[3 .. 6].load(), Some(4));

		assert!(bits[5 .. 5].load().is_none());
	}

	#[test]
	fn be() {
		let mut data = [0u8; 2];
		let bits = data.bits_mut::<BigEndian>();

		bits[.. 3].store(15);
		assert_eq!(bits[.. 4].load(), Some(14));
		assert_eq!(bits.as_slice(), [224, 0]);

		bits[6 .. 10].store(31);
		assert_eq!(bits[5 .. 11].load(), Some(30));
		assert_eq!(bits.as_slice(), [224 | 3, 192]);

		bits[13 ..].store(15);
		assert_eq!(bits[12 ..].load(), Some(7));
		assert_eq!(bits.as_slice(), [224 | 3, 192 | 7]);

		bits[10 .. 13].store(15);
		assert_eq!(bits[10 .. 13].load(), Some(7));
		assert_eq!(bits.as_slice(), [224 | 3, 255]);
		assert_eq!(bits[8 ..].load(), Some(255));

		bits[.. 8].store(0);
		bits[8 ..].store(0);

		bits[.. 3].store(1);
		assert_eq!(bits[.. 3].load(), Some(1));
		bits[.. 3].store(4);
		//  old set bits are erased
		assert_eq!(bits[.. 3].load(), Some(4));

		bits[3 .. 6].store(4);
		assert_eq!(bits[3 .. 6].load(), Some(4));

		assert!(bits[5 .. 5].load().is_none());
	}

	#[test]
	fn le_u8() {
		let mut slab = [0u8; 8];
		let slice = slab.bits_mut::<LittleEndian>();
		let mut val = 1u32;
		for _ in 0 .. 20 {
			slice[5 ..][.. 20].store_val(val);
			eprintln!("{:?}", &slice[5 ..][.. 20]);
			val <<= 1;
			val |= 1;
		}

		slice[5 ..][.. 20].store_val(18u32);
		eprintln!("{:?}", slice);
		let val: u32 = slice[5 ..][.. 20].load_val().unwrap();
		assert_eq!(val, 18);
		panic!("{:x?}", slice.as_slice());
	}
}
