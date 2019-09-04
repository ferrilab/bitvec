/*! Operator implementations for `BitSlice`.

Operator trait implementations are moved here, in order to reduce the total size
of the `src/slice.rs` file.
!*/

use super::BitSlice;

use crate::{
	bits::BitsMut,
	cursor::Cursor,
	domain::BitDomainMut,
	pointer::BitPtr,
	store::{
		BitStore,
		IntoBitIdx,
	},
};

use core::{
	ops::{
		AddAssign,
		BitAndAssign,
		BitOrAssign,
		BitXorAssign,
		Index,
		IndexMut,
		Neg,
		Not,
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
		ShlAssign,
		ShrAssign,
	},
	ptr,
};


/** Performs unsigned addition in place on a `BitSlice`.

If the addend bitstream is shorter than `self`, the addend is zero-extended at
the left (so that its final bit matches with `self`’s final bit). If the addend
is longer, the excess front length is unused.

Addition proceeds from the right ends of each slice towards the left. Because
this trait is forbidden from returning anything, the final carry-out bit is
discarded.

Note that, unlike `BitVec`, there is no subtraction implementation until I find
a subtraction algorithm that does not require modifying the subtrahend.

Subtraction can be implemented by negating the intended subtrahend yourself and
then using addition, or by using `BitVec`s instead of `BitSlice`s.

# Type Parameters

- `I`: The bitstream to add into `self`. It must be finite and double-ended,
  since addition operates in reverse.
**/
impl<C, T, I> AddAssign<I> for BitSlice<C, T>
where C: Cursor, T: BitStore,
	I: IntoIterator<Item=bool>, I::IntoIter: DoubleEndedIterator {
	/// Performs unsigned wrapping addition in place.
	///
	/// # Examples
	///
	/// This example shows addition of a slice wrapping from max to zero.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0b1110_1111u8, 0b0000_0001];
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// let (nums, one) = bits.split_at_mut(12);
	/// let (accum, steps) = nums.split_at_mut(4);
	/// *accum += &*one;
	/// assert_eq!(accum, &steps[.. 4]);
	/// *accum += &*one;
	/// assert_eq!(accum, &steps[4 ..]);
	/// ```
	//  Clippy doesn’t like single-letter names (which is accurate) but this is
	//  pretty standard mathematical notation in EE.
	#[allow(clippy::many_single_char_names)]
	fn add_assign(&mut self, addend: I) {
		use core::iter;

		//  I don't, at this time, want to implement a carry-lookahead adder in
		//  software, so this is going to be a plain ripple-carry adder with
		//  O(n) runtime.
		//
		//  Computers are fast. Whatever.
		let mut c = false;
		//  Reverse self, reverse addend and zero-extend, and zip both together.
		//  This walks both slices from rightmost to leftmost, and considers an
		//  early expiration of addend to continue with 0 bits.
		//
		//  100111
		// +  0010
		//  ^^---- semantically zero
		let addend_iter = addend.into_iter().rev().chain(iter::repeat(false));
		for (i, b) in (0 .. self.len()).rev().zip(addend_iter) {
			//  Bounds checks are performed in the loop header.
			let a = unsafe { self.get_unchecked(i) };
			let (y, z) = crate::rca1(a, b, c);
			unsafe { self.set_unchecked(i, y); }
			c = z;
		}
	}
}

/** Performs the Boolean `AND` operation against another bitstream and writes
the result into `self`. If the other bitstream ends before `self,`, the
remaining bits of `self` are cleared.

# Type Parameters

- `I`: A stream of bits, which may be a `BitSlice` or some other bit producer as
  desired.
**/
impl<C, T, I> BitAndAssign<I> for BitSlice<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `AND`s a bitstream into a slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `rhs`: The bitstream to `AND` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = [0b0101_0100u8];
	/// let     other = [0b0011_0000u8];
	/// let lhs = store.as_mut_bitslice::<BigEndian>();
	/// let rhs = other.as_bitslice::<BigEndian>();
	/// lhs[.. 6] &= &rhs[.. 4];
	/// assert_eq!(store[0], 0b0001_0000);
	/// ```
	fn bitand_assign(&mut self, rhs: I) {
		use core::iter;
		rhs.into_iter()
			.chain(iter::repeat(false))
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| {
				let val = self[idx] & bit;
				self.set(idx, val);
			});
	}
}

/** Performs the Boolean `OR` operation against another bitstream and writes the
result into `self`. If the other bitstream ends before `self`, the remaining
bits of `self` are not affected.

# Type Parameters

- `I`: A stream of bits, which may be a `BitSlice` or some other bit producer as
  desired.
**/
impl<C, T, I> BitOrAssign<I> for BitSlice<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `OR`s a bitstream into a slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `rhs`: The bitstream to `OR` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = [0b0101_0100u8];
	/// let     other = [0b0011_0000u8];
	/// let lhs = store.as_mut_bitslice::<BigEndian>();
	/// let rhs = other.as_bitslice::<BigEndian>();
	/// lhs[.. 6] |= &rhs[.. 4];
	/// assert_eq!(store[0], 0b0111_0100);
	/// ```
	fn bitor_assign(&mut self, rhs: I) {
		rhs.into_iter()
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| {
				let val = self[idx] | bit;
				self.set(idx, val);
			});
	}
}

/** Performs the Boolean `XOR` operation against another bitstream and writes
the result into `self`. If the other bitstream ends before `self`, the remaining
bits of `self` are not affected.

# Type Parameters

- `I`: A stream of bits, which may be a `BitSlice` or some other bit producer as
  desired.
**/
impl<C, T, I> BitXorAssign<I> for BitSlice<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `XOR`s a bitstream into a slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `rhs`: The bitstream to `XOR` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = [0b0101_0100u8];
	/// let     other = [0b0011_0000u8];
	/// let lhs = store.as_mut_bitslice::<BigEndian>();
	/// let rhs = other.as_bitslice::<BigEndian>();
	/// lhs[.. 6] ^= &rhs[.. 4];
	/// assert_eq!(store[0], 0b0110_0100);
	/// ```
	fn bitxor_assign(&mut self, rhs: I) {
		rhs.into_iter()
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| {
				let val = self[idx] ^ bit;
				self.set(idx, val);
			})
	}
}

/** Indexes a single bit by semantic count. The index must be less than the
length of the `BitSlice`.
**/
impl<C, T> Index<usize> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = bool;

	/// Looks up a single bit by semantic index.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The semantic index of the bit to look up.
	///
	/// # Returns
	///
	/// The value of the bit at the requested index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0010_0000u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// assert!(bits[2]);
	/// assert!(!bits[3]);
	/// ```
	fn index(&self, index: usize) -> &Self::Output {
		let len = self.len();
		assert!(index < len, "Index out of range: {} >= {}", index, len);
		if unsafe { self.get_unchecked(index) } { &true } else { &false }
	}
}

impl<C, T> Index<Range<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(&self, Range { start, end }: Range<usize>) -> &Self::Output {
		let (data, head, len) = self.bitptr().raw_parts();
		assert!(
			start <= len,
			"Index {} out of range: {}",
			start,
			len,
		);
		assert!(end <= len, "Index {} out of range: {}", end, len);
		assert!(start <= end, "Ranges can only run from low to high");
		//  Find the number of elements to drop from the front, and the index of
		//  the new head
		let (skip, new_head) = head.offset(start as isize);
		let new_len = end - start;
		unsafe { BitPtr::new_unchecked(
			data.r().offset(skip),
			new_head,
			new_len,
		) }.into_bitslice::<C>()
	}
}

impl<C, T> IndexMut<Range<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(
		&mut self,
		Range { start, end }: Range<usize>,
	) -> &mut Self::Output {
		//  Get an immutable slice, and then type-hack mutability back in.
		(&self[start .. end]).bitptr().into_bitslice_mut()
	}
}

impl<C, T> Index<RangeInclusive<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		let start = *range.start();
		//  This check can never fail, due to implementation details of
		//  `BitPtr<T>`.
		if let Some(end) = range.end().checked_add(1) {
			&self[start .. end]
		}
		else {
			&self[start ..]
		}
	}
}

impl<C, T> IndexMut<RangeInclusive<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		(&self[range]).bitptr().into_bitslice_mut()
	}
}

impl<C, T> Index<RangeFrom<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(&self, RangeFrom { start }: RangeFrom<usize>) -> &Self::Output {
		&self[start .. self.len()]
	}
}

impl<C, T> IndexMut<RangeFrom<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		(&self[range]).bitptr().into_bitslice_mut()
	}
}

impl<C, T> Index<RangeFull> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self
	}
}

impl<C, T> IndexMut<RangeFull> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self
	}
}

impl<C, T> Index<RangeTo<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(&self, RangeTo { end }: RangeTo<usize>) -> &Self::Output {
		&self[0 .. end]
	}
}

impl<C, T> IndexMut<RangeTo<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		(&self[range]).bitptr().into_bitslice_mut()
	}
}

impl<C, T> Index<RangeToInclusive<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn index(
		&self,
		RangeToInclusive { end }: RangeToInclusive<usize>,
	) -> &Self::Output {
		&self[0 ..= end]
	}
}

impl<C, T> IndexMut<RangeToInclusive<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(
		&mut self,
		range: RangeToInclusive<usize>,
	) -> &mut Self::Output {
		(&self[range]).bitptr().into_bitslice_mut()
	}
}

/** Performs fixed-width 2’s-complement negation of a `BitSlice`.

Unlike the `!` operator (`Not` trait), the unary `-` operator treats the
`BitSlice` as if it represents a signed 2’s-complement integer of fixed width.
The negation of a number in 2’s complement is defined as its inversion (using
`!`) plus one, and on fixed-width numbers has the following discontinuities:

- A slice whose bits are all zero is considered to represent the number zero
  which negates as itself.
- A slice whose bits are all one is considered to represent the most negative
  number, which has no correpsonding positive number, and thus negates as zero.

This behavior was chosen so that all possible values would have *some* output,
and so that repeated application converges at idempotence. The most negative
input can never be reached by negation, but `--MOST_NEG` converges at the least
unreasonable fallback value, 0.

Because `BitSlice` cannot move, the negation is performed in place.
**/
impl<'a, C, T> Neg for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Output = Self;

	/// Perform 2’s-complement fixed-width negation.
	///
	/// Negation is accomplished by inverting the bits and adding one. This has
	/// one edge case: `1000…`, the most negative number for its width, will
	/// negate to zero instead of itself. It thas no corresponding positive
	/// number to which it can negate.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Examples
	///
	/// The contortions shown here are a result of this operator applying to a
	/// mutable reference, and this example balancing access to the original
	/// `BitVec` for comparison with aquiring a mutable borrow *as a slice* to
	/// ensure that the `BitSlice` implementation is used, not the `BitVec`.
	///
	/// Negate an arbitrary positive number (first bit clear).
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0110_1010u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// eprintln!("{:?}", bits.split_at(4));
	/// let num = &mut bits[.. 4];
	/// -num;
	/// eprintln!("{:?}", bits.split_at(4));
	/// assert_eq!(&bits[.. 4], &bits[4 ..]);
	/// ```
	///
	/// Negate an arbitrary negative number. This example will use the above
	/// result to demonstrate round-trip correctness.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b1010_0110u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// let num = &mut bits[.. 4];
	/// -num;
	/// assert_eq!(&bits[.. 4], &bits[4 ..]);
	/// ```
	///
	/// Negate the most negative number, which will become zero, and show
	/// convergence at zero.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 128u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// let num = &mut bits[..];
	/// -num;
	/// assert!(bits.not_any());
	/// let num = &mut bits[..];
	/// -num;
	/// assert!(bits.not_any());
	/// ```
	fn neg(self) -> Self::Output {
		use core::iter;
		//  negative zero is zero. The invert-and-add will result in zero, but
		//  this case can be detected quickly.
		if self.is_empty() || self.not_any() {
			return self;
		}
		//  The most negative number (leading one, all zeroes else) negates to
		//  zero.
		if self[0] {
			//  Testing the whole range, rather than [1 ..], is more likely to
			//  hit the fast path.
			self.set(0, false);
			if self.not_any() {
				return self;
			}
			self.set(0, true);
		}
		let _ = Not::not(&mut *self);
		AddAssign::add_assign(&mut *self, iter::once(true));
		self
	}
}

/// Flips all bits in the slice, in place.
impl<'a, C, T> Not for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Output = Self;

	/// Inverts all bits in the slice.
	///
	/// This will not affect bits outside the slice in slice storage elements.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8; 2];
	/// let bits = &mut src.as_mut_bitslice::<BigEndian>()[2 .. 14];
	/// let new_bits = !bits;
	/// //  The `bits` binding is consumed by the `!` operator, and a new
	/// //  reference is returned.
	/// assert_eq!(&src, &[0x3F, 0xFC]);
	/// ```
	fn not(self) -> Self::Output {
		match self.bitptr().domain_mut() {
			BitDomainMut::Empty => {},
			BitDomainMut::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					elt.invert::<C>(n.idx());
				}
			},
			BitDomainMut::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					head.invert::<C>(n.idx());
				}
				for elt in body {
					*elt = !*elt;
				}
				for n in 0 .. *t {
					tail.invert::<C>(n.idx());
				}
			},
			BitDomainMut::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					head.invert::<C>(n.idx());
				}
				for elt in body {
					*elt = !*elt;
				}
			},
			BitDomainMut::PartialTail(body, tail, t) => {
				for elt in body {
					*elt = !*elt;
				}
				for n in 0 .. *t {
					tail.invert::<C>(n.idx());
				}
			},
			BitDomainMut::Spanning(body) => {
				for elt in body {
					*elt = !*elt;
				}
			},
		}
		self
	}
}

__bitslice_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/** Shifts all bits in the array to the left — **DOWN AND TOWARDS THE FRONT**.

On primitives, the left-shift operator `<<` moves bits away from the origin and
towards the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BitSlice` WORKS!**

`BitSlice` defines its layout with the minimum on the left and the maximum on
the right! Thus, left-shifting moves bits towards the **minimum**.

In BigEndian order, the effect in memory will be what you expect the `<<`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `>>` on**
**the primitives in memory!**

# Notes

In order to preserve the effecs in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The shift amount is modulated against the array length, so it is not an error to
pass a shift amount greater than the array length.

A shift amount of zero is a no-op, and returns immediately.
**/
impl<C, T> ShlAssign<usize> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Shifts a slice left, in place.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `shamt`: The shift amount. If this is greater than the length, then
	///   the slice is zeroed immediately.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0x4Bu8, 0xA5];
	/// let bits = &mut src.as_mut_bitslice::<BigEndian>()[2 .. 14];
	/// *bits <<= 3;
	/// assert_eq!(&src, &[0b01_011_101, 0b001_000_01]);
	/// ```
	fn shl_assign(&mut self, shamt: usize) {
		use core::ops::Shr;
		if shamt == 0 {
			return;
		}
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			return;
		}
		//  If the shift amount is an even multiple of the element width AND the
		//  slice fully owns its memory, use `ptr::copy` instead of a bitwise
		//  crawl.
		if shamt & T::MASK as usize == 0 && self.bitptr().domain().is_spanning() {
			//  Compute the shift distance measured in elements.
			let offset = shamt.shr(T::INDX);
			//  Compute the number of elements that will remain.
			let elts = self.as_slice().len();
			let rem = elts.saturating_sub(offset);
			//  Clear the bits after the tail cursor before the move.
			let tail = self.bitptr().tail();
			let last_elt = self.as_mut_slice()[elts - 1].as_mut_bitslice::<C>();
			for n in *tail .. T::BITS {
				unsafe { last_elt.set_unchecked(n as usize, false); }
			}
			//  Memory model: suppose we have this slice of sixteen elements,
			//  that is shifted five elements to the left. We have three
			//  pointers and two lengths to manage.
			//  - rem is 11
			//  - offset is 5
			//  - head is [0]
			//  - body is [5; 11]
			//  - tail is [11]
			//  [ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			//              ^-------before------^
			//    ^-------after-------^ 0 0 0 0 0
			//  Pointer to the front of the slice
			let head: *mut T = self.as_mut_ptr();
			//  Pointer to the front of the section that will move and be
			//  retained
			let body: *const T = &self.as_slice()[offset];
			//  Pointer to the back of the slice that will be zero-filled.
			let tail: *mut T = &mut self.as_mut_slice()[rem];
			unsafe {
				ptr::copy(body, head, rem);
				ptr::write_bytes(tail, 0, offset);
			}
			return;
		}
		//  Otherwise, crawl.
		for (to, from) in (shamt .. len).enumerate() {
			unsafe {
				let val = self.get_unchecked(from);
				self.set_unchecked(to, val);
			}
		}
		for bit in (len.saturating_sub(shamt)) .. len {
			unsafe { self.set_unchecked(bit, false); }
		}
	}
}

/** Shifts all bits in the array to the right — **UP AND TOWARDS THE BACK**.

On primitives, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BitSlice` WORKS!**

`BitSlice` defines its layout with the minimum on the left and the maximum on
the right! Thus, right-shifting moves bits towards the **maximum**.

In Big-Endian order, the effect in memory will be what you expect the `>>`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `<<` on**
**the primitives in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The shift amount is modulated against the array length, so it is not an error to
pass a shift amount greater than the array length.

A shift amount of zero is a no-op, and returns immediately.
**/
impl<C, T> ShrAssign<usize> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Shifts a slice right, in place.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `shamt`: The shift amount. If this is greater than the length, then
	///   the slice is zeroed immediately.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0x4Bu8, 0xA5];
	/// let bits = &mut src.as_mut_bitslice::<BigEndian>()[2 .. 14];
	/// *bits >>= 3;
	/// assert_eq!(&src, &[0b01_000_00_1, 0b011_101_01])
	/// ```
	fn shr_assign(&mut self, shamt: usize) {
		if shamt == 0 {
			return;
		}
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			return;
		}
		//  If the shift amount is an even multiple of the element width AND the
		//  slice fully owns its memory, use `ptr::copy` instead of a bitwise
		//  crawl.
		if shamt & T::MASK as usize == 0 && self.bitptr().domain().is_spanning() {
			//  Compute the shift amount measured in elements.
			let offset = shamt >> T::INDX;
			// Compute the number of elements that will remain.
			let rem = self.as_slice().len().saturating_sub(offset);
			//  Clear the bits ahead of the head cursor before the move.
			let head = self.bitptr().head();
			let first_elt = self.as_mut_slice()[0].as_mut_bitslice::<C>();
			for n in 0 .. *head {
				unsafe { first_elt.set_unchecked(n as usize, false); }
			}
			//  Memory model: suppose we have this slice of sixteen elements,
			//  that is shifted five elements to the right. We have two pointers
			//  and two lengths to manage.
			//  - rem is 11
			//  - offset is 5
			//  - head is [0; 11]
			//  - body is [5]
			//  [ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			//    ^-------before------^
			//    0 0 0 0 0 ^-------after-------^
			let head: *mut T = self.as_mut_ptr();
			let body: *mut T = &mut self.as_mut_slice()[offset];
			unsafe {
				ptr::copy(head, body, rem);
				ptr::write_bytes(head, 0, offset);
			}
			return;
		}
		//  Otherwise, crawl.
		for (from, to) in (shamt .. len).enumerate().rev() {
			unsafe {
				let val = self.get_unchecked(from);
				self.set_unchecked(to, val);
			}
		}
		for bit in 0 .. shamt {
			unsafe { self.set_unchecked(bit, false); }
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::cursor::BigEndian;

	#[test]
	fn shl_assign() {
		let mut bytes = [0u8, 0, 0x5A, !0, !0];
		let bits = bytes.as_mut_bitslice::<BigEndian>();

		*bits <<= 16;
		assert_eq!(bits.as_slice(), &[0x5Au8, !0, !0, 0, 0]);

		let mut bytes = [!0u8, 0, 0, !0, !0, !0];
		let bits = &mut bytes.as_mut_bitslice::<BigEndian>()[2 .. 46];

		*bits <<= 16;
		assert_eq!(bits.bitptr().as_slice(), &[0xC0u8, !0, !0, 0xFC, 0, 3]);
	}

	#[test]
	fn shr_assign() {
		let mut bytes = [!0u8, !0, 0xA5, 0, 0];
		let bits = bytes.as_mut_bitslice::<BigEndian>();

		*bits >>= 16;
		assert_eq!(bits.as_slice(), &[0u8, 0, !0, !0, 0xA5]);

		let mut bytes = [0xF0u8, !0, !0, 0, 0, !0];
		let bits = &mut bytes.as_mut_bitslice::<BigEndian>()[2 .. 46];

		*bits >>= 16;
		assert_eq!(bits.bitptr().as_slice(), &[0xC0u8, 0, 0x30, !0, !0, 3]);
	}
}
