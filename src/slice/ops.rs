//! Operator trait implementations.

use super::api::BitSliceIndex;

use crate::{
	access::BitAccess,
	indices::Indexable,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use either::Either;

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

- `I: IntoIterator<Item=bool, IntoIter: DoubleEndedIterator>`: The bitstream to
  add into `self`. It must be finite and double-ended, since addition operates
  in reverse.
**/
impl<O, T, I> AddAssign<I> for BitSlice<O, T>
where O: BitOrder, T: BitStore,
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
	/// let bits = src.bits_mut::<Msb0>();
	/// let (nums, one) = bits.split_at_mut(12);
	/// let (accum, steps) = nums.split_at_mut(4);
	/// *accum += one.iter().copied();
	/// assert_eq!(accum, &steps[.. 4]);
	/// *accum += one.iter().copied();
	/// assert_eq!(accum, &steps[4 ..]);
	/// ```
	//  Clippy doesn’t like single-letter names (which is accurate) but this is
	//  pretty standard mathematical notation in EE.
	#[allow(clippy::many_single_char_names)]
	fn add_assign(&mut self, addend: I) {
		use core::iter::repeat;

		//  I don't, at this time, want to implement a carry-lookahead adder in
		//  software, so this is going to be a plain ripple-carry adder with
		//  O(n) runtime. Furthermore, until I think of an optimization
		//  strategy, it is going to build up another bitvec to use as a stack.
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
		let addend_iter = addend.into_iter().rev().chain(repeat(false));
		for (i, b) in (0 .. self.len()).rev().zip(addend_iter) {
			//  Bounds checks are performed in the loop header.
			let a = unsafe { *self.get_unchecked(i) };
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

- `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
  or some other bit producer as desired.
**/
impl<O, T, I> BitAndAssign<I> for BitSlice<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
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
	/// let lhs = store.bits_mut::<Msb0>();
	/// let rhs = other.bits::<Msb0>();
	/// lhs[.. 6] &= rhs[.. 4].iter().copied();
	/// assert_eq!(store[0], 0b0001_0000);
	/// ```
	fn bitand_assign(&mut self, rhs: I) {
		use core::iter;
		rhs.into_iter()
			.chain(iter::repeat(false))
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| unsafe {
				let val = *self.get_unchecked(idx);
				self.set_unchecked(idx, val & bit);
			});
	}
}

/** Performs the Boolean `OR` operation against another bitstream and writes the
result into `self`. If the other bitstream ends before `self`, the remaining
bits of `self` are not affected.

# Type Parameters

- `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
  or some other bit producer as desired.
**/
impl<O, T, I> BitOrAssign<I> for BitSlice<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
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
	/// let lhs = store.bits_mut::<Msb0>();
	/// let rhs = other.bits::<Msb0>();
	/// lhs[.. 6] |= rhs[.. 4].iter().copied();
	/// assert_eq!(store[0], 0b0111_0100);
	/// ```
	fn bitor_assign(&mut self, rhs: I) {
		rhs.into_iter()
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| unsafe {
				let val = *self.get_unchecked(idx);
				self.set_unchecked(idx, val | bit);
			});
	}
}

/** Performs the Boolean `XOR` operation against another bitstream and writes
the result into `self`. If the other bitstream ends before `self`, the remaining
bits of `self` are not affected.

# Type Parameters

- `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
  or some other bit producer as desired.
**/
impl<O, T, I> BitXorAssign<I> for BitSlice<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
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
	/// let lhs = store.bits_mut::<Msb0>();
	/// let rhs = other.bits::<Msb0>();
	/// lhs[.. 6] ^= rhs[.. 4].iter().copied();
	/// assert_eq!(store[0], 0b0110_0100);
	/// ```
	fn bitxor_assign(&mut self, rhs: I) {
		rhs.into_iter()
			.enumerate()
			.take(self.len())
			.for_each(|(idx, bit)| unsafe {
				let val = *self.get_unchecked(idx);
				self.set_unchecked(idx, val ^ bit);
			})
	}
}

impl<O, T> Index<usize> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = bool;

	fn index(&self, place: usize) -> &Self::Output {
		place.index(self)
	}
}

impl<O, T> Index<Range<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, range: Range<usize>) -> &Self {
		range.index(self)
	}
}

impl<O, T> IndexMut<Range<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self {
		range.index_mut(self)
	}
}

impl<O, T> Index<RangeInclusive<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, range: RangeInclusive<usize>) -> &Self {
		range.index(self)
	}
}

impl<O, T> IndexMut<RangeInclusive<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self {
		range.index_mut(self)
	}
}

impl<O, T> Index<RangeFrom<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, range: RangeFrom<usize>) -> &Self {
		range.index(self)
	}
}

impl<O, T> IndexMut<RangeFrom<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self {
		range.index_mut(self)
	}
}

impl<O, T> Index<RangeFull> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, _: RangeFull) -> &Self {
		self
	}
}

impl<O, T> IndexMut<RangeFull> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self {
		self
	}
}

impl<O, T> Index<RangeTo<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, range: RangeTo<usize>) -> &Self {
		range.index(self)
	}
}

impl<O, T> IndexMut<RangeTo<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self {
		range.index_mut(self)
	}
}

impl<O, T> Index<RangeToInclusive<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self {
		range.index(self)
	}
}

impl<O, T> IndexMut<RangeToInclusive<usize>> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self {
		range.index_mut(self)
	}
}

/** Performs fixed-width 2’s-complement negation of a `BitSlice`.

Unlike the `!` operator (`Not` trait), the unary `-` operator treats the
`BitSlice` as if it represents a signed 2’s-complement integer of fixed
width. The negation of a number in 2’s complement is defined as its
inversion (using `!`) plus one, and on fixed-width numbers has the following
discontinuities:

- A slice whose bits are all zero is considered to represent the number zero
  which negates as itself.
- A slice whose bits are all one is considered to represent the most negative
  number, which has no correpsonding positive number, and thus negates as zero.

This behavior was chosen so that all possible values would have *some*
output, and so that repeated application converges at idempotence. The most
negative input can never be reached by negation, but `--MOST_NEG` converges
at the least unreasonable fallback value, 0.

Because `BitSlice` cannot move, the negation is performed in place.
**/
impl<'a, O, T> Neg for &'a mut BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
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
	/// Negate an arbitrary positive number (first bit unset).
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0110_1010u8;
	/// let bits = src.bits_mut::<Msb0>();
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
	/// let bits = src.bits_mut::<Msb0>();
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
	/// let bits = src.bits_mut::<Msb0>();
	/// let num = &mut bits[..];
	/// -num;
	/// assert!(bits.not_any());
	/// let num = &mut bits[..];
	/// -num;
	/// assert!(bits.not_any());
	/// ```
	fn neg(self) -> Self::Output {
		//  negative zero is zero. The invert-and-add will result in zero, but
		//  this case can be detected quickly.
		if self.is_empty() || self.not_any() {
			return self;
		}
		//  The most negative number (leading one, all zeroes else) negates to
		//  zero.
		if unsafe { *self.get_unchecked(0) } {
			//  Testing the whole range, rather than [1 ..], is more likely to
			//  hit the fast path for `not_any`.
			unsafe { self.set_unchecked(0, false); }
			if self.not_any() {
				return self;
			}
			unsafe { self.set_unchecked(0, true); }
		}
		let this = !self;
		*this += core::iter::once(true);
		this
	}
}

/// Flips all bits in the slice, in place.
impl<'a, O, T> Not for &'a mut BitSlice<O, T>
where O: BitOrder, T: 'a + BitStore {
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
	/// let bits = &mut src.bits_mut::<Msb0>()[2 .. 14];
	/// let _ = !bits;
	/// //  The `bits` binding is consumed by the `!` operator, and a new
	/// //  reference is returned.
	/// // assert_eq!(bits.as_ref(), &[!0, !0]);
	/// assert_eq!(src, [0x3F, 0xFC]);
	/// ```
	fn not(self) -> Self::Output {
		match self.bitptr().domain().splat() {
			Either::Right((h, e, t)) => for n in *h .. *t {
				e.invert_bit::<O>(n.idx());
			},
			Either::Left((h, b, t)) => {
				if let Some((h, head)) = h {
					for n in *h .. T::BITS {
						head.invert_bit::<O>(n.idx())
					}
				}
				if let Some(body) = b {
					for elt in body {
						elt.store(!elt.load());
					}
				}
				if let Some((tail, t)) = t {
					for n in 0 .. *t {
						tail.invert_bit::<O>(n.idx())
					}
				}
			},
		}
		self
	}
}

__bitslice_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/** Shifts all bits in the array to the left — **DOWN AND TOWARDS THE FRONT**.

On fundamentals, the left-shift operator `<<` moves bits away from the origin
and  towards the ceiling. This is because we label the bits in a primitive with
the  minimum on the right and the maximum on the left, which is big-endian bit
order.  This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BitSlice` WORKS!**

`BitSlice` defines its layout with the minimum on the left and the maximum on
the right! Thus, left-shifting moves bits towards the **minimum**.

In `Msb0` order, the effect in memory will be what you expect the `<<` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `>>` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effecs in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than
left to their old value.

The shift amount is modulated against the array length, so it is not an
error to pass a shift amount greater than the array length.

A shift amount of zero is a no-op, and returns immediately.
**/
impl<O, T> ShlAssign<usize> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
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
	/// let bits = &mut src.bits_mut::<Msb0>()[2 .. 14];
	/// *bits <<= 3;
	/// assert_eq!(src, [0b01_011_101, 0b001_000_01]);
	/// ```
	#[allow(clippy::suspicious_op_assign_impl)] // These functions require math
	fn shl_assign(&mut self, shamt: usize) {
		if shamt == 0 {
			return;
		}
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			return;
		}
		//  If the slice fully owns its memory, then a fast path is available
		//  with element-wise `memmove`.
		if self.bitptr().domain().is_spanning() {
			//  Compute the shift distance measured in elements.
			let offset = shamt >> T::INDX;
			//  Compute the number of elements that will remain.
			let rem = self.bitptr().elements() - offset;

			/* Memory model: suppose we have this slice of sixteen elements,
			that is shifted five elements to the left. We have three pointers
			and two lengths to manage.
			- rem is 11 (len - offset)
			- offset is 5
			- to is &[0 .. 11]
			- from is &[5 .. 16]
			- tail is &[11]
			  _ _ _ _ _ v-------before------v
			[ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			  ^-------after-------^ 0 0 0 0 0
			*/

			//  Pointer to the front of the slice.
			let to: *mut T = self.as_mut_ptr();
			//  Pointer to the front of the section that will move and be
			//  retained.
			let from: *const T = &self.as_slice()[offset];
			//  Pointer to the back of the slice that will be zero-filled.
			let tail: *mut T = &mut self.as_mut_slice()[rem];
			unsafe {
				ptr::copy(from, to, rem);
				ptr::write_bytes(tail, 0, offset);
			}
			//  Any remaining shift amount only needs to shift the `after` block
			//  above.
			self[.. rem << T::INDX] <<= shamt & T::INDX as usize;
			return;
		}
		//  Otherwise, crawl.
		for (to, from) in (shamt .. len).enumerate() {
			unsafe { self.copy_unchecked(from, to); }
		}
		self[len - shamt ..].set_all(false);
	}
}

/** Shifts all bits in the array to the right — **UP AND TOWARDS THE BACK**.

On fundamentals, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BitSlice` WORKS!**

`BitSlice` defines its layout with the minimum on the left and the maximum on
the right! Thus, right-shifting moves bits towards the **maximum**.

In `Msb0` order, the effect in memory will be what you expect the `>>` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `<<` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The shift amount is modulated against the array length, so it is not an error to
pass a shift amount greater than the array length.

A shift amount of zero is a no-op, and returns immediately.
**/
impl<O, T> ShrAssign<usize> for BitSlice<O, T>
where O: BitOrder, T: BitStore {
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
	/// let bits = &mut src.bits_mut::<Msb0>()[2 .. 14];
	/// *bits >>= 3;
	/// assert_eq!(src, [0b01_000_00_1, 0b011_101_01])
	/// ```
	#[allow(clippy::suspicious_op_assign_impl)] // These functions require math
	fn shr_assign(&mut self, shamt: usize) {
		if shamt == 0 {
			return;
		}
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			return;
		}
		//  If the slice fully owns its memory, then a fast path is available
		//  with element-wise `memmove`.
		if self.bitptr().domain().is_spanning() {
			//  Compute the shift amount measured in elements.
			let offset = shamt >> T::INDX;
			// Compute the number of elements that will remain.
			let rem = self.bitptr().elements() - offset;

			/* Memory model: suppose we have this slice of sixteen elements,
			that is shifted five elements to the right. We have two pointers
			and two lengths to manage.
			- rem is 11 (len - offset)
			- offset is 5
			- from is &[0 .. 11]
			- to is &[5 .. 16]
			  v-------before------v
			[ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			  0 0 0 0 0 ^-------after-------^
			*/
			let from: *mut T = self.as_mut_ptr();
			let to: *mut T = &mut self.as_mut_slice()[offset];
			unsafe {
				ptr::copy(from, to, rem);
				ptr::write_bytes(from, 0, offset);
			}
			//  Any remaining shift amount only needs to shift the `after` block
			//  above.
			self[offset << T::INDX ..] >>= shamt & T::INDX as usize;
			return;
		}
		//  Otherwise, crawl.
		for (from, to) in (shamt .. len).enumerate().rev() {
			unsafe { self.copy_unchecked(from, to); }
		}
		self[.. shamt].set_all(false);
	}
}
