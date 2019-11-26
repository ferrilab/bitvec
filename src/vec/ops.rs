//! Operator trait implementations.

use super::*;

use crate::{
	order::BitOrder,
	store::BitStore,
};

use core::{
	ops::{
		Add,
		AddAssign,
		BitAnd,
		BitAndAssign,
		BitOr,
		BitOrAssign,
		BitXor,
		BitXorAssign,
		Deref,
		DerefMut,
		Index,
		IndexMut,
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
		Neg,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
		Sub,
		SubAssign,
	},
};

/** Adds two `BitVec`s together, zero-extending the shorter.

`BitVec` addition works just like adding numbers longhand on paper. The first
bits in the `BitVec` are the highest, so addition works from right to left, and
the shorter `BitVec` is assumed to be extended to the left with zero.

The output `BitVec` may be one bit longer than the longer input, if addition
overflowed.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<O, T> Add for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Adds two `BitVec`s.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 0, 1];
	/// let b = bitvec![0, 0, 1, 1];
	/// let s = a + b;
	/// assert_eq!(bitvec![1, 0, 0, 0], s);
	/// ```
	///
	/// This example demonstrates the addition of differently-sized `BitVec`s,
	/// and will overflow.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![1; 4];
	/// let b = bitvec![1; 1];
	/// let s = b + a;
	/// assert_eq!(bitvec![1, 0, 0, 0, 0], s);
	/// ```
	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

/** Adds another `BitVec` into `self`, zero-extending the shorter.

`BitVec` addition works just like adding numbers longhand on paper. The first
bits in the `BitVec` are the highest, so addition works from right to left, and
the shorter `BitVec` is assumed to be extended to the left with zero.

The output `BitVec` may be one bit longer than the longer input, if addition
overflowed.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<O, T> AddAssign for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Adds another `BitVec` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut a = bitvec![1, 0, 0, 1];
	/// let b = bitvec![0, 1, 1, 1];
	/// a += b;
	/// assert_eq!(a, bitvec![1, 0, 0, 0, 0]);
	/// ```
	fn add_assign(&mut self, mut addend: Self) {
		use core::iter::repeat;
		//  If the other vec is longer, swap them before continuing.
		if addend.len() > self.len() {
			mem::swap(self, &mut addend);
		}
		//  Now that self.len() >= addend.len(), proceed with addition.
		let mut c = false;
		let mut stack = BitVec::<O, T>::with_capacity(self.len());
		let addend = addend.into_iter().rev().chain(repeat(false));
		for (a, b) in self.iter().copied().rev().zip(addend) {
			let (y, z) = crate::rca1(a, b, c);
			stack.push(y);
			c = z;
		}
		//  If the carry made it to the end, push it.
		if c {
			stack.push(true);
		}
		//  Unwind the stack into `self`.
		self.clear();
		self.extend(stack.into_iter().rev());
	}
}

/** Performs the Boolean `AND` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<O, T, I> BitAnd<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `AND`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![Msb0, u8; 0, 1, 0, 1];
	/// let rhs = bitvec![Msb0, u8; 0, 0, 1, 1];
	/// let and = lhs & rhs;
	/// assert_eq!("[0001]", &format!("{}", and));
	/// ```
	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

/** Performs the Boolean `AND` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<O, T, I> BitAndAssign<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	/// `AND`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![Msb0, u8; 0, 1, 0, 1];
	///         src &= bitvec![Msb0, u8; 0, 0, 1, 1];
	/// assert_eq!("[0001]", &format!("{}", src));
	/// ```
	fn bitand_assign(&mut self, rhs: I) {
		let mut len = 0;
		for bit in rhs.into_iter().take(self.len()) {
			let cur = unsafe { *self.get_unchecked(len) };
			unsafe { self.set_unchecked(len, cur & bit); }
			len += 1;
		}
		self.truncate(len);
	}
}

/** Performs the Boolean `OR` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<O, T, I> BitOr<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `OR`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![0, 1, 0, 1];
	/// let rhs = bitvec![0, 0, 1, 1];
	/// let or  = lhs | rhs;
	/// assert_eq!("[0111]", &format!("{}", or));
	/// ```
	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

/** Performs the Boolean `OR` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<O, T, I> BitOrAssign<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	/// `OR`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![0, 1, 0, 1];
	///         src |= bitvec![0, 0, 1, 1];
	/// assert_eq!("[0111]", &format!("{}", src));
	/// ```
	fn bitor_assign(&mut self, rhs: I) {
		let mut len = 0;
		for bit in rhs.into_iter().take(self.len()) {
			let cur = unsafe { *self.get_unchecked(len) };
			unsafe { self.set_unchecked(len, cur | bit); }
			len += 1;
		}
		self.truncate(len);
	}
}

/** Performs the Boolean `XOR` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<O, T, I> BitXor<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `XOR`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![0, 1, 0, 1];
	/// let rhs = bitvec![0, 0, 1, 1];
	/// let xor = lhs ^ rhs;
	/// assert_eq!("[0110]", &format!("{}", xor));
	/// ```
	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

/** Performs the Boolean `XOR` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<O, T, I> BitXorAssign<I> for BitVec<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	/// `XOR`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![0, 1, 0, 1];
	///         src ^= bitvec![0, 0, 1, 1];
	/// assert_eq!("[0110]", &format!("{}", src));
	/// ```
	fn bitxor_assign(&mut self, rhs: I) {
		let mut len = 0;
		for bit in rhs.into_iter().take(self.len()) {
			let cur = unsafe { *self.get_unchecked(len) };
			unsafe { self.set_unchecked(len, cur ^ bit); }
			len += 1;
		}
		self.truncate(len);
	}
}

/** Reborrows the `BitVec` as a `BitSlice`.

This mimics the separation between `Vec<T>` and `[T]`.
**/
impl<O, T> Deref for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Target = BitSlice<O, T>;

	/// Dereferences `&BitVec` down to `&BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec = bitvec![1; 4];
	/// let bref: &BitSlice = &bv;
	/// assert!(bref[2]);
	/// ```
	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

/** Mutably reborrows the `BitVec` as a `BitSlice`.

This mimics the separation between `Vec<T>` and `[T]`.
**/
impl<O, T> DerefMut for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Dereferences `&mut BitVec` down to `&mut BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = bitvec![0; 6];
	/// let bref: &mut BitSlice = &mut bv;
	/// assert!(!bref[5]);
	/// bref.set(5, true);
	/// assert!(bref[5]);
	/// ```
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

/// Readies the underlying storage for Drop.
impl<O, T> Drop for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Rebuild the interior `Vec` and let it run the deallocator.
	fn drop(&mut self) {
		let bp = mem::replace(&mut self.pointer, BitPtr::empty());
		//  Build a Vec<T> out of the elements, and run its destructor.
		let (ptr, cap) = (bp.pointer(), self.capacity);
		drop(unsafe { Vec::from_raw_parts(ptr.w(), 0, cap) });
	}
}

/// Gets the bit at a specific index. The index must be less than the length of
/// the `BitVec`.
impl<O, T> Index<usize> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = bool;

	/// Looks up a single bit by semantic count.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
	/// assert!(!bv[7]); // ---------------------------------^  |  |
	/// assert!( bv[8]); // ------------------------------------^  |
	/// assert!(!bv[9]); // ---------------------------------------^
	/// ```
	///
	/// If the index is greater than or equal to the length, indexing will
	/// panic.
	///
	/// The below test will panic when accessing index 1, as only index 0 is
	/// valid.
	///
	/// ```rust,should_panic
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::new();
	/// bv.push(true);
	/// bv[1];
	/// ```
	fn index(&self, cursor: usize) -> &Self::Output {
		&self.as_bitslice()[cursor]
	}
}

impl<O, T> Index<Range<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: Range<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<Range<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeFrom<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeFrom<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeFull> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self.as_bitslice()
	}
}

impl<O, T> IndexMut<RangeFull> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self.as_mut_bitslice()
	}
}

impl<O, T> Index<RangeInclusive<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeInclusive<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeTo<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeTo<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeTo<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeToInclusive<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeToInclusive<usize>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

/** 2’s-complement negation of a `BitVec`.

In 2’s-complement, negation is defined as bit-inversion followed by adding one.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<O, T> Neg for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Numerically negates a `BitVec` using 2’s-complement arithmetic.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 1];
	/// let ne = -bv;
	/// assert_eq!(ne, bitvec![1, 0, 1]);
	/// ```
	fn neg(mut self) -> Self::Output {
		//  An empty vector does nothing.
		//  Negative zero is zero. Without this check, -[0+] becomes[10+1].
		if self.is_empty() || self.not_any() {
			return self;
		}
		self = !self;
		let mut one = Self::new();
		one.push(true);
		self += one;
		self
	}
}

/// Flips all bits in the vector.
impl<O, T> Not for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Inverts all bits in the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec<Msb0, u32> = BitVec::from(&[0u32] as &[u32]);
	/// let flip = !bv;
	/// assert_eq!(!0u32, flip.as_slice()[0]);
	/// ```
	fn not(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().not();
		self
	}
}

__bitvec_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/** Shifts all bits in the vector to the left – **DOWN AND TOWARDS THE FRONT**.

On fundamentals, the left-shift operator `<<` moves bits away from origin and
towards the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, left-shifting moves bits towards the **minimum**.

In `Msb0` order, the effect in memory will be what you expect the `<<` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `>>` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than
left to their old value.

The length of the vector is decreased by the shift amount.

If the shift amount is greater than the length, the vector calls `clear()` and
zeroes its memory. This is *not* an error.
**/
impl<O, T> Shl<usize> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Shifts a `BitVec` to the left, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let ls = bv << 2usize;
	/// assert_eq!("[0111]", &format!("{}", ls));
	/// assert_eq!(0b0111_0000, ls.as_slice()[0]);
	/// assert_eq!(ls.len(), 4);
	/// ```
	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

/** Shifts all bits in the vector to the left – **DOWN AND TOWARDS THE FRONT**.

On fundamentals, the left-shift operator `<<` moves bits away from origin and
towards the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, left-shifting moves bits towards the **minimum**.

In `Msb0` order, the effect in memory will be what you expect the `<<` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `>>` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is decreased by the shift amount.

If the shift amount is greater than the length, the vector calls `clear()` and
zeroes its memory. This is *not* an error.
**/
impl<O, T> ShlAssign<usize> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Shifts a `BitVec` to the left in place, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![Lsb0, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv <<= 2;
	/// assert_eq!("[0111]", &format!("{}", bv));
	/// assert_eq!(0b0000_1110, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 4);
	/// ```
	fn shl_assign(&mut self, shamt: usize) {
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			self.clear();
			return;
		}
		for idx in shamt .. len {
			let val = self[idx];
			self.set(idx.saturating_sub(shamt), val);
		}
		let trunc = len.saturating_sub(shamt);
		for idx in trunc .. len {
			self.set(idx, false);
		}
		self.truncate(trunc);
	}
}

/** Shifts all bits in the vector to the right – **UP AND TOWARDS THE BACK**.

On fundamentals, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, right-shifting moves bits towards the **maximum**.

In `Msb0` order, the effect in memory will be what you expect the `>>` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `<<` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is increased by the shift amount.

If the new length of the vector would overflow, a panic occurs. This *is* an
error.
**/
impl<O, T> Shr<usize> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Shifts a `BitVec` to the right, lengthening it and filling the front
	/// with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let rs = bv >> 2usize;
	/// assert_eq!("[00000111]", &format!("{}", rs));
	/// assert_eq!(0b0000_0111, rs.as_slice()[0]);
	/// assert_eq!(rs.len(), 8);
	/// ```
	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

/** Shifts all bits in the vector to the right – **UP AND TOWARDS THE BACK**.

On fundamentals, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, right-shifting moves bits towards the **maximum**.

In `Msb0` order, the effect in memory will be what you expect the `>>` operator
to do.

**In `Lsb0` order, the effect will be equivalent to using `<<` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is increased by the shift amount.

If the new length of the vector would overflow, a panic occurs. This *is* an
error.
**/
impl<O, T> ShrAssign<usize> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Shifts a `BitVec` to the right in place, lengthening it and filling the
	/// front with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![Lsb0, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv >>= 2;
	/// assert_eq!("[00000111]", &format!("{}", bv));
	/// assert_eq!(0b1110_0000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 8);
	/// ```
	fn shr_assign(&mut self, shamt: usize) {
		let old_len = self.len();
		for _ in 0 .. shamt {
			self.push(false);
		}
		for idx in (0 .. old_len).rev() {
			let val = self[idx];
			self.set(idx.saturating_add(shamt), val);
		}
		for idx in 0 .. shamt {
			self.set(idx, false);
		}
	}
}

/** Subtracts one `BitVec` from another assuming 2’s-complement encoding.

Subtraction is a more complex operation than addition. The bit-level work is
largely the same, but semantic distinctions must be made. Unlike addition, which
is commutative and tolerant of switching the order of the addends, subtraction
cannot swap the minuend (LHS) and subtrahend (RHS).

Because of the properties of 2’s-complement arithmetic, M - S is equivalent to M
+ (!S + 1). Subtraction therefore bitflips the subtrahend and adds one. This
may, in a degenerate case, cause the subtrahend to increase in length.

Once the subtrahend is stable, the minuend zero-extends its left side in order
to match the length of the subtrahend if needed (this is provided by the `>>`
operator).

When the minuend is stable, the minuend and subtrahend are added together by the
`<BitVec as Add>` implementation. The output will be encoded in 2’s-complement,
so a leading one means that the output is considered negative.

Interpreting the contents of a `BitVec` as an integer is beyond the scope of
this crate.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<O, T> Sub for BitVec<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	/// Subtracts one `BitVec` from another.
	///
	/// # Examples
	///
	/// Minuend larger than subtrahend, positive difference.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![1, 0];
	/// let b = bitvec![   1];
	/// let c = a - b;
	/// assert_eq!(bitvec![0, 1], c);
	/// ```
	///
	/// Minuend smaller than subtrahend, negative difference.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![   1];
	/// let b = bitvec![1, 0];
	/// let c = a - b;
	/// assert_eq!(bitvec![1, 1], c);
	/// ```
	///
	/// Subtraction from self is correctly handled.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 1, 0];
	/// let b = a.clone();
	/// let c = a - b;
	/// assert!(c.not_any(), "{:?}", c);
	/// ```
	fn sub(mut self, subtrahend: Self) -> Self::Output {
		self -= subtrahend;
		self
	}
}

/** Subtracts another `BitVec` from `self`, assuming 2’s-complement encoding.

The minuend is zero-extended, or the subtrahend sign-extended, as needed to
ensure that the vectors are the same width before subtraction occurs.

The `Sub` trait has more documentation on the subtraction process.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<O, T> SubAssign for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Subtracts another `BitVec` from `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 0, 0, 1];
	/// let b = bitvec![0, 0, 0, 0];
	/// let c = a - b;
	/// assert_eq!(c, bitvec![0, 0, 0, 1]);
	/// ```
	//  Note: in `a - b`, `a` is `self` and the minuend, `b` is the subtrahend
	fn sub_assign(&mut self, mut subtrahend: Self) {
		//  Test for a zero subtrahend. Subtraction of zero is the identity
		//  function, and can exit immediately.
		if subtrahend.not_any() {
			return;
		}
		//  Invert the subtrahend in preparation for addition
		subtrahend = -subtrahend;
		let (llen, rlen) = (self.len(), subtrahend.len());
		//  If the subtrahend is longer than the minuend, 0-extend the minuend.
		if rlen > llen {
			let diff = rlen - llen;
			*self >>= diff;
		}
		else {
			//  If the minuend is longer than the subtrahend, sign-extend the
			//  subtrahend.
			if llen > rlen {
				let diff = llen - rlen;
				let sign = subtrahend[0];
				subtrahend >>= diff;
				subtrahend[.. diff].set_all(sign);
			}
		}
		let old = self.len();
		*self += subtrahend;
		//  If the subtraction emitted a carry, remove it.
		if self.len() > old {
			*self <<= 1;
		}
	}
}
