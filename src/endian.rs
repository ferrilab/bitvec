/*! Endianness Markers

`BitVec` does not have a concept of byte- or element- level endianness, but
*does* have a concept of bit-level endianness. This module defines orders of
traversal of an element in the `BitVec` storage.
!*/

use super::bits::Bits;

/// Travels an element starting at the Most Significant Bit and ending at the
/// Least Significant Bit.
pub struct BigEndian;

/// Travels an element starting at the Least Significant Bit and ending at the
/// Most Significant Bit.
pub struct LittleEndian;

/** A manipulator trait for Endianness.

# Usage

`BitVec` stores semantic count, not a cursor into an element, as its `bits`
value. The methods on `Endian` all return a cursor into a storage element.

- `curr` computes the bit index of the count given. In Little-Endian order, this
  is the identity function (bit indices count up “left” from LSb), and in
  Big-Endian order, this subtracts the count given from `T::MASK` (bit indices
  count down “right” from MSb).
- `next` computes the next index forward from the count given. In Little-Endian
  order, this increments (moving up from LSb towards MSb); in Big-Endian order,
  this decrements (moving down from MSb towards LSb).
- `prev` computes the previous index backward from the count given. In
  Little-Endian order, this decrements (moving down towards LSb from MSb); in
  Big-Endian order, this increments (moving up towards MSb from LSb).
- `jump` computes a number of whole elements to move, as well as the bit index
  within the destination element of the target bit.

You should use `curr` to look up a bit at a known point, such as when indexing a
`BitVec`; you should use `next` or `prev` to implement push, pop, and iteration;
you should use `jump` only to implement striding iterators in a manner faster
than the default (which just repeatedly calls `next` and drops most yielded
values).

# Notes

All functions *take* a semantic count into a storage element, which will always
move upwards from zero, but all functions *return* an actual index to a specific
bit in the element achieved by shifting right and masking off all but the LSb of
the output. The output is *not* a semantic count, and does not need converted to
an index with `curr`. It therefore cannot be stored as the new semantic count
during a mutation. The caller is responsible for maintaining count status.

`next` and `prev` signal when they cross the boundary of a storage element. If
their second return value is true, then the first return value is an index into
the storage element either after (`next`) or before (`prev`) the element for
which the input count referred. The caller is responsible for ensuring that they
use the returned index in the correct storage element by inspecting this flag
and moving their selection accordingly.

`jump` returns the number of storage elements the caller will have to move their
cursor before indexing. `next` and `prev` can only move zero or one elements, so
their flag is a `bool` rather than an `isize`. The order swap for `jump` is
because the number of elements to move is expected to be a more significant part
of its return value than the edge flag is in `next` and `prev`.
**/
pub trait Endian {
	/// Compute the bit index at a given count.
	///
	/// In Little-Endian, this is a no-op; in Big-Endian, it subtracts the index
	/// from `T::MASK` (the maximum value).
	fn curr<T: Bits>(count: u8) -> u8;

	/// Compute the semantic index that logically follows the given index.
	///
	/// The first value returned must be passed into `curr` in order to index
	/// into an element. The second value indicates whether the increment points
	/// into a different element.
	fn next<T: Bits>(count: u8) -> (u8, bool) {
		let next = count.wrapping_add(1) & T::MASK;
		let wrap = next == 0;
		(next, wrap)
	}

	/// Compute the semantic index that logically precedes the given index.
	///
	/// The first value returned must be passed into `curr` in order to index
	/// into an element. The second value indicates whether the decrement points
	/// into a different element.
	fn prev<T: Bits>(count: u8) -> (u8, bool) {
		count.overflowing_sub(1)
	}

	/// Computes the bit index at a given semantic offset from the current
	/// cursor.
	///
	/// Returns a tuple where the first value is the number of whole storage
	/// elements to move, and the second is the bit index within the element.
	fn jump<T: Bits>(count: u8, offset: isize) -> (isize, u8) {
		assert!(count <= T::MASK, "Bit count out of range for the storage type");
		//  Add offset to *count*, not to the current bit index, because this
		//  math doesn't know how to move around in an ordering. The offset is
		//  signed in count order, not Endian order.
		//  Subtraction can never fail, because count is always >= 0 and
		//  `0 - isize::MIN` is `isize::MIN`, which does not overflow.
		//  In a non-overflowing addition, the result will be the position of
		//  the target bit
		match (count as isize).overflowing_add(offset) {
			//  If the addition overflows, then the offset is positive. Add as
			//  unsigned and use that.
			//  Note that this is guaranteed not to overflow `usize::MAX`
			//  because converting two positive signed integers to unsigned
			//  doubles the domain, which will always be enormously wider than
			//  the domain of count.
			(_, true) => {
				let far = Self::curr::<T>(count) as usize + offset as usize;
				//  The number of elements advanced is, conveniently, the number
				//  of bits advanced integer-divided by the number of bits in
				//  the elements, which even more conveniently, is equivalent to
				//  right-shift by the number of bits required to index an
				//  element. Note that we don't cast until *after* the shift, in
				//  order to ensure that it is zero-filled at the high bits.
				let elements = (far >> T::BITS) as isize;
				//  The new bit position of the cursor is the new position
				//  modulo the number of bits in the element (equivalent to
				//  bit-and of the provided mask).
				let pos = (far & (T::MASK as usize)) as u8;
				(elements, pos)
			},
			//  If `far` is negative, then the jump leaves the element going
			//  backward. If `far` is greater than `T::MASK`, then the jump
			//  leaves the element going forward.
			(far, _) if far < 0 || far > T::MASK as isize => {
				let elements = far >> T::BITS;
				let pos = (far & (T::MASK as isize)) as u8;
				(elements, Self::curr::<T>(pos))
			},
			//  Otherwise, `far` is the *bit count* in the current element. It
			//  must still be converted from count to bit index.
			(far, _) => {
				(0, Self::curr::<T>(far as u8))
			},
		}
	}

	#[doc(hidden)]
	const TY: &'static str = "";
}

impl Endian for BigEndian {
	fn curr<T: Bits>(count: u8) -> u8 {
		assert!(count <= T::MASK, "Index out of range of the storage type");
		T::MASK - count
	}

	const TY: &'static str = "BigEndian";
}

impl Endian for LittleEndian {
	fn curr<T: Bits>(count: u8) -> u8 {
		assert!(count <= T::MASK, "Index out of range of the storage type");
		count
	}

	const TY: &'static str = "LittleEndian";
}

#[cfg(test)]
mod tests {
	use super::*;

	/*
	All the comments below are because I didn't actually do the math correctly
	when writing the test cases, and kept getting test failures on perfectly
	sound code because I didn't grok what was actually going on. If you (either
	someone who is not me, or my future self) decide to add more test cases to
	this to harden expectations about what jump does, be absolutely sure you
	have correct expectations before changing the code if your tests fail.

	Be sure to remember that all the functions take a *semantic count*, not a
	*bit index*, and as such you should **not** pass different values to
	different Endian implementations in order to try to account for their
	different counting styles.
	*/

	#[test]
	fn incr_edge() {
		// assert_eq!(LittleEndian::next::<u8>(7), (0, true));
		// assert_eq!(BigEndian::next::<u8>(7), (7, true));
		// assert_eq!(LittleEndian::next::<u16>(15), (0, true));
		// assert_eq!(BigEndian::next::<u16>(15), (15, true));
		// assert_eq!(LittleEndian::next::<u32>(31), (0, true));
		// assert_eq!(BigEndian::next::<u32>(31), (31, true));
		// assert_eq!(LittleEndian::next::<u64>(63), (0, true));
		// assert_eq!(BigEndian::next::<u64>(63), (63, true));
	}

	#[test]
	fn decr_edge() {
		// assert_eq!(LittleEndian::prev::<u8>(0), (7, true));
		// assert_eq!(BigEndian::prev::<u8>(0), (0, true));
		// assert_eq!(LittleEndian::prev::<u16>(0), (15, true));
		// assert_eq!(BigEndian::prev::<u16>(0), (0, true));
		// assert_eq!(LittleEndian::prev::<u32>(0), (31, true));
		// assert_eq!(BigEndian::prev::<u32>(0), (0, true));
		// assert_eq!(LittleEndian::prev::<u64>(0), (63, true));
		// assert_eq!(BigEndian::prev::<u64>(0), (0, true));
	}

	#[test]
	fn jump_inside_elt() {
		//  TODO(myrrlyn): test the other two types.

		let (elt, bit) = LittleEndian::jump::<u8>(5, 2);
		assert_eq!(elt, 0);
		assert_eq!(bit, 7);

		//  Counts start from 0, so count 5 is the SIXTH bit
		let (elt, bit) = BigEndian::jump::<u8>(5, 2);
		assert_eq!(elt, 0);
		assert_eq!(bit, 0);

		let (elt, bit) = LittleEndian::jump::<u32>(20, 8);
		assert_eq!(elt, 0);
		assert_eq!(bit, 28);

		//  In Big-Endian order, count 20 is bit 11, and moving that backward by
		//  8 is addition, up to 19.
		let (elt, bit) = BigEndian::jump::<u32>(20, -8);
		assert_eq!(elt, 0);
		assert_eq!(bit, 19);
	}

	#[test]
	fn jump_backwards() {
		//  TODO(myrrlyn): Test the other three types.

		let (elt, bit) = LittleEndian::jump::<u32>(10, -15);
		assert_eq!(elt, -1);
		//  Moving backwards through LE starts at MSb and decrements
		//  10 - 10 is 0, 0 - 1 is 31, 31 - 4 is 27
		assert_eq!(bit, 27);

		let (elt, bit) = BigEndian::jump::<u32>(10, -15);
		assert_eq!(elt, -1);
		//  Moving backwards through BE starts at LSb and increments
		//  10 - 10 is count 0 (bit 31), then the cursor crosses the boundary
		//  and counts 0, 1, 2, 3, 4.
		assert_eq!(bit, 4);
	}

	#[test]
	fn jump_forwards() {
		//  TODO(myrrlyn): Test the other three types.

		let (elt, bit) = LittleEndian::jump::<u32>(25, 10);
		assert_eq!(elt, 1);
		assert_eq!(bit, 3);

		let (elt, bit) = BigEndian::jump::<u32>(25, 10);
		assert_eq!(elt, 1);
		//  Moving forwards through BE starts at MSb and decrements. 25 + 6 is
		//  count 31 (bit 0), then the cursor crosses the boundary and counts
		//  31, 30, 29, 28.
		assert_eq!(bit, 28);
	}

	#[test]
	fn jump_overflow() {
		//  TODO(myrrlyn): Test the other three types.

		//  Force an overflowing stride. We expect the destination bit *count*
		//  to be one less than the starting point (which on BigEndian will be
		//  `MASK - start - 1`), and the elements skipped to be
		//  `isize::MIN >> BITS` (an overflowing isize add will set the high bit
		//  as the `usize` repr).
		let start = 20;
		let (elt, bit) = LittleEndian::jump::<u32>(start, ::std::isize::MAX);

		assert_eq!(elt as usize, ::std::isize::MIN as usize >> u32::BITS);
		assert_eq!(bit, start - 1);

		let (elt, bit) = BigEndian::jump::<u32>(start, ::std::isize::MAX);
		assert_eq!(elt as usize, ::std::isize::MIN as usize >> u32::BITS);
		assert_eq!(bit, BigEndian::curr::<u32>(start) - 1);
	}

	#[test]
	fn curr_reversible() {
		for n in 0 .. 8 {
			assert_eq!(n, BigEndian::curr::<u8>(BigEndian::curr::<u8>(n)));
		}
		for n in 0 .. 16 {
			assert_eq!(n, BigEndian::curr::<u16>(BigEndian::curr::<u16>(n)));
		}
		for n in 0 .. 32 {
			assert_eq!(n, BigEndian::curr::<u32>(BigEndian::curr::<u32>(n)));
		}
		for n in 0 .. 64 {
			assert_eq!(n, BigEndian::curr::<u64>(BigEndian::curr::<u64>(n)));
		}
	}
}
