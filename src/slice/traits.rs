/*! General trait implementations for `BitSlice`.

The operator traits are defined in the `ops` module.
!*/

use super::*;

use core::{
	cmp::Ordering,
	hint::unreachable_unchecked,
};

#[cfg(feature = "alloc")]
use crate::{
	vec::BitVec,
};

#[cfg(feature = "alloc")]
impl<C, T> ToOwned for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Owned = BitVec<C, T>;

	fn to_owned(&self) -> Self::Owned {
		BitVec::from_bitslice(self)
	}
}

impl<C, T> Eq for BitSlice<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.partial_cmp(rhs)
			//  `BitSlice` has a total ordering, and never returns `None`.
			.unwrap_or_else(|| unsafe { unreachable_unchecked() })
	}
}

/** Tests if two `BitSlice`s are semantically — not bitwise — equal.

It is valid to compare two slices of different cursor or element types.

The equality condition requires that they have the same number of total bits and
that each pair of bits in semantic order are identical.
**/
impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performas a comparison by `==`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// If the two slices are equal, by comparing the lengths and bit values at
	/// each semantic index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lsrc = [8u8, 16, 32, 0];
	/// let rsrc = 0x10_08_04_00u32;
	/// let lbits = lsrc.bits::<LittleEndian>();
	/// let rbits = rsrc.bits::<BigEndian>();
	///
	/// assert_eq!(lbits, rbits);
	/// ```
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		if self.len() != rhs.len() {
			return false;
		}
		self.iter().zip(rhs.iter()).all(|(l, r)| l == r)
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		(*self).eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.eq(*rhs)
	}
}

/** Compares two `BitSlice`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one slice to have a set bit where
the other has an unset bit. If the slices are different, the slice with the set
bit sorts greater than the slice with the unset bit.

If one of the slices is exhausted before they differ, the longer slice is
greater.
**/
impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performs a comparison by `<` or `>`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// The relative ordering of `self` against `rhs`. `self` is greater if it
	/// has a `true` bit at an index where `rhs` has a `false`; `self` is lesser
	/// if it has a `false` bit at an index where `rhs` has a `true`; if the two
	/// slices do not disagree then they are compared by length.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0x45u8;
	/// let bits = src.bits::<BigEndian>();
	/// let a = &bits[0 .. 3]; // 010
	/// let b = &bits[0 .. 4]; // 0100
	/// let c = &bits[0 .. 5]; // 01000
	/// let d = &bits[4 .. 8]; // 0101
	///
	/// assert!(a < b);
	/// assert!(b < c);
	/// assert!(c < d);
	/// ```
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		for (l, r) in self.iter().zip(rhs.iter()) {
			match (l, r) {
				(true, false) => return Some(Ordering::Greater),
				(false, true) => return Some(Ordering::Less),
				_ => continue,
			}
		}
		self.len().partial_cmp(&rhs.len())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		(*self).partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.partial_cmp(*rhs)
	}
}

// impl<C, T> AsMut<[T]> for BitSlice<C, T>
// where C: Cursor, T: BitStore {
// 	fn as_mut(&mut self) -> &mut [T]
// }
