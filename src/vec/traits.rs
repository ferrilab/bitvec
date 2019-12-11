/*! General trait implementations for `BitVec`.

The operator traits are defined in the `ops` module.
!*/

use super::*;

use crate::{
	order::BitOrder,
	store::BitStore,
};

use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
		ToOwned,
	},
	boxed::Box,
	vec::Vec,
};

use core::{
	cmp::Ordering,
	fmt::{
		self,
		Binary,
		Debug,
		Display,
		Formatter,
		LowerHex,
		Octal,
		UpperHex,
	},
	hash::{
		Hash,
		Hasher,
	},
	marker::PhantomData,
	mem,
};

/// Signifies that `BitSlice` is the borrowed form of `BitVec`.
impl<O, T> Borrow<BitSlice<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Borrows the `BitVec` as a `BitSlice`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A borrowed `BitSlice` of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use std::borrow::Borrow;
	///
	/// let bv = bitvec![0; 13];
	/// let bs: &BitSlice = bv.borrow();
	/// assert!(!bs[10]);
	/// ```
	fn borrow(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

/// Signifies that `BitSlice` is the borrowed form of `BitVec`.
impl<O, T> BorrowMut<BitSlice<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Mutably borrows the `BitVec` as a `BitSlice`.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutably borrowed `BitSlice` of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// use std::borrow::BorrowMut;
	///
	/// let mut bv = bitvec![0; 13];
	/// let bs: &mut BitSlice = bv.borrow_mut();
	/// assert!(!bs[10]);
	/// bs.set(10, true);
	/// assert!(bs[10]);
	/// ```
	fn borrow_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<O, T> Clone for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn clone(&self) -> Self {
		let new_vec = self.as_slice().to_owned();
		let capacity = new_vec.capacity();
		let mut pointer = self.pointer;
		unsafe { pointer.set_pointer(new_vec.as_ptr()); }
		mem::forget(new_vec);
		Self {
			_order: PhantomData,
			pointer, // unsafe { BitPtr::new_unchecked(ptr, e, h, t) },
			capacity,
		}
	}

	fn clone_from(&mut self, other: &Self) {
		let slice = other.pointer.as_slice();
		self.clear();
		//  Copy the other data region into the underlying vector, then grab its
		//  pointer and capacity values.
		let (ptr, capacity) = self.with_vec(|v| {
			v.copy_from_slice(slice);
			(v.as_ptr(), v.capacity())
		});
		//  Copy the other `BitPtr<T>`,
		let mut pointer = other.pointer;
		//  Then set it to aim at the copied pointer.
		unsafe { pointer.set_pointer(ptr); }
		//  And set the new pointer/capacity.
		self.pointer = pointer;
		self.capacity = capacity;
	}
}

impl<O, T> Eq for BitVec<O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> Ord for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bitslice().cmp(rhs.as_bitslice())
	}
}

/** Tests if two `BitVec`s are semantically — not bitwise — equal.

It is valid to compare two vectors of different order or element types.

The equality condition requires that they have the same number of stored bits
and that each pair of bits in semantic order are identical.
**/
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	/// Performs a comparison by `==`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: The other vector to compare.
	///
	/// # Returns
	///
	/// Whether the vectors compare equal.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let l: BitVec<Lsb0, u16> = bitvec![Lsb0, u16; 0, 1, 0, 1];
	/// let r: BitVec<Msb0, u32> = bitvec![Msb0, u32; 0, 1, 0, 1];
	/// assert!(l == r);
	/// ```
	///
	/// This example uses the same types to prove that raw, bitwise, values are
	/// not used for equality comparison.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let l: BitVec<Msb0, u8> = bitvec![Msb0, u8; 0, 1, 0, 1];
	/// let r: BitVec<Lsb0, u8> = bitvec![Lsb0, u8; 0, 1, 0, 1];
	///
	/// assert_eq!(l, r);
	/// assert_ne!(l.as_slice(), r.as_slice());
	/// ```
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.as_bitslice().eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(*rhs)
	}
}

// impl<A, B, C, D> PartialEq<&mut BitSlice<C, D>> for BitVec<A, B>
// where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
// 	fn eq(&self, rhs: &&mut BitSlice<C, D>) -> bool {
// 		self.as_bitslice().eq(*rhs)
// 	}
// }

impl<A, B, C, D> PartialEq<BitVec<C, D>> for &BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

// impl<A, B, C, D> PartialEq<BitVec<C, D>> for &mut BitSlice<A, B>
// where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
// 	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
// 		(**self).eq(rhs.as_bitslice())
// 	}
// }

/** Compares two `BitVec`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one vector to have a set bit
where the other vector has an unset bit. If the vectors are different, the
vector with the set bit sorts greater than the vector with the unset bit.

If one of the vectors is exhausted before they differ, the longer vector is
greater.
**/
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	/// Performs a comparison by `<` or `>`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: The other vector to compare.
	///
	/// # Returns
	///
	/// The relative ordering of the two vectors.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 0, 0];
	/// let b = bitvec![0, 1, 0, 1];
	/// let c = bitvec![0, 1, 0, 1, 1];
	/// assert!(a < b);
	/// assert!(b < c);
	/// ```
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitVec<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(*rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

// impl<A, B, C, D> PartialOrd<&mut BitSlice<C, D>> for BitVec<A, B>
// where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
// 	fn partial_cmp(&self, rhs: &&mut BitSlice<C, D>) -> Option<Ordering> {
// 		self.as_bitslice().partial_cmp(*rhs)
// 	}
// }

// impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &mut BitSlice<A, B>
// where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
// 	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
// 		(**self).partial_cmp(rhs.as_bitslice())
// 	}
// }

impl<O, T> AsMut<BitSlice<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

/// Gives write access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<O, T> AsMut<[T]> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

impl<O, T> AsRef<BitSlice<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

/// Gives read access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<O, T> AsRef<[T]> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// assert_eq!(&[0, 0b1000_0000], bv.as_slice());
	/// ```
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<O, T> From<&BitSlice<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: &BitSlice<O, T>) -> Self {
		Self::from_bitslice(src)
	}
}

/** Builds a `BitVec` out of a slice of `bool`.

This is primarily for the `bitvec!` macro; it is not recommended for general
use.
**/
impl<O, T> From<&[bool]> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: &[bool]) -> Self {
		src.iter().cloned().collect()
	}
}

impl<O, T> From<BitBox<O, T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: BitBox<O, T>) -> Self {
		Self::from_boxed_bitslice(src)
	}
}

impl<O, T> From<&[T]> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<O, T> From<Box<[T]>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_bitslice(BitBox::from_boxed_slice(src))
	}
}

impl<O, T> Into<Box<[T]>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

/** Builds a `BitVec` out of a `Vec` of elements.

This moves the memory as-is from the source buffer into the new `BitVec`. The
source buffer will be unchanged by this operation, so you don't need to worry
about using the correct order type.
**/
impl<O, T> From<Vec<T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: Vec<T>) -> Self {
		Self::from_vec(src)
	}
}

impl<O, T> Into<Vec<T>> for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn into(self) -> Vec<T> {
		self.into_vec()
	}
}

impl<O, T> Default for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn default() -> Self {
		Self::new()
	}
}

impl<O, T> Binary for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

/** Prints the `BitVec` for debugging.

The output is of the form `BitVec<O, T> [ELT, *]`, where `<O, T>` is the order
and element type, with square brackets on each end of the bits and all the live
elements in the vector printed in binary. The printout is always in semantic
order, and may not reflect the underlying store. To see the underlying store,
use `format!("{:?}", self.as_slice());` instead.

The alternate character `{:#?}` prints each element on its own line, rather than
separated by a space.
**/
impl<O, T> Debug for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Renders the `BitVec` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Lsb0, u16;
	///   0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1
	/// ];
	/// assert_eq!(
	///   "BitVec<Lsb0, u16> [0101000011110101]",
	///   &format!("{:?}", bv)
	/// );
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitVec<")?;
		f.write_str(O::TYPENAME)?;
		f.write_str(", ")?;
		f.write_str(T::TYPENAME)?;
		f.write_str("> ")?;
		Display::fmt(&**self, f)
	}
}

/** Prints the `BitVec` for displaying.

This prints each element in turn, formatted in binary in semantic order (so the
first bit seen is printed first and the last bit seen printed last). Each
element of storage is separated by a space for ease of reading.

The alternate character `{:#}` prints each element on its own line.

To see the in-memory representation, use `AsRef` to get access to the raw
elements and print that slice instead.
**/
impl<O, T> Display for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Renders the `BitVec` contents for display.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![Msb0, u8; 0, 1, 0, 0, 1, 0, 1, 1, 0, 1];
	/// assert_eq!("[01001011, 01]", &format!("{}", bv));
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(&**self, f)
	}
}

impl<O, T> LowerHex for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Octal for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> UpperHex for BitVec<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

/// Writes the contents of the `BitVec`, in semantic bit order, into a hasher.
impl<O, T> Hash for BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Writes each bit of the `BitVec`, as a full `bool`, into the hasher.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `hasher`: The hashing pool into which the vector is written.
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		<BitSlice<O, T> as Hash>::hash(self, hasher)
	}
}

/// `BitVec` is safe to move across thread boundaries, as is `&mut BitVec`.
unsafe impl<O, T> Send for BitVec<O, T>
where O: BitOrder, T: BitStore {}

/// `&BitVec` is safe to move across thread boundaries.
unsafe impl<O, T> Sync for BitVec<O, T>
where O: BitOrder, T: BitStore {}
