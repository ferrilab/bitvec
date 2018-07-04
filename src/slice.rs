/*! `BitSlice` Wide Reference

This module bears some explanation. Let's get *uncomfortable* here.

Safe Rust is very strict about concepts like lifetimes and size in memory. It
won't allow you to have arbitrary *references* to things where Rust doesn't feel
absolutely confident that the referent will outlive the reference, and it won't
let you have things *at all* that it can't size at compile time. This makes
dealing with runtime-sized memory of uncertain lifetime tricky to do, and the
language provides some tools out of the box for this: slice references, which
store a pointer and also a length, and do so in a manner vaguely obscured to the
rest of Rust code behind opaque stdlib types.

My first instinct was to define `BitSlice` as a newtype wrapper around an `&T`,
so that `BitSlice` would be sized and manageable directly. Unfortunately, this
parameterizes the lifetime of the reference into the `BitSlice` struct, making
it generic over a lifetime. When I tried to implement `Deref` on `BitVec` to
return a `BitSlice`, I realized I could not do so for two main reasons: one,
`Deref` requires returning a reference to a type, and it is impossible to tell
Rust "this type is a named reference", and two, ... the lifetime parameter of
`BitSlice` is not able to be provided by the `Deref` trait, the `deref` trait
function, or even by using Higher Ranked Trait Bounds because HRTB just allows
the creation of a lifetime parameter in items in the trait scope that were not
defined with that lifetime parameter, but without Generic Associated Types it is
impossible to add that lifetime parameter to the associated type `Target`!

Also this ran into mutability issues in regards to the interior reference vs the
wrapper.

So `BitSlice` is a newtype wrapper around `[T]`, and can only be touched as a
reference or mutable reference, and has the advantage that now it can be a
`Deref::Target`.

**DO NOT** create an `&BitSlice` yourself! A slice reference can be made to
count bits using `.into()`.
!*/

use super::{
	Bits,
	Endian,
	BigEndian,
	BitVec,
	TRUE,
	FALSE,
};
use std::borrow::ToOwned;
use std::cmp::{
	Eq,
	Ord,
	PartialEq,
	PartialOrd,
	Ordering,
};
use std::convert::{
	AsRef,
	AsMut,
	From,
};
use std::fmt::{
	self,
	Debug,
	Display,
	Formatter,
};
use std::iter::{
	DoubleEndedIterator,
	ExactSizeIterator,
	Iterator,
	IntoIterator,
};
use std::marker::PhantomData;
use std::mem;
use std::ops::{
	BitAndAssign,
	BitOrAssign,
	BitXorAssign,
	Index,
	Not,
	ShlAssign,
	ShrAssign,
};
use std::ptr;
use std::slice;

/** A compact slice of bits, whose cursor and storage type can be customized.

`BitSlice` is a newtype wrapper over `[T]`, and as such can only be held by
reference. It is impossible to create a `Box<BitSlice<E, T>>` from this library,
and assembling one yourself is Undefined Behavior for which this library is not
responsible. **Do not try to create a `Box<BitSlice>`.** If you want an owned
bit collection, use `BitVec`.

`BitSlice` is strictly a reference type. The memory it governs must be owned by
some other type, and a shared or exclusive reference to it as `BitSlice` can be
created by using the `From` implementation on `&BitSlice` and `&mut BitSlice`.

`BitSlice` is to `BitVec` what `[T]` is to `Vec<T>`.

`BitSlice` takes two type parameters.

- `E: Endian` must be an implementor of the `Endian` trait. `BitVec` takes a
  `PhantomData` marker for access to the associated functions, and will never
  make use of an instance of the trait. The default implementations,
  `LittleEndian` and `BigEndian`, are zero-sized, and any further
  implementations should be as well, as the invoked functions will never receive
  state.
- `T: Bits` must be a primitive type. Rust decided long ago to not provide a
  unifying trait over the primitives, so `Bits` provides access to just enough
  properties of the primitives for `BitVec` to use. This trait is sealed against
  downstream implementation, and can only be implemented in this crate.
**/
#[cfg_attr(nightly, repr(transparent))]
pub struct BitSlice<E: Endian = BigEndian, T: Bits = u8> {
	_endian: PhantomData<E>,
	inner: [T],
}

impl<E, T> BitSlice<E, T>
where E: Endian, T: Bits {
	/// Gets the bit value at the given position.
	///
	/// The index value is a semantic count, not a bit address. It converts to a
	/// bit position internally to this function.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![0, 0, 1, 0, 0];
	/// let bits: &BitSlice = &bv;
	/// assert!(bits.get(2));
	/// ```
	pub fn get(&self, index: usize) -> bool {
		assert!(index < self.len(), "Index out of range!");
		let (elt, bit) = T::split(index);
		self.as_ref()[elt].get(E::curr::<T>(bit))
	}

	/// Sets the bit value at the given position.
	///
	/// The index value is a semantic count, not a bit address. It converts to a
	/// bit position internally to this function.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![0; 5];
	/// let bits: &mut BitSlice = &mut bv;
	/// bits.set(2, true);
	/// assert!(bits.get(2));
	/// ```
	pub fn set(&mut self, index: usize, value: bool) {
		assert!(index < self.len(), "Index out of range!");
		let (elt, bit) = T::split(index);
		self.as_mut()[elt].set(E::curr::<T>(bit), value);
	}

	/// Returns the number of bits contained in the `BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1; 10];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.len(), 10);
	/// ```
	pub fn len(&self) -> usize {
		self.inner.len()
	}

	/// Counts how many *whole* storage elements are in the `BitSlice`.
	///
	/// If the `BitSlice` length is not an even multiple of the width of `T`,
	/// then the slice under this `BitSlice` is one element longer than this
	/// method reports, and the number of bits in it are reported by `bits()`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1; 10];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.elts(), 1);
	/// ```
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1; 16];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.elts(), 2);
	/// ```
	pub fn elts(&self) -> usize {
		self.len() >> T::BITS
	}

	/// Counts how many bits are in the trailing partial storage element.
	///
	/// If the `BitSlice` length is an even multiple of the width of `T`, then
	/// this returns 0 and the `BitSlice` does not consider its final element to
	/// be partially used.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1; 10];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.bits(), 2);
	/// ```
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1; 16];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.bits(), 0);
	/// ```
	pub fn bits(&self) -> u8 {
		self.len() as u8 & T::MASK
	}

	/// Returns `true` if the slice contains no bits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![];
	/// let bits: &BitSlice = &bv;
	/// assert!(bits.is_empty());
	/// ```
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![0; 5];
	/// let bits: &BitSlice = &bv;
	/// assert!(!bits.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Provides read-only iteration across the collection.
	///
	/// The iterator returned from this method implements `ExactSizeIterator`
	/// and `DoubleEndedIterator` just as the consuming `.into_iter()` method’s
	/// iterator does.
	pub fn iter<'a>(&'a self) -> Iter<'a, E, T> {
		self.into_iter()
	}

	/// Retrieves a read pointer to the start of the data slice.
	pub(crate) fn as_ptr(&self) -> *const T {
		self.inner.as_ptr()
	}

	/// Retrieves a write pointer to the start of the data slice.
	pub(crate) fn as_mut_ptr(&mut self) -> *mut T {
		self.inner.as_mut_ptr()
	}

	/// Computes the actual length of the data slice, including the partial tail
	/// if any.
	///
	/// # Examples
	///
	/// ```rust,ignore
	/// use bitvec::*;
	/// let bv = bitvec![1; 10];
	/// let bits: &BitSlice = &bv;
	/// assert_eq!(bits.elts(), 1);
	/// assert_eq!(bits.raw_len(), 2);
	/// ```
	pub(crate) fn raw_len(&self) -> usize {
		self.elts() + if self.bits() > 0 { 1 } else { 0 }
	}

	/// Prints a type header into the Formatter.
	pub(crate) fn fmt_header(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(fmt, "BitSlice<{}, {}>", E::TY, T::TY)
	}

	/// Formats the contents data slice.
	///
	/// The debug flag indicates whether to indent each line (`Debug` does,
	/// `Display` does not).
	pub(crate) fn fmt_body(&self, fmt: &mut Formatter, debug: bool) -> fmt::Result {
		let (elts, bits) = T::split(self.len());
		let len = self.raw_len();
		let buf = self.as_ref();
		let alt = fmt.alternate();
		for idx in 0 .. elts {
			Self::fmt_element(fmt, &buf[idx])?;
			if idx < len - 1 {
				match (alt, debug) {
					// {}
					(false, false) => fmt.write_str(" "),
					// {:#}
					(true, false) => writeln!(fmt),
					// {:?}
					(false, true) => fmt.write_str(", "),
					// {:#?}
					(true, true) => { writeln!(fmt, ",")?; fmt.write_str("    ") },
				}?;
			}
		}
		if bits > 0 {
			Self::fmt_bits(fmt, &buf[elts], bits)?;
		}
		Ok(())
	}

	/// Formats a whole storage element of the data slice.
	pub(crate) fn fmt_element(fmt: &mut Formatter, elt: &T) -> fmt::Result {
		Self::fmt_bits(fmt, elt, T::WIDTH)
	}

	/// Formats a partial element of the data slice.
	pub(crate) fn fmt_bits(fmt: &mut Formatter, elt: &T, bits: u8) -> fmt::Result {
		use std::fmt::Write;
		let mut out = String::with_capacity(bits as usize);
		for bit in 0 .. bits {
			let cur = E::curr::<T>(bit);
			write!(out, "{}", if elt.get(cur) { "1" } else { "0" })?;
		}
		fmt.write_str(&out)
	}
}

/// Gives write access to all elements in the underlying storage, including the
/// partially-filled tail element (if present).
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let bytes: &mut [u8] = &mut [5, 10, 15, 20, 25];
/// let bits: &mut BitSlice = bytes.into();
/// for elt in bits.as_mut() {
///   *elt += 2;
/// }
/// assert_eq!(&[7, 12, 17, 22, 27], bits.as_ref());
/// ```
impl<E, T> AsMut<[T]> for BitSlice<E, T>
where E: Endian, T: Bits {
	fn as_mut(&mut self) -> &mut [T] {
		let (ptr, len): (*mut T, usize) = (self.as_mut_ptr(), self.raw_len());
		unsafe { slice::from_raw_parts_mut(ptr, len) }
	}
}

/// Gives read access to all elements in the underlying storage, including the
/// partially-filled tail element (if present).
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let bytes: &[u8] = &[5, 10, 15, 20, 25];
/// let bits: &BitSlice = bytes.into();
/// assert_eq!(&[5, 10, 15, 20, 25], bits.as_ref());
/// ```
impl<E, T> AsRef<[T]> for BitSlice<E, T>
where E: Endian, T: Bits {
	fn as_ref(&self) -> &[T] {
		let (ptr, len): (*const T, usize) = (self.as_ptr(), self.raw_len());
		unsafe { slice::from_raw_parts(ptr, len) }
	}
}

/// Performs the Boolean AND operation against another bitstream and writes the
/// result into `self`. If the other bitstream ends before `self` does, it is
/// extended with zero, clearing all remaining bits in `self`.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let lhs: &mut BitSlice = &mut bitvec![0, 1, 0, 1, 0, 1];
/// let rhs                =      bitvec![0, 0, 1, 1];
/// *lhs &= rhs;
/// assert_eq!("000100", &format!("{}", lhs));
/// ```
impl<E, T, I> BitAndAssign<I> for BitSlice<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	fn bitand_assign(&mut self, rhs: I) {
		use std::iter::repeat;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter().chain(repeat(false))) {
			let val = self.get(idx) & other;
			self.set(idx, val);
		}
	}
}

/// Performs the Boolear OR operation against another bitstream and writes the
/// result into `self`. If the other bitstream ends before `self` does, it is
/// extended with zero, leaving all remaining bits in `self` as they were.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let lhs: &mut BitSlice = &mut bitvec![0, 1, 0, 1, 0, 1];
/// let rhs                =      bitvec![0, 0, 1, 1];
/// *lhs |= rhs;
/// assert_eq!("011101", &format!("{}", lhs));
/// ```
impl<E, T, I> BitOrAssign<I> for BitSlice<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	fn bitor_assign(&mut self, rhs: I) {
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
			let val = self.get(idx) | other;
			self.set(idx, val);
		}
	}
}

/// Performs the Boolean XOR operation against another bitstream and writes the
/// result into `self`. If the other bitstream ends before `self` does, it is
/// extended with zero, leaving all remaining bits in `self` as they were.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let lhs: &mut BitSlice = &mut bitvec![0, 1, 0, 1, 0, 1];
/// let rhs                =      bitvec![0, 0, 1, 1];
/// *lhs ^= rhs;
/// assert_eq!("011001", &format!("{}", lhs));
/// ```
impl<E, T, I> BitXorAssign<I> for BitSlice<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	fn bitxor_assign(&mut self, rhs: I) {
		use std::iter::repeat;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter().chain(repeat(false))) {
			let val = self.get(idx) ^ other;
			self.set(idx, val);
		}
	}
}

/// Prints the `BitSlice` for debugging.
///
/// The output is of the form `BitSlice<E, T> [ELT, *]` where `<E, T>` is the
/// endianness and element type, with square brackets on each end of the bits
/// and all the elements of the array printed in binary. The printout is always
/// in semantic order, and may not reflect the underlying buffer. To see the
/// underlying buffer, use `.as_ref()`.
///
/// The alternate character `{:#?}` prints each element on its own line, rather
/// than having all elements on the same line.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let bits: &BitSlice<LittleEndian, u16> = &bitvec![
///   LittleEndian, u16;
///   0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1,
///   0, 1
/// ];
/// assert_eq!("BitSlice<LittleEndian, u16> [0101000011110101, 01]", &format!("{:?}", bits));
/// ```
impl<E, T> Debug for BitSlice<E, T>
where E: Endian, T: Bits {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let alt = fmt.alternate();
		self.fmt_header(fmt)?;
		fmt.write_str(" [")?;
		if alt { writeln!(fmt)?; }
		self.fmt_body(fmt, true)?;
		if alt { writeln!(fmt)?; }
		fmt.write_str("]")
	}
}

/// Prints the `BitSlice` for displaying.
///
/// This prints each element in turn, formatted in binary in semantic order (so
/// the first bit seen is printed first and the last bit seen is printed last).
/// Each element of storage is separated by a space for ease of reading.
///
/// The alternate character `{:#}` prints each element on its own line.
///
/// To see the in-memory representation, use `.as_ref()` to get access to the
/// raw elements and print that slice instead.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let bits: &BitSlice = &bitvec![0, 1, 0, 0, 1, 0, 1, 1, 0, 1];
/// assert_eq!("01001011 01", &format!("{}", bits));
/// ```
impl<E, T> Display for BitSlice<E, T>
where E: Endian, T: Bits {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.fmt_body(fmt, false)
	}
}

/// Builds a `BitSlice` from a slice of elements. The resulting `BitSlice` will
/// always completely fill the original slice, and will not have a partial tail.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let src = vec![1u8, 2, 3];
/// let borrow: &[u8] = &src;
/// let bits: &BitSlice = borrow.into();
/// assert_eq!(bits.len(), 24);
/// assert_eq!(bits.elts(), 3);
/// assert_eq!(bits.bits(), 0);
/// assert!(bits.get(7));  // src[0] == 0b0000_0001
/// assert!(bits.get(14)); // src[1] == 0b0000_0010
/// assert!(bits.get(22)); // src[2] == 0b0000_0011
/// assert!(bits.get(23));
/// ```
impl<'a, E, T> From<&'a [T]> for &'a BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	fn from(src: &'a [T]) -> Self {
		let (ptr, len): (*const T, usize) = (src.as_ptr(), src.len());
		assert!(len <= T::MAX_ELT, "Source slice length out of range!");
		unsafe {
			mem::transmute(
				slice::from_raw_parts(ptr, len << T::BITS)
			)
		}
	}
}

/// Builds a mutable `BitSlice` from a slice of mutable elements. The resulting
/// `BitSlice` will always completely fill the original slice, and will not have
/// a partial tail.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let mut src = vec![1u8, 2, 3];
/// let borrow: &mut [u8] = &mut src;
/// let bits: &mut BitSlice = borrow.into();
/// assert!(!bits.get(0));
/// bits.set(0, true);
/// assert!(bits.get(0));
/// ```
impl<'a, E, T> From<&'a mut [T]> for &'a mut BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	fn from(src: &'a mut [T]) -> Self {
		let (ptr, len): (*mut T, usize) = (src.as_mut_ptr(), src.len());
		assert!(len <= T::MAX_ELT, "Source slice length out of range!");
		unsafe {
			mem::transmute(
				slice::from_raw_parts_mut(ptr, len << T::BITS)
			)
		}
	}
}

/// Index a single bit by semantic count. The index must be less than the length
/// of the `BitSlice`.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let bv = bitvec![0, 0, 1, 0, 0];
/// let bits: &BitSlice = &bv;
/// assert!(bits[2]);
/// assert!(!bits[3]);
/// ```
impl<'a, E, T> Index<usize> for &'a BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	type Output = bool;

	fn index(&self, index: usize) -> &Self::Output {
		match self.get(index) {
			true => &TRUE,
			false => &FALSE,
		}
	}
}

/// Index a single bit by element and bit index within the element. The element
/// index must be less than the length of the underlying store, and the bit
/// index must be less than the width of the underlying element.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let mut bv = bitvec![0; 10];
/// bv.push(true);
/// let bits: &BitSlice = &bv;
/// assert!(bits[(1, 2)]); // 10
/// assert!(!bits[(1, 1)]); // 9
/// ```
impl<'a, E, T> Index<(usize, u8)> for &'a BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	type Output = bool;

	fn index(&self, (elt, bit): (usize, u8)) -> &Self::Output {
		match self.get(T::join(elt, bit)) {
			true => &TRUE,
			false => &FALSE,
		}
	}
}

/// Produces a read-only iterator over all the bits in the `BitSlice`.
///
/// This iterator follows the ordering in the `BitSlice` type, and implements
/// `ExactSizeIterator` as `BitSlice` has a known, fixed length, and
/// `DoubleEndedIterator` as it has known ends.
impl<'a, E, T> IntoIterator for &'a BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	type Item = bool;
	type IntoIter = Iter<'a, E, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.into()
	}
}

/// Flips all bits in the slice, in place.
///
/// This invokes the `!` operator on each element of the borrowed storage, and
/// so it will also flip bits in the tail that are outside the `BitSlice` length
/// if any. Use `^= repeat(true)` to flip only the bits actually inside the
/// `BitSlice` purview.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let mut bv = bitvec![0; 10];
/// let bits: &mut BitSlice = &mut bv;
/// let new_bits = !bits;
/// //  The `bits` binding is consumed by the `!` operator, and a new reference
/// //  is returned.
/// // assert_eq!(bits.as_ref(), &[!0, !0]);
/// assert_eq!(new_bits.as_ref(), &[!0, !0]);
/// ```
impl<'a, E, T> Not for &'a mut BitSlice<E, T>
where E: Endian, T: 'a + Bits {
	type Output = Self;

	fn not(self) -> Self::Output {
		for elt in self.as_mut() {
			*elt = !*elt;
		}
		self
	}
}

/// Tests if two `BitSlice`s are semantically — not bitwise — equal.
///
/// It is valid to compare two slices of different endianness or element types.
///
/// The equality condition requires that they have the same number of total bits
/// and that each pair of bits in semantic order are identical.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let l: BitVec<LittleEndian, u16> = bitvec![LittleEndian, u16; 0, 1, 0, 1];
/// let r: BitVec<BigEndian, u32> = bitvec![BigEndian, u32; 0, 1, 0, 1];
///
/// let ls: &BitSlice<_, _> = &l;
/// let rs: &BitSlice<_, _> = &r;
/// assert!(ls == rs);
/// ```
impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: Endian, B: Bits, C: Endian, D: Bits {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		let (l, r) = (self.iter(), rhs.iter());
		if l.len() != r.len() {
			return false;
		}
		l.zip(r).all(|(l, r)| l == r)
	}
}

impl<E, T> Eq for BitSlice<E, T>
where E: Endian, T: Bits {}

/// Compares two `BitSlice`s by semantic — not bitwise — ordering.
///
/// The comparison sorts by testing each index for one slice to have a set bit
/// where the other has an unset bit. If the slices are different, the slice
/// with the set bit sorts greater than the slice with the unset bit.
///
/// If one of the slices is exhausted while the inspected part is identical,
/// then the slices sort by length.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let a = bitvec![0, 1, 0, 0];
/// let b = bitvec![0, 1, 0, 1];
/// let c = bitvec![0, 1, 0, 1, 1];
/// let aref: &BitSlice = &a;
/// let bref: &BitSlice = &b;
/// let cref: &BitSlice = &c;
/// assert!(aref < bref);
/// assert!(bref < cref);
/// ```
impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: Endian, B: Bits, C: Endian, D: Bits {
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

impl<E, T> Ord for BitSlice<E, T>
where E: Endian, T: Bits {
	fn cmp(&self, rhs: &Self) -> Ordering {
		match self.partial_cmp(rhs) {
			Some(ord) => ord,
			None => unreachable!("`BitSlice` has a total ordering"),
		}
	}
}

__bitslice_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/// Shifts all bits in the array to the left — DOWN AND TOWARDS THE FRONT.
///
/// On primitives, the left-shift operator `<<` moves bits away from the origin
/// and towards the ceiling. This is because we label the bits in a primitive
/// with the minimum on the right and the maximum on the left, which is
/// big-endian bit order. This increases the value of the primitive being
/// shifted.
///
/// **THAT IS NOT HOW `BitSlice` WORKS!**
///
/// `BitSlice` defines its layout with the minimum on the left and the maximum
/// on the right! Thus, left-shifting moves bits towards the **minimum**.
///
/// In BigEndian order, the effect in memory will be what you expect the `<<`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `>>` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effecs in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The shift amount is modulated against the array length, so it is not an
/// error to pass a shift amount greater than the array length.
///
/// A shift amount of zero is a no-op, and returns immediately.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let mut bv = bitvec![1, 1, 1, 0, 0, 0, 0, 0, 1];
/// let bits: &mut BitSlice = &mut bv;
/// *bits <<= 3;
/// assert_eq!("00000100 0", &format!("{}", bits));
/// //               ^ former tail
/// ```
impl<E, T> ShlAssign<usize> for BitSlice<E, T>
where E: Endian, T: Bits {
	fn shl_assign(&mut self, shamt: usize) {
		let len = self.len();
		//  Bring the shift amount down into the slice's domain.
		let shamt = shamt % len;
		//  If the shift amount was an even multiple of the length, exit.
		if shamt == 0 {
			return;
		}
		//  If the shift amount is an even multiple of the element width, use
		//  ptr::copy instead of a bitwise crawl
		if shamt & T::MASK as usize == 0 {
			//  Compute the shift distance measured in elements.
			let offset = shamt >> T::BITS;
			//  Compute the number of elements that will remain.
			let rem = self.raw_len() - offset;
			//  Memory model: suppose we have this slice of sixteen elements,
			//  that is shifted five elements to the left. We have three
			//  pointers and two lengths to manage.
			//  - rem is 11
			//  - offset is 5
			//  - head is [0]
			//  - body is [5; 11]
			//  - tail is [11]
			//  [ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			//    |         ^---------+---------^  <- before
			//    ^-------------------^ ^-------^  <- zero-filled
			//    after
			//  Pointer to the front of the slice
			let head: *mut T = self.as_mut_ptr();
			//  Pointer to the front of the section that will move and be
			//  retained
			let body: *const T = &self.as_ref()[offset];
			//  Pointer to the back of the slice that will be zero-filled.
			let tail: *mut T = &mut self.as_mut()[rem];
			unsafe {
				ptr::copy(body, head, rem);
				ptr::write_bytes(tail, 0, offset);
			}
			return;
		}
		//  If the shift amount is not an even multiple, do a bitwise crawl and
		//  move bits forward, then zero-fill the back.
		//  Same general logic as above, but bit-level instead of element-level.
		for (to, from) in (shamt .. len).enumerate() {
			let val = self.get(from);
			self.set(to, val);
		}
		for bit in (len - shamt) .. len {
			self.set(bit, false);
		}
	}
}

/// Shifts all bits in the array to the right — UP AND TOWARDS THE BACK.
///
/// On primitives, the right-shift operator `>>` moves bits towards the origin
/// and away from the ceiling. This is because we label the bits in a primitive
/// with the minimum on the right and the maximum on the left, which is
/// big-endian bit order. This decreases the value of the primitive being
/// shifted.
///
/// **THAT IS NOT HOW `BitSlice` WORKS!**
///
/// `BitSlice` defines its layout with the minimum on the left and the maximum
/// on the right! Thus, right-shifting moves bits towards the **maximum**.
///
/// In Big-Endian order, the effect in memory will be what you expect the `>>`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `<<` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effects in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The shift amount is modulated against the array length, so it is not an
/// error to pass a shift amount greater than the array length.
///
/// A shift amount of zero is a no-op, and returns immediately.
///
/// # Examples
///
/// ```rust
/// use bitvec::*;
/// let mut bv = bitvec![1, 0, 0, 0, 0, 0, 1, 1, 1];
/// let bits: &mut BitSlice = &mut bv;
/// *bits >>= 3;
/// assert_eq!("00010000 0", &format!("{}", bits));
/// //             ^ former head
/// ```
impl<E, T> ShrAssign<usize> for BitSlice<E, T>
where E: Endian, T: Bits {
	fn shr_assign(&mut self, shamt: usize) {
		let len = self.len();
		//  Bring the shift amount down into the slice's domain.
		let shamt = shamt % len;
		//  If the shift amount was an even multiple of the length, exit.
		if shamt == 0 {
			return;
		}
		//  If the shift amount is an even multiple of the element width, use
		//  ptr::copy instead of a bitwise crawl.
		if shamt & T::MASK as usize == 0 {
			//  Compute the shift amount measured in elements.
			let offset = shamt >> T::BITS;
			//  Compute the number of elements that will remain.
			let rem = self.raw_len() - offset;
			//  Memory model: suppose we have this slice of sixteen elements,
			//  that is shifted five elements to the right. We have two pointers
			//  and two lengths to manage.
			//  - rem is 11
			//  - offset is 5
			//  - head is [0; 11]
			//  - body is [5]
			//  [ 0 1 2 3 4 5 6 7 8 9 a b c d e f ]
			//    ^---------+---------^         |  <- before
			//    ^-------^ ^-------------------^  <- after
			//    zero-filled
			let head: *mut T = self.as_mut_ptr();
			let body: *mut T = &mut self.as_mut()[offset];
			unsafe {
				ptr::copy(head, body, rem);
				ptr::write_bytes(head, 0, offset);
			}
			return;
		}
		for (from, to) in (shamt .. len).enumerate().rev() {
			let val = self.get(from);
			self.set(to, val);
		}
		for bit in 0 .. shamt {
			self.set(bit, false);
		}
	}
}

/// Clones a borrowed `BitSlice` into an owned `BitVec`.
impl<E, T> ToOwned for BitSlice<E, T>
where E: Endian, T: Bits {
	type Owned = BitVec<E, T>;

	fn to_owned(&self) -> Self::Owned {
		let mut out = Self::Owned::with_capacity(self.len());
		unsafe {
			let src = self.as_ptr();
			let dst = out.as_mut_ptr();
			let len = self.raw_len();
			ptr::copy_nonoverlapping(src, dst, len);
		}
		out
	}
}

/// Permits iteration over a `BitSlice`
#[doc(hidden)]
pub struct Iter<'a, E: 'a + Endian, T: 'a + Bits> {
	inner: &'a BitSlice<E, T>,
	head: usize,
	tail: usize,
}

impl<'a, E: 'a + Endian, T: 'a + Bits> Iter<'a, E, T> {
	fn reset(&mut self) {
		self.head = 0;
		self.tail = self.inner.len();
	}
}

impl<'a, E: 'a + Endian, T: 'a + Bits> DoubleEndedIterator for Iter<'a, E, T> {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.tail > self.head {
			self.tail -= 1;
			Some(self.inner.get(self.tail))
		}
		else {
			self.reset();
			None
		}
	}
}

impl<'a, E: 'a + Endian, T: 'a + Bits> ExactSizeIterator for Iter<'a, E, T> {
	fn len(&self) -> usize {
		self.tail - self.head
	}
}

impl<'a, E: 'a + Endian, T: 'a + Bits> From<&'a BitSlice<E, T>> for Iter<'a, E, T> {
	fn from(src: &'a BitSlice<E, T>) -> Self {
		let len = src.len();
		Self {
			inner: src,
			head: 0,
			tail: len,
		}
	}
}

impl<'a, E: 'a + Endian, T: 'a + Bits> Iterator for Iter<'a, E, T> {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		if self.head < self.tail {
			let ret = self.inner.get(self.head);
			self.head += 1;
			Some(ret)
		}
		else {
			self.reset();
			None
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let rem = ExactSizeIterator::len(self);
		(rem, Some(rem))
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 1, 0, 1, 0];
	/// assert_eq!(bv.iter().count(), 5);
	/// ```
	fn count(self) -> usize {
		ExactSizeIterator::len(&self)
	}

	/// Advances the iterator by `n` bits, starting from zero.
	///
	/// It is not an error to advance past the end of the iterator! Doing so
	/// returns `None`, and resets the iterator to its beginning.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// let mut bv_iter = bv.iter();
	/// assert_eq!(bv_iter.len(), 4);
	/// assert!(bv_iter.nth(3).unwrap());
	/// ```
	///
	/// This example intentionally overshoots the iterator bounds, which causes
	/// a reset to the initiol state. It then demonstrates that `nth` is
	/// stateful, and is not an absolute index, by seeking ahead by two (to the
	/// third zero bit) and then taking the bit immediately after it, which is
	/// set. This shows that the argument to `nth` is how many bits to discard
	/// before yielding the next.
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// let mut bv_iter = bv.iter();
	/// assert!(bv_iter.nth(4).is_none());
	/// assert!(!bv_iter.nth(2).unwrap());
	/// assert!(bv_iter.nth(0).unwrap());
	/// ```
	fn nth(&mut self, n: usize) -> Option<bool> {
		self.head += n;
		self.next()
	}

	/// Consumes the iterator, returning only the last bit.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// assert!(bv.into_iter().last().unwrap());
	/// ```
	///
	/// Empty iterators return `None`
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![];
	/// assert!(bv.into_iter().last().is_none());
	/// ```
	fn last(mut self) -> Option<bool> {
		self.next_back()
	}
}
