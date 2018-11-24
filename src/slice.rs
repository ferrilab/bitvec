/*! `BitSlice` Wide Reference

This module bears some explanation. Let’s get *uncomfortable* here.

Safe Rust is very strict about concepts like lifetimes and size in memory. It
won’t allow you to have arbitrary *references* to things where Rust doesn’t feel
absolutely confident that the referent will outlive the reference, and it won’t
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
Rust "this type is a named reference", and two, … the lifetime parameter of
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

use core::{
	cmp::{
		Eq,
		Ord,
		Ordering,
		PartialEq,
		PartialOrd,
	},
	convert::{
		AsMut,
		AsRef,
		From,
	},
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
	},
	hash::{
		Hash,
		Hasher,
	},
	iter::{
		DoubleEndedIterator,
		ExactSizeIterator,
		Iterator,
		IntoIterator,
	},
	marker::PhantomData,
	mem,
	ops::{
		AddAssign,
		BitAndAssign,
		BitOrAssign,
		BitXorAssign,
		Index,
		Neg,
		Not,
		ShlAssign,
		ShrAssign,
	},
	ptr,
	slice,
};

#[cfg(feature = "std")]
use std::borrow::ToOwned;

#[cfg(not(feature = "std"))]
use alloc::borrow::ToOwned;

/** A compact slice of bits, whose cursor and storage type can be customized.

`BitSlice` is a newtype wrapper over `[T]`, and as such can only be held by
reference. It is impossible to create a `Box<BitSlice<E, T>>` from this library,
and assembling one yourself is Undefined Behavior for which this library is not
responsible. **Do not try to create a `Box<BitSlice>`.** If you want an owned
bit collection, use `BitVec`. (This may change in a future release.)

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
pub struct BitSlice<E = crate::BigEndian, T = u8>
where E: crate::Endian, T: crate::Bits {
	_endian: PhantomData<E>,
	inner: [T],
}

impl<E, T> BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
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

	/// Returns true if *all* bits in the slice are set (logical `∧`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 0
	/// 1 0 => 0
	/// 1 1 => 1
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let all = bitvec![1; 10];
	/// let any = bitvec![0, 0, 1, 0, 0];
	/// let some = bitvec![1, 1, 0, 1, 1];
	/// let none = bitvec![0; 10];
	///
	/// assert!(all.all());
	/// assert!(!any.all());
	/// assert!(!some.all());
	/// assert!(!none.all());
	/// ```
	pub fn all(&self) -> bool {
		//  Gallop the filled elements
		let store = self.as_ref();
		for elt in &store[.. self.elts()] {
			if *elt != T::from(!0) {
				return false;
			}
		}
		//  Walk the partial tail
		let bits = self.bits();
		if bits > 0 {
			let tail = store[self.elts()];
			for bit in 0 .. bits {
				if !tail.get(E::curr::<T>(bit)) {
					return false;
				}
			}
		}
		true
	}

	/// Returns true if *any* bit in the slice is set (logical `∨`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 1
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let all = bitvec![1; 10];
	/// let any = bitvec![0, 0, 1, 0, 0];
	/// let some = bitvec![1, 1, 0, 1, 1];
	/// let none = bitvec![0; 10];
	///
	/// assert!(all.any());
	/// assert!(any.any());
	/// assert!(some.any());
	/// assert!(!none.any());
	/// ```
	pub fn any(&self) -> bool {
		//  Gallop the filled elements
		let store = self.as_ref();
		for elt in &store[.. self.elts()] {
			if *elt != T::from(0) {
				return true;
			}
		}
		//  Walk the partial tail
		let bits = self.bits();
		if bits > 0 {
			let tail = store[self.elts()];
			for bit in 0 .. bits {
				if tail.get(E::curr::<T>(bit)) {
					return true;
				}
			}
		}
		false
	}

	/// Returns true if *any* bit in the slice is unset (logical `¬∧`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 1
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 0
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let all = bitvec![1; 10];
	/// let any = bitvec![0, 0, 1, 0, 0];
	/// let some = bitvec![1, 1, 0, 1, 1];
	/// let none = bitvec![0; 10];
	///
	/// assert!(!all.not_all());
	/// assert!(any.not_all());
	/// assert!(some.not_all());
	/// assert!(none.not_all());
	/// ```
	pub fn not_all(&self) -> bool {
		!self.all()
	}

	/// Returns true if *all* bits in the slice are unset (logical `¬∨`).
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 1
	/// 0 1 => 0
	/// 1 0 => 0
	/// 1 1 => 0
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let all = bitvec![1; 10];
	/// let any = bitvec![0, 0, 1, 0, 0];
	/// let some = bitvec![1, 1, 0, 1, 1];
	/// let none = bitvec![0; 10];
	///
	/// assert!(!all.not_any());
	/// assert!(!any.not_any());
	/// assert!(!some.not_any());
	/// assert!(none.not_any());
	/// ```
	pub fn not_any(&self) -> bool {
		!self.any()
	}

	/// Returns true if some, but not all, bits are set and some, but not all,
	/// are unset.
	///
	/// This is false if either `all()` or `none()` are true.
	///
	/// # Truth Table
	///
	/// ```text
	/// 0 0 => 0
	/// 0 1 => 1
	/// 1 0 => 1
	/// 1 1 => 0
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let all = bitvec![1; 2];
	/// let some = bitvec![1, 0];
	/// let none = bitvec![0; 2];
	///
	/// assert!(!all.some());
	/// assert!(some.some());
	/// assert!(!none.some());
	/// ```
	pub fn some(&self) -> bool {
		self.any() && self.not_all()
	}

	/// Counts how many bits are set high.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1, 0, 1, 0, 1];
	/// assert_eq!(bv.count_ones(), 3);
	/// ```
	pub fn count_ones(&self) -> usize {
		self.into_iter().filter(|b| *b).count()
	}

	/// Counts how many bits are set low.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![0, 1, 0, 1, 0];
	/// assert_eq!(bv.count_zeros(), 3);
	/// ```
	pub fn count_zeros(&self) -> usize {
		self.into_iter().filter(|b| !b).count()
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
	pub fn iter(&self) -> Iter<E, T> {
		self.into_iter()
	}

	/// Provides mutable traversal of the collection.
	///
	/// It is impossible to implement `IndexMut` on `BitSlice` because bits do
	/// not have addresses, so there can be no `&mut u1`. This method allows the
	/// client to receive an enumerated bit, and provide a new bit to set at
	/// each index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![1; 8];
	/// let bref: &mut BitSlice = &mut bv;
	/// bref.for_each(|idx, bit| {
	///     if idx % 2 == 0 {
	///         !bit
	///     }
	///     else {
	///         bit
	///     }
	/// });
	/// assert_eq!(&[0b01010101], bref.as_ref());
	/// ```
	pub fn for_each<F>(&mut self, op: F)
	where F: Fn(usize, bool) -> bool {
		for idx in 0 .. self.len() {
			let tmp = self.get(idx);
			self.set(idx, op(idx, tmp));
		}
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
	/// if present.
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
		for (idx, elt) in buf.iter().take(elts).enumerate() {
			Self::fmt_element(fmt, elt)?;
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
		use core::fmt::Write;

		#[cfg(not(feature = "std"))]
		use alloc::string::String;

		let mut out = String::with_capacity(bits as usize);
		for bit in 0 .. bits {
			let cur = E::curr::<T>(bit);
			out.write_str(if elt.get(cur) { "1" } else { "0" })?;
		}
		fmt.write_str(&out)
	}
}

/// Creates a new `BitVec` out of a `BitSlice`.
impl<E, T> ToOwned for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	type Owned = crate::BitVec<E, T>;

	/// Clones a borrowed `BitSlice` into an owned `BitVec`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let src = bitvec![0; 5];
	/// let src_ref: &BitSlice = &src;
	/// let dst = src_ref.to_owned();
	/// assert_eq!(src, dst);
	/// ```
	fn to_owned(&self) -> Self::Owned {
		let mut out = Self::Owned::with_capacity(self.len());
		unsafe {
			let src = self.as_ptr();
			let dst = out.as_mut_ptr();
			let len = self.raw_len();
			ptr::copy_nonoverlapping(src, dst, len);
			out.set_len(self.len());
		}
		out
	}
}

impl<E, T> Eq for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {}

impl<E, T> Ord for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	fn cmp(&self, rhs: &Self) -> Ordering {
		match self.partial_cmp(rhs) {
			Some(ord) => ord,
			None => unreachable!("`BitSlice` has a total ordering"),
		}
	}
}

/// Tests if two `BitSlice`s are semantically — not bitwise — equal.
///
/// It is valid to compare two slices of different endianness or element types.
///
/// The equality condition requires that they have the same number of total bits
/// and that each pair of bits in semantic order are identical.
impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: crate::Endian, B: crate::Bits, C: crate::Endian, D: crate::Bits {
	/// Performs a comparison by `==`.
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
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		let (l, r) = (self.iter(), rhs.iter());
		if l.len() != r.len() {
			return false;
		}
		l.zip(r).all(|(l, r)| l == r)
	}
}

/// Compares two `BitSlice`s by semantic — not bitwise — ordering.
///
/// The comparison sorts by testing each index for one slice to have a set bit
/// where the other has an unset bit. If the slices are different, the slice
/// with the set bit sorts greater than the slice with the unset bit.
///
/// If one of the slices is exhausted before they differ, the longer slice is
/// greater.
impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: crate::Endian, B: crate::Bits, C: crate::Endian, D: crate::Bits {
	/// Performs a comparison by `<` or `>`.
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

/// Gives write access to all elements in the underlying storage, including the
/// partially-filled tail element (if present).
impl<E, T> AsMut<[T]> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Accesses the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv: BitVec = bitvec![0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// for elt in bv.as_mut() {
	///   *elt += 2;
	/// }
	/// assert_eq!(&[2, 130], bv.as_ref());
	/// ```
	fn as_mut(&mut self) -> &mut [T] {
		let (ptr, len): (*mut T, usize) = (self.as_mut_ptr(), self.raw_len());
		unsafe { slice::from_raw_parts_mut(ptr, len) }
	}
}

/// Gives read access to all elements in the underlying storage, including the
/// partially-filled tail element (if present).
impl<E, T> AsRef<[T]> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Accesses the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// let bref: &BitSlice = &bv;
	/// assert_eq!(&[0, 0b1000_0000], bref.as_ref());
	/// ```
	fn as_ref(&self) -> &[T] {
		let (ptr, len): (*const T, usize) = (self.as_ptr(), self.raw_len());
		unsafe { slice::from_raw_parts(ptr, len) }
	}
}

/// Builds a `BitSlice` from a slice of elements. The resulting `BitSlice` will
/// always completely fill the original slice, and will not have a partial tail.
impl<'a, E, T> From<&'a [T]> for &'a BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	/// Wraps an `&[T: Bits]` in an `&BitSlice<E: Endian, T>`. The endianness
	/// must be specified by the call site. The element type cannot be changed.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let src = vec![1u8, 2, 3];
	/// let borrow: &[u8] = &src;
	/// let bits: &BitSlice<BigEndian, _> = borrow.into();
	/// assert_eq!(bits.len(), 24);
	/// assert_eq!(bits.elts(), 3);
	/// assert_eq!(bits.bits(), 0);
	/// assert!(bits.get(7));  // src[0] == 0b0000_0001
	/// assert!(bits.get(14)); // src[1] == 0b0000_0010
	/// assert!(bits.get(22)); // src[2] == 0b0000_0011
	/// assert!(bits.get(23));
	/// ```
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
impl<'a, E, T> From<&'a mut [T]> for &'a mut BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	/// Wraps an `&mut [T: Bits]` in an `&mut BitSlice<E: Endian, T>`. The
	/// endianness must be specified by the call site. The element type cannot
	/// be changed.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut src = vec![1u8, 2, 3];
	/// let borrow: &mut [u8] = &mut src;
	/// let bits: &mut BitSlice<LittleEndian, _> = borrow.into();
	/// //  The first bit read is the LSb of the first element, which is set.
	/// assert!(bits.get(0));
	/// bits.set(0, false);
	/// assert!(!bits.get(0));
	/// ```
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
impl<E, T> Debug for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Renders the `BitSlice` type header and contents for debug.
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
	/// assert_eq!(
    ///     "BitSlice<LittleEndian, u16> [0101000011110101, 01]",
	///     &format!("{:?}", bits)
	/// );
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let alt = fmt.alternate();
		self.fmt_header(fmt)?;
		fmt.write_str(" [")?;
		if alt { writeln!(fmt)?; fmt.write_str("    ")?; }
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
impl<E, T> Display for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Renders the `BitSlice` contents for display.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bits: &BitSlice = &bitvec![0, 1, 0, 0, 1, 0, 1, 1, 0, 1];
	/// assert_eq!("01001011 01", &format!("{}", bits));
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.fmt_body(fmt, false)
	}
}

/// Writes the contents of the `BitSlice`, in semantic bit order, into a hasher.
impl<E, T> Hash for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Writes each bit of the `BitSlice`, as a full `bool`, into the hasher.
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		for bit in self {
			hasher.write_u8(bit as u8);
		}
	}
}

/// Produces a read-only iterator over all the bits in the `BitSlice`.
///
/// This iterator follows the ordering in the `BitSlice` type, and implements
/// `ExactSizeIterator` as `BitSlice` has a known, fixed length, and
/// `DoubleEndedIterator` as it has known ends.
impl<'a, E, T> IntoIterator for &'a BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	type Item = bool;
	type IntoIter = Iter<'a, E, T>;

	/// Iterates over the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![1, 0, 1, 0, 1, 1, 0, 0];
	/// let bref: &BitSlice = &bv;
	/// let mut count = 0;
	/// for bit in bref {
	///     if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		self.into()
	}
}

/// Performs unsigned addition in place on a `BitSlice`.
///
/// If the addend `BitSlice` is shorter than `self`, the addend is zero-extended
/// at the left (so that its final bit matches with `self`’s final bit). If the
/// addend is longer, the excess front length is unused.
///
/// Addition proceeds from the right ends of each slice towards the left.
/// Because this trait is forbidden from returning anything, the final carry-out
/// bit is discarded.
///
/// Note that, unlike `BitVec`, there is no subtraction implementation until I
/// find a subtraction algorithm that does not require modifying the subtrahend.
///
/// Subtraction can be implemented by negating the intended subtrahend yourself
/// and then using addition, or by using `BitVec`s instead of `BitSlice`s.
impl<'a, E, T> AddAssign<&'a BitSlice<E, T>> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Performs unsigned wrapping addition in place.
	///
	/// # Examples
	///
	/// This example shows addition of a slice wrapping from MAX to zero.
	///
	/// ```rust
	/// use bitvec::*;
	/// let nums: [BitVec; 3] = [
	///     bitvec![1, 1, 1, 0],
	///     bitvec![1, 1, 1, 1],
	///     bitvec![0, 0, 0, 0],
	/// ];
	/// let one = bitvec![0, 1];
	/// let mut num = nums[0].clone();
	/// let numr: &mut BitSlice = &mut num;
	/// *numr += &one;
	/// assert_eq!(numr, &nums[1] as &BitSlice);
	/// *numr += &one;
	/// assert_eq!(numr, &nums[2] as &BitSlice);
	/// ```
	fn add_assign(&mut self, addend: &'a BitSlice<E, T>) {
		use core::iter::repeat;
		//  zero-extend the addend if it’s shorter than self
		let mut addend_iter = addend.into_iter().rev().chain(repeat(false));
		let mut c = false;
		for place in (0 .. self.len()).rev() {
			//  See `BitVec::AddAssign`
			static JUMP: [u8; 8] = [0, 2, 2, 1, 2, 1, 1, 3];
			let a = self.get(place);
			let b = addend_iter.next().unwrap(); // addend is an infinite source
			let idx = ((c as u8) << 2) | ((a as u8) << 1) | (b as u8);
			let yz = JUMP[idx as usize];
			let (y, z) = (yz & 2 != 0, yz & 1 != 0);
			self.set(place, y);
			c = z;
		}
	}
}

/// Performs the Boolean `AND` operation against another bitstream and writes
/// the result into `self`. If the other bitstream ends before `self` does, it
/// is extended with zero, clearing all remaining bits in `self`.
impl<E, T, I> BitAndAssign<I> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits, I: IntoIterator<Item=bool> {
	/// `AND`s a bitstream into a slice.
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
	fn bitand_assign(&mut self, rhs: I) {
		use core::iter::repeat;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter().chain(repeat(false))) {
			let val = self.get(idx) & other;
			self.set(idx, val);
		}
	}
}

/// Performs the Boolean `OR` operation against another bitstream and writes the
/// result into `self`. If the other bitstream ends before `self` does, it is
/// extended with zero, leaving all remaining bits in `self` as they were.
impl<E, T, I> BitOrAssign<I> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits, I: IntoIterator<Item=bool> {
	/// `OR`s a bitstream into a slice.
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
	fn bitor_assign(&mut self, rhs: I) {
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
			let val = self.get(idx) | other;
			self.set(idx, val);
		}
	}
}

/// Performs the Boolean `XOR` operation against another bitstream and writes
/// the result into `self`. If the other bitstream ends before `self` does, it
/// is extended with zero, leaving all remaining bits in `self` as they were.
impl<E, T, I> BitXorAssign<I> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits, I: IntoIterator<Item=bool> {
	/// `XOR`s a bitstream into a slice.
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
	fn bitxor_assign(&mut self, rhs: I) {
		use core::iter::repeat;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter().chain(repeat(false))) {
			let val = self.get(idx) ^ other;
			self.set(idx, val);
		}
	}
}

/// Indexes a single bit by semantic count. The index must be less than the
/// length of the `BitSlice`.
impl<'a, E, T> Index<usize> for &'a BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	type Output = bool;

	/// Looks up a single bit by semantic count.
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
	fn index(&self, index: usize) -> &Self::Output {
		if self.get(index) { &true} else { &false }
	}
}

/// Indexes a single bit by element and bit index within the element. The
/// element index must be less than the length of the underlying store, and the
/// bit index must be less than the width of the underlying element.
///
/// This index is not recommended for public use.
impl<'a, E, T> Index<(usize, u8)> for &'a BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	type Output = bool;

	/// Looks up a single bit by storage element and bit indices. The bit index
	/// is still a semantic count, not an absolute index into the element.
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
	fn index(&self, (elt, bit): (usize, u8)) -> &Self::Output {
		if self.get(T::join(elt, bit)) { &true } else { &false }
	}
}

/// Performs fixed-width 2’s-complement negation of a `BitSlice`.
///
/// Unlike the `!` operator (`Not` trait), the unary `-` operator treats the
/// `BitSlice` as if it represents a signed 2’s-complement integer of fixed
/// width. The negation of a number in 2’s complement is defined as its
/// inversion (using `!`) plus one, and on fixed-width numbers has the following
/// discontinuities:
///
/// - A slice whose bits are all zero is considered to represent the number zero
///   which negates as itself.
/// - A slice whose bits are all one is considered to represent the most
///   negative number, which has no correpsonding positive number, and thus
///   negates as zero.
///
/// This behavior was chosen so that all possible values would have *some*
/// output, and so that repeated application converges at idempotence. The most
/// negative input can never be reached by negation, but `--MOST_NEG` converges
/// at the least unreasonable fallback value, 0.
///
/// Because `BitSlice` cannot move, the negation is performed in place.
impl<'a, E, T> Neg for &'a mut BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	type Output = Self;

	/// Perform 2’s-complement fixed-width negation.
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
	/// use bitvec::*;
	/// let mut num = bitvec![0, 1, 1, 0];
	/// - (&mut num as &mut BitSlice);
	/// assert_eq!(num, bitvec![1, 0, 1, 0]);
	/// ```
	///
	/// Negate an arbitrary negative number. This example will use the above
	/// result to demonstrate round-trip correctness.
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut num = bitvec![1, 0, 1, 0];
	/// - (&mut num as &mut BitSlice);
	/// assert_eq!(num, bitvec![0, 1, 1, 0]);
	/// ```
	///
	/// Negate the most negative number, which will become zero, and show
	/// convergence at zero.
	///
	/// ```rust
	/// use bitvec::*;
	/// let zero = bitvec![0; 10];
	/// let mut num = bitvec![1; 10];
	/// - (&mut num as &mut BitSlice);
	/// assert_eq!(num, zero);
	/// - (&mut num as &mut BitSlice);
	/// assert_eq!(num, zero);
	/// ```
	fn neg(self) -> Self::Output {
		if self.is_empty() || self.not_any() {
			return self;
		}
		let _ = Not::not(&mut *self);
		//  Fill an element with all 1 bits
		let elt: [T; 1] = [!T::default()];
		if self.any() {
			//  Turn a slice reference `[T; 1]` into a bit-slice reference
			//  `[u1; 1]`
			let addend: &BitSlice<E, T> = {
				unsafe { mem::transmute::<&[T], &BitSlice<E, T>>(&elt) }
			};
			//  And add it (if the slice was not all-ones).
			AddAssign::add_assign(&mut *self, addend);
		}
		self
	}
}

/// Flips all bits in the slice, in place.
///
/// This invokes the `!` operator on each element of the borrowed storage, and
/// so it will also flip bits in the tail that are outside the `BitSlice` length
/// if any. Use `^= repeat(true)` to flip only the bits actually inside the
/// `BitSlice` purview. `^=` also has the advantage of being a borrowing
/// operator rather than a consuming/returning operator.
impl<'a, E, T> Not for &'a mut BitSlice<E, T>
where E: crate::Endian, T: 'a + crate::Bits {
	type Output = Self;

	/// Inverts all bits in the slice.
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
	fn not(self) -> Self::Output {
		for elt in self.as_mut() {
			*elt = !*elt;
		}
		self
	}
}

__bitslice_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/// Shifts all bits in the array to the left — **DOWN AND TOWARDS THE FRONT**.
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
impl<E, T> ShlAssign<usize> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Shifts a slice left, in place.
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
			//              ^-------before------^
			//    ^-------after-------^ 0 0 0 0 0
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

/// Shifts all bits in the array to the right — **UP AND TOWARDS THE BACK**.
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
impl<E, T> ShrAssign<usize> for BitSlice<E, T>
where E: crate::Endian, T: crate::Bits {
	/// Shifts a slice right, in place.
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
			//    ^-------before------^
			//    0 0 0 0 0 ^-------after-------^
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

/// Permits iteration over a `BitSlice`
#[doc(hidden)]
pub struct Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
	inner: &'a BitSlice<E, T>,
	head: usize,
	tail: usize,
}

impl<'a, E, T> Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
	fn reset(&mut self) {
		self.head = 0;
		self.tail = self.inner.len();
	}
}

impl<'a, E, T> DoubleEndedIterator for Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
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

impl<'a, E, T> ExactSizeIterator for Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
	fn len(&self) -> usize {
		self.tail - self.head
	}
}

impl<'a, E, T> From<&'a BitSlice<E, T>> for Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
	fn from(src: &'a BitSlice<E, T>) -> Self {
		let len = src.len();
		Self {
			inner: src,
			head: 0,
			tail: len,
		}
	}
}

impl<'a, E, T> Iterator for Iter<'a, E, T>
where E: 'a + crate::Endian, T: 'a + crate::Bits {
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
	/// a reset to the initial state. It then demonstrates that `nth` is
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
		self.head = self.head.saturating_add(n);
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
