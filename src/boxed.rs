/*! `BitBox` structure

This module holds the type for an owned but ungrowable bit sequence. `BitVec` is
the more appropriate and useful type for most collections.
!*/

#![cfg(any(feature = "alloc", feature = "std"))]

use crate::{
	cursor::{
		Cursor,
		Local,
	},
	pointer::BitPtr,
	slice::BitSlice,
	store::{
		BitStore,
		Word,
	},
	vec::BitVec,
};

#[cfg(feature = "alloc")]
use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
	},
	boxed::Box,
	vec::Vec,
};

use core::{
	cmp::Ordering,
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
	iter::FusedIterator,
	marker::PhantomData,
	mem,
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
	},
};

/** A pointer type for owned bit sequences.

This type is essentially a `&BitSlice` that owns its own memory. It can change
the contents of its domain, but it cannot change its own domain like `BitVec`
can. It is useful for fixed-size collections without lifetime tracking.

# Type Parameters

- `C: Cursor`: An implementor of the [`Cursor`] trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the [`BitStore`] trait: `u8`, `u16`, `u32`,
  or `u64` (64-bit systems only). This is the actual type in memory that the box
  will use to store data.

# Safety

The `BitBox` handle has the same *size* as standard Rust `Box<[T]>` handles, but
it is ***extremely binary incompatible*** with them. Attempting to treat
`BitBox<_, T>` as `Box<[T]>` in any manner except through the provided APIs is
***catastrophically*** unsafe and unsound.

# Trait Implementations

`BitBox<C, T>` implements all the traits that `BitSlice<C, T>` does, by
deferring to the `BitSlice` implementation. It also implements conversion traits
to and from `BitSlice`, and to/from `BitVec`.
**/
#[repr(C)]
pub struct BitBox<C = Local, T = Word>
where C: Cursor, T: BitStore {
	_cursor: PhantomData<C>,
	pointer: BitPtr<T>,
}

impl<C, T> BitBox<C, T>
where C: Cursor, T: BitStore {
	/// Constructs an empty boxed bitslice.
	///
	/// # Returns
	///
	/// An empty `BitBox` at an arbitrary location.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox = BitBox::empty();
	/// assert!(bb.is_empty());
	/// ```
	pub fn empty() -> Self {
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::empty(),
		}
	}

	/// Produces a `BitBox` from a single element.
	///
	/// # Parameters
	///
	/// - `elt`: The source element from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bb: BitBox<BigEndian, u16> = BitBox::from_element(!0);
	/// assert!(bb.all());
	/// ```
	pub fn from_element(elt: T) -> Self {
		BitSlice::<C, T>::from_element(&elt).into()
	}

	/// Builds a `BitBox` from a borrowed slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` containing the (cloned) provided slice.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [5, 10];
	/// let bb: BitBox<BigEndian, u8> = BitBox::from_slice(&src[..]);
	/// assert!(bb[5]);
	/// assert!(bb[7]);
	/// assert!(bb[12]);
	/// assert!(bb[14]);
	/// ```
	pub fn from_slice(slice: &[T]) -> Self {
		BitVec::from_slice(slice).into_boxed_bitslice()
	}

	/// Clones a `&BitSlice` into a `BitBox`.
	///
	/// # Parameters
	///
	/// - `slice`: The bit slice to clone into a bit box.
	///
	/// # Returns
	///
	/// A `BitBox` containing the same bits as the source slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, !0];
	/// let bb = BitBox::<BigEndian, _>::from_bitslice(src.bits());
	/// assert_eq!(bb.len(), 16);
	/// assert!(bb.some());
	/// ```
	pub fn from_bitslice(slice: &BitSlice<C, T>) -> Self {
		BitVec::from_bitslice(slice).into_boxed_bitslice()
	}

	/// Produces a `BitBox` from an owned slice of elements.
	///
	/// # Parameters
	///
	/// - `slice`: The source boxed slice from which to make the `BitBox`.
	///
	/// # Returns
	///
	/// A `BitBox` governing the same slice that was passed in. This function
	/// does not reallocate.
	///
	/// # Panics
	///
	/// This function may panic if the provided slice is longer than the
	/// `BitBox` can support.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<LittleEndian, _>::from_boxed_slice(slice);
	/// assert!(bb.some());
	/// assert_eq!(bb.len(), 32);
	/// ```
	pub fn from_boxed_slice(boxed: Box<[T]>) -> Self {
		let len = boxed.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitBox cannot address {} elements",
			len,
		);

		let bs = BitSlice::<C, T>::from_slice(&boxed[..]);
		let pointer = bs.bitptr();
		let out = Self {
			_cursor: PhantomData,
			pointer,
		};
		mem::forget(boxed);
		out
	}

	/// Removes the `BitBox` wrapper from a `Box<[T]>`.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The `Box<[T]>` underneath `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let slice: Box<[u16]> = vec![0, !0].into_boxed_slice();
	/// let bb = BitBox::<LittleEndian, _>::from_boxed_slice(slice);
	/// assert_eq!(bb.len(), 32);
	/// let slice = bb.into_boxed_slice();
	/// assert_eq!(slice.len(), 2);
	/// ```
	pub fn into_boxed_slice(self) -> Box<[T]> {
		let slice = self.pointer.as_mut_slice();
		let (data, elts) = (slice.as_mut_ptr(), slice.len());
		let out = unsafe { Vec::from_raw_parts(data, elts, elts) }
			.into_boxed_slice();
		mem::forget(self);
		out
	}

	/// Constructs a `BitBox` from a raw `BitPtr`.
	///
	/// After calling this function, the raw pointer is owned by the resulting
	/// `BitBox`. The `BitBox` will deallocate the memory region it describes.
	///
	/// # Parameters
	///
	/// - `pointer`: A `BitPtr<T>` describing a region of owned memory. This
	///   must have previously produced by `BitBox` constructors; it is unsound
	///   to even pass in `BitPtr<T>` values taken from `BitVec<C, T>` handles.
	///
	/// # Returns
	///
	/// An owned `BitBox` over the given pointer.
	///
	/// # Safety
	///
	/// Because Rust does not specify the allocation scheme used, the only
	/// valid pointer to pass into this function is one that had previously been
	/// produced by `BitBox` constructors and extracted by [`BitBox::into_raw`].
	///
	/// This function is unsafe because improper use can lead to double-free
	/// errors (constructing multiple `BitBox`es from the same `BitPtr`) or
	/// allocator inconsistencies (arbitrary pointers).
	///
	/// [`BitBox::into_raw`]: #method.into_raw
	pub unsafe fn from_raw(pointer: BitPtr<T>) -> Self {
		Self {
			_cursor: PhantomData,
			pointer,
		}
	}

	/// Consumes the `BitBox`, returning the wrapped `BitPtr` directly.
	///
	/// After calling this function, the caller is responsible for the memory
	/// previously managed by the `BitBox`. In particular, the caller must
	/// properly release the memory region to which the `BitPtr` refers.
	/// The proper way to do so is to convert the `BitPtr` back into a `BitBox`
	/// with the [`BitBox::from_raw`] function.
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub unsafe fn into_raw(self) -> BitPtr<T> {
		let out = self.bitptr();
		mem::forget(self);
		out
	}

	/// Consumes and leaks the `BitBox`, returning a mutable reference,
	/// `&'a mut BitSlice<C, T>`. Note that the memory region `[T]` must outlive
	/// the chosen lifetime `'a`.
	///
	/// This function is mainly useful for bit regions that live for the
	/// remainder of the program’s life. Dropping the returned reference will
	/// cause a memory leak. If this is not acceptable, the reference should
	/// first be wrapped with the [`Box::from_raw`] function, producing a
	/// `BitBox`. This `BitBox` can then be dropped which will properly
	/// deallocate the memory.
	///
	/// # Parameters
	///
	/// - `b`: The `BitBox` to deconstruct.
	///
	/// # Returns
	///
	/// The slice formerly governed by the `BitBox`, which will never
	/// deallocate.
	///
	/// [`BitBox::from_raw`]: #method.from_raw
	pub fn leak<'a>(self) -> &'a mut BitSlice<C, T> {
		let out = self.bitptr();
		mem::forget(self);
		out.into_bitslice_mut()
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This delegates to `BitSlice::add_assign_reverse`.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `addend: impl IntoIterator<Item=bool>`: A bitstream to add to `self`.
	///
	/// # Returns
	///
	/// The sum of `self` and `addend`.
	pub fn add_reverse<I>(mut self, addend: I) -> Self
	where I: IntoIterator<Item=bool> {
		self.add_assign_reverse(addend);
		self
	}

	/// Changes the cursor on a box handle, without changing the data it
	/// governs.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An equivalent handle to the same data, with a new cursor parameter.
	pub fn change_cursor<D>(self) -> BitBox<D, T>
	where D: Cursor {
		let bp = self.bitptr();
		mem::forget(self);
		unsafe { BitBox::from_raw(bp) }
	}

	/// Accesses the `BitSlice<C, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_bitslice(&self) -> &BitSlice<C, T> {
		self.pointer.into_bitslice()
	}

	/// Accesses the `BitSlice<C, T>` to which the `BitBox` refers.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The slice of bits behind the box.
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<C, T> {
		self.pointer.into_bitslice_mut()
	}

	/// Accesses the vector’s backing store as an element slice.
	///
	/// Unlike `BitSlice`’s method of the same name, this includes the partial
	/// edges, as `BitBox` forbids fragmentation that leads to contention.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The slice of all live elements in the backing storage, including the
	/// partial edges if present.
	pub fn as_slice(&self) -> &[T] {
		self.bitptr().as_slice()
	}

	/// Accesses the vector’s backing store as an element slice.
	///
	/// Unlike `BitSlice`’s method of the same name, this includes the partial
	/// edges, as `BitBox` forbids fragmentation that leads to contention.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The slice of all live elements in the backing storage, including the
	/// partial edges if present.
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		self.bitptr().as_mut_slice()
	}

	/// Gives read access to the `BitPtr<T>` structure powering the box.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A copy of the interior `BitPtr<T>`.
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.pointer
	}

	/// Allows a function to access the `Box<[T]>` that the `BitBox` is using
	/// under the hood.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `func`: A function which works with a borrowed `Box<[T]>` representing
	///   the actual memory held by the `BitBox`.
	///
	/// # Type Parameters
	///
	/// - `F: FnOnce(&Box<[T]>) -> R`: A function which borrows a box.
	/// - `R`: The return value of the function.
	///
	/// # Returns
	///
	/// The return value of the provided function.
	fn do_with_box<F, R>(&self, func: F) -> R
	where F: FnOnce(&Box<[T]>) -> R {
		let slice = self.pointer.as_mut_slice();
		let (data, elts) = (slice.as_mut_ptr(), slice.len());
		let b: Box<[T]> = unsafe {
			Vec::from_raw_parts(data, elts, elts)
		}.into_boxed_slice();
		let out = func(&b);
		mem::forget(b);
		out
	}
}

impl<C, T> Borrow<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow(&self) -> &BitSlice<C, T> {
		self.as_bitslice()
	}
}

impl<C, T> BorrowMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_mut_bitslice()
	}
}

impl<C, T> Clone for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn clone(&self) -> Self {
		let new_box = self.do_with_box(Clone::clone);
		let mut pointer = self.pointer;
		unsafe { pointer.set_pointer(new_box.as_ptr()); }
		mem::forget(new_box);
		Self {
			_cursor: PhantomData,
			pointer,
		}
	}
}

impl<C, T> Eq for BitBox<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bitslice().cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.as_bitslice().eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

impl<C, T> AsMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_mut_bitslice()
	}
}

impl<C, T> AsMut<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_bitslice().as_mut()
	}
}

impl<C, T> AsRef<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.as_bitslice()
	}
}

impl<C, T> AsRef<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_bitslice().as_ref()
	}
}

impl<C, T> From<&BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<C, T> From<&[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<C, T> From<BitVec<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: BitVec<C, T>) -> Self {
		src.into_boxed_bitslice()
	}
}

impl<C, T> From<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_slice(src)
	}
}

impl<C, T> Into<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<C, T> Default for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn default() -> Self {
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::default(),
		}
	}
}

impl<C, T> Debug for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitBox<")?;
		f.write_str(C::TYPENAME)?;
		f.write_str(", ")?;
		f.write_str(T::TYPENAME)?;
		f.write_str("> ")?;
		Display::fmt(self.as_bitslice(), f)
	}
}

impl<C, T> Display for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bitslice(), f)
	}
}

impl<C, T> Hash for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		self.as_bitslice().hash(hasher)
	}
}

impl<C, T> IntoIterator for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;
	type IntoIter = IntoIter<C, T>;

	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			region: self.bitptr(),
			bitbox: self,
		}
	}
}

impl<'a, C, T> IntoIterator for &'a BitBox<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = <&'a BitSlice<C, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		self.as_bitslice().into_iter()
	}
}

/// `BitBox` is safe to move across thread boundaries, as is `&mut BitBox`.
unsafe impl<C, T> Send for BitBox<C, T>
where C: Cursor, T: BitStore {}

/// `&BitBox` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitBox<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Add<Self> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

impl<C, T> AddAssign for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn add_assign(&mut self, addend: Self) {
		self.as_mut_bitslice().add_assign(addend.as_bitslice().iter().copied())
	}
}

impl<C, T, I> BitAnd<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

impl<C, T, I> BitAndAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitand_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitand_assign(rhs);
	}
}

impl<C, T, I> BitOr<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

impl<C, T, I> BitOrAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitor_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitor_assign(rhs);
	}
}

impl<C, T, I> BitXor<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

impl<C, T, I> BitXorAssign<I> for BitBox<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitxor_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitxor_assign(rhs);
	}
}

impl<C, T> Deref for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Target = BitSlice<C, T>;

	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

impl<C, T> DerefMut for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

impl<C, T> Drop for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn drop(&mut self) {
		let ptr = self.as_mut_slice().as_mut_ptr();
		let len = self.as_slice().len();
		//  Run the `Box<[T]>` destructor.
		drop(unsafe { Vec::from_raw_parts(ptr, 0, len) }.into_boxed_slice());
	}
}

impl<C, T> Index<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = bool;

	fn index(&self, index: usize) -> &Self::Output {
		&self.as_bitslice()[index]
	}
}

impl<C, T> Index<Range<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: Range<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<Range<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeFrom<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeFrom<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeFull> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self.as_bitslice()
	}
}

impl<C, T> IndexMut<RangeFull> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self.as_mut_bitslice()
	}
}

impl<C, T> Index<RangeInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeTo<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeTo<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeTo<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeToInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeToInclusive<usize>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(
		&mut self,
		range: RangeToInclusive<usize>,
	) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Neg for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().neg();
		self
	}
}

impl<C, T> Not for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn not(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().not();
		self
	}
}

impl<C, T> Shl<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

impl<C, T> ShlAssign<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn shl_assign(&mut self, shamt: usize) {
		self.as_mut_bitslice().shl_assign(shamt);
	}
}

impl<C, T> Shr<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

impl<C, T> ShrAssign<usize> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn shr_assign(&mut self, shamt: usize) {
		self.as_mut_bitslice().shr_assign(shamt);
	}
}

/** State keeper for consuming iteration over a `BitBox`.
**/
#[repr(C)]
pub struct IntoIter<C, T>
where C: Cursor, T: BitStore {
	/// Owning pointer to the full slab
	bitbox: BitBox<C, T>,
	/// Slice descriptor for the region undergoing iteration.
	region: BitPtr<T>,
}

impl<C, T> IntoIter<C, T>
where C: Cursor, T: BitStore {
	fn iterator(&self) -> <&BitSlice<C, T> as IntoIterator>::IntoIter {
		self.region.into_bitslice().into_iter()
	}
}

impl<C, T> DoubleEndedIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next_back().copied();
		self.region = slice_iter.bitptr();
		out
	}
}

impl<C, T> ExactSizeIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> FusedIterator for IntoIter<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Iterator for IntoIter<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next().copied();
		self.region = slice_iter.bitptr();
		out
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iterator().size_hint()
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.nth(n).copied();
		self.region = slice_iter.bitptr();
		out
	}

	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}
