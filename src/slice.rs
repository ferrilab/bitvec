/*! `BitSlice` Wide Reference

This module defines semantic operations on `[u1]`, in contrast to the mechanical
operations defined in `BitPtr`.

The `&BitSlice` handle has the same size and general layout as the standard Rust
slice handle `&[T]`. Its binary layout is wholly incompatible with the layout of
Rust slices, and must never be interchanged except through the provided APIs.
!*/

use crate::{
	access::BitAccess,
	cursor::{
		BigEndian,
		Cursor,
	},
	domain::*,
	indices::Indexable,
	pointer::BitPtr,
	store::BitStore,
};

#[cfg(feature = "alloc")]
use {
	crate::vec::BitVec,
	alloc::borrow::ToOwned,
};

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
	default::Default,
	fmt::{
		self,
		Debug,
		DebugList,
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
		FusedIterator,
		Iterator,
		IntoIterator,
	},
	marker::{
		PhantomData,
		Send,
		Sync,
	},
	mem,
	ops::{
		AddAssign,
		BitAndAssign,
		BitOrAssign,
		BitXorAssign,
		Deref,
		DerefMut,
		Drop,
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
	str,
};

/** A compact slice of bits, whose cursor and storage types can be customized.

`BitSlice` is a specialized slice type, which can only ever be held by
reference or specialized owning pointers provided by this crate. The value
patterns of its handles are opaque binary structures, which cannot be
meaningfully inspected by user code.

`BitSlice` can only be dynamically allocated by this library. Creation of any
other `BitSlice` collections will result in severely incorrect behavior.

A `BitSlice` reference can be created through the [`bitvec!`] macro, from a
[`BitVec`] collection, or from most common Rust types (fundamentals, slices of
them, and small arrays) using the [`Bits`] and [`BitsMut`] traits.

`BitSlice`s are a view into a block of memory at bit-level resolution. They are
represented by a crate-internal pointer structure that ***cannot*** be used with
other Rust code except through the provided conversion APIs.

```rust
use bitvec::prelude::*;

# #[cfg(feature = "alloc")] {
let bv = bitvec![0, 1, 0, 1];
//  slicing a bitvec
let bslice: &BitSlice = &bv[..];
# }
//  coercing an array to a bitslice
let bslice: &BitSlice = [1u8, 254u8].as_bitslice::<BigEndian>();
```

Bit slices are either mutable or shared. The shared slice type is
`&BitSlice<C, T>`, while the mutable slice type is `&mut BitSlice<C, T>`. For
example, you can mutate bits in the memory to which a mutable `BitSlice` points:

```rust
use bitvec::prelude::*;

let mut base = [0u8, 0, 0, 0];
{
 let bs: &mut BitSlice = base.as_mut_bitslice::<BigEndian>();
 bs.set(13, true);
 eprintln!("{:?}", bs.as_ref());
 assert!(bs[13]);
}
assert_eq!(base[1], 4);
```

# Type Parameters

- `C: Cursor`: An implementor of the `Cursor` trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the `BitStore` trait: `u8`, `u16`, `u32`, or
  `u64` (64-bit systems only). This is the actual type in memory that the slice
  will use to store data.

# Safety

The `&BitSlice` reference handle has the same *size* as standard Rust slice
handles, but it is ***extremely binary incompatible*** with them. Attempting to
treat `&BitSlice<_, T>` as `&[T]` in any manner except through the provided APIs
is ***catastrophically*** unsafe and unsound.

[`BitVec`]: ../vec/struct.BitVec.html
[`Bits`]: ../bits/trait.Bits.html
[`BitsMut`]: ../bits/trait.BitsMut.html
[`From`]: https://doc.rust-lang.org/stable/std/convert/trait.From.html
[`bitvec!`]: ../macro.bitvec.html
**/
#[repr(transparent)]
pub struct BitSlice<C = BigEndian, T = u8>
where C: Cursor, T: BitStore {
	/// Cursor type for selecting bits inside an element.
	_kind: PhantomData<C>,
	/// Element type of the slice.
	///
	/// eddyb recommends using `PhantomData<T>` and `[()]` instead of `[T]`
	/// alone.
	_type: PhantomData<T>,
	/// Slice of elements `T` over which the `BitSlice` has usage.
	_elts: [()],
}

impl<C, T> BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Produces the empty slice. This is equivalent to `&[]` for Rust slices.
	///
	/// # Returns
	///
	/// An empty `&BitSlice` handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits: &BitSlice = BitSlice::empty();
	/// ```
	pub fn empty<'a>() -> &'a Self {
		BitPtr::empty().into_bitslice()
	}

	/// Produces the empty mutable slice. This is equivalent to `&mut []` for
	/// Rust slices.
	///
	/// # Returns
	///
	/// An empty `&mut BitSlice` handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits: &mut BitSlice = BitSlice::empty_mut();
	/// ```
	pub fn empty_mut<'a>() -> &'a mut Self {
		BitPtr::empty().into_bitslice_mut()
	}

	/// Produces an immutable `BitSlice` over a single element.
	///
	/// # Parameters
	///
	/// - `elt`: A reference to an element over which the `BitSlice` will be
	///   created.
	///
	/// # Returns
	///
	/// A `BitSlice` over the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let elt: u8 = !0;
	/// let bs: &BitSlice = BitSlice::from_element(&elt);
	/// assert!(bs.all());
	/// ```
	pub fn from_element(elt: &T) -> &Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0u8.idx(), T::BITS as usize)
		}.into_bitslice()
	}

	/// Produces a mutable `BitSlice` over a single element.
	///
	/// # Parameters
	///
	/// - `elt`: A reference to an element over which the `BitSlice` will be
	///   created.
	///
	/// # Returns
	///
	/// A `BitSlice` over the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut elt: u8 = !0;
	/// let bs: &mut BitSlice = BitSlice::from_element_mut(&mut elt);
	/// bs.set(0, false);
	/// assert!(!bs.all());
	/// ```
	pub fn from_element_mut(elt: &mut T) -> &mut Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0u8.idx(), T::BITS as usize)
		}.into_bitslice_mut()
	}

	/// Wraps a `&[T: BitStore]` in a `&BitSlice<C: Cursor, T>`. The cursor must
	/// be specified at the call site. The element type cannot be changed.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `BitSlice` representing the original element slice.
	///
	/// # Panics
	///
	/// The source slice must not exceed the maximum number of elements that a
	/// `BitSlice` can contain. This value is documented in [`BitPtr`].
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [1, 2, 3];
	/// let bits = BitSlice::<BigEndian, u8>::from_slice(&src[..]);
	/// assert_eq!(bits.len(), 24);
	/// assert_eq!(bits.as_ref().len(), 3);
	/// assert!(bits[7]);  // src[0] == 0b0000_0001
	/// assert!(bits[14]); // src[1] == 0b0000_0010
	/// assert!(bits[22]); // src[2] == 0b0000_0011
	/// assert!(bits[23]);
	/// ```
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn from_slice(slice: &[T]) -> &Self {
		let len = slice.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitSlice cannot address {} elements",
			len,
		);
		let bits = len.checked_mul(T::BITS as usize)
			.expect("Bit length out of range");
		BitPtr::new(slice.as_ptr(), 0u8.idx(), bits).into_bitslice()
	}

	/// Wraps a `&mut [T: BitStore]` in a `&mut BitSlice<C: Cursor, T>`. The
	/// cursor must be specified by the call site. The element type cannot
	/// be changed.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `BitSlice` representing the original element slice.
	///
	/// # Panics
	///
	/// The source slice must not exceed the maximum number of elements that a
	/// `BitSlice` can contain. This value is documented in [`BitPtr`].
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1, 2, 3];
	/// let bits = BitSlice::<LittleEndian, u8>::from_slice_mut(&mut src[..]);
	/// //  The first bit is the LSb of the first element.
	/// assert!(bits[0]);
	/// bits.set(0, false);
	/// assert!(!bits[0]);
	/// assert_eq!(bits.as_ref(), &[0, 2, 3]);
	/// ```
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn from_slice_mut(slice: &mut [T]) -> &mut Self {
		Self::from_slice(slice).bitptr().into_bitslice_mut()
	}

	/// Returns the number of bits contained in the `BitSlice`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of live bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store = 0u8;
	/// let bs = store.as_bitslice::<BigEndian>();
	/// assert_eq!(bs.len(), 8);
	/// ```
	pub fn len(&self) -> usize {
		self.bitptr().len()
	}

	/// Tests if the slice is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether the slice has no live bits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bs = BitSlice::<BigEndian, u8>::empty();
	/// assert!(bs.is_empty());
	/// let bs = 0u8.as_bitslice::<BigEndian>();
	/// assert!(!bs.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Gets the first element of the slice, if present.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// `None` if the slice is empty, or `Some(bit)` if it is not.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().first().is_none());
	/// assert!(128u8.as_bitslice::<BigEndian>().first().unwrap());
	/// ```
	pub fn first(&self) -> Option<bool> {
		self.get(0)
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the first bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().split_first().is_none());
	///
	/// let store = 128u8;
	/// let bits = store.as_bitslice::<BigEndian>();
	/// let (h, t) = bits.split_first().unwrap();
	/// assert!(h);
	/// assert!(t.not_any());
	///
	/// let (h, t) = bits[0 .. 1].split_first().unwrap();
	/// assert!(h);
	/// assert!(t.is_empty());
	/// ```
	pub fn split_first(&self) -> Option<(bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((self[0], &self[1 ..]))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the first bit
	/// - a `&mut BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 0u8;
	/// let bits = store.as_mut_bitslice::<LittleEndian>();
	/// assert!(!bits[0]);
	/// *bits.at(0) = true;
	/// let (h, t) = bits.split_first_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(bool, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((self[0], &mut self[1 ..]))
		}
	}

	/// Returns the last and all the rest of the bits in the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the last bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().split_last().is_none());
	///
	/// let bits = 1u8.as_bitslice::<BigEndian>();
	/// let (t, h) = bits.split_last().unwrap();
	/// assert!(t);
	/// assert!(h.not_any());
	///
	/// let bits = &bits[7 .. 8];
	/// let (t, h) = bits.split_last().unwrap();
	/// assert!(t);
	/// assert!(h.is_empty());
	/// ```
	pub fn split_last(&self) -> Option<(bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			let len = self.len();
			Some((self[len - 1], &self[.. len - 1]))
		}
	}

	/// Returns the last and all the rest of the bits in the slice, or `None`
	/// if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// If the slice is empty, this returns `None`, otherwise, it returns `Some`
	/// of:
	///
	/// - the last bit
	/// - a `&BitSlice` of all the rest of the bits (this may be empty)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 0u8;
	/// let bits = store.as_mut_bitslice::<LittleEndian>();
	/// assert!(!bits[7]);
	/// *bits.at(7) = true;
	/// let (h, t) = bits.split_last_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(bool, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			let len = self.len();
			Some((self[len - 1], &mut self[.. len - 1]))
		}
	}

	/// Gets the last element of the slice, or `None` if it is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// `None` if the slice is empty, or `Some(bit)` if it is not.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// assert!(BitSlice::<BigEndian, u8>::empty().last().is_none());
	/// assert!(1u8.as_bitslice::<BigEndian>().last().unwrap());
	/// ```
	pub fn last(&self) -> Option<bool> {
		if self.is_empty() {
			None
		}
		else {
			Some(self[self.len() - 1])
		}
	}

	/// Gets the bit value at the given position.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The bit index to retrieve.
	///
	/// # Returns
	///
	/// The bit at the specified index, if any. If `index` is beyond the bounds
	/// of `self`, then `None` is produced.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 8u8.as_bitslice::<BigEndian>();
	/// assert!(bits.get(4).unwrap());
	/// assert!(!bits.get(3).unwrap());
	/// assert!(bits.get(10).is_none());
	/// ```
	pub fn get(&self, index: usize) -> Option<bool> {
		if index >= self.len() {
			None
		}
		else {
			Some(unsafe { self.get_unchecked(index) })
		}
	}

	/// Looks up a bit at an index, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`get`].
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `index`: The bit index to retrieve. This index is *not* checked
	///   against the length of `self`.
	///
	/// # Returns
	///
	/// The bit at the requested index.
	///
	/// # Safety
	///
	/// This method is **not** safe. It performs raw pointer arithmetic to seek
	/// from the start of the slice to the requested index, and look up the bit
	/// there. It does not inspect the length of `self`, and it is free to
	/// perform out-of-bounds memory access.
	///
	/// Use this method **only** when you have already performed the bounds
	/// check, and can guarantee that the call occurs with a safely in-bounds
	/// index.
	///
	/// # Examples
	///
	/// This example uses a bit slice of length 2, and demonstrates
	/// out-of-bounds access to the last bit in the element.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 1u8;
	/// let bits = &src.as_bitslice::<BigEndian>()[2 .. 4];
	/// assert_eq!(bits.len(), 2);
	/// assert!(unsafe { bits.get_unchecked(5) });
	/// ```
	///
	/// [`get`]: #method.get
	pub unsafe fn get_unchecked(&self, index: usize) -> bool {
		let bitptr = self.bitptr();
		let (elt, bit) = bitptr.head().offset(index as isize);
		let data_ptr = bitptr.pointer().a();
		(&*data_ptr.offset(elt)).get::<C>(bit)
	}

	/// Sets the bit value at the given position.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The bit index to set. It must be in the domain
	///   `0 .. self.len()`.
	/// - `value`: The value to be set, `true` for `1` and `false` for `0`.
	///
	/// # Panics
	///
	/// This method panics if `index` is outside the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 8u8;
	/// let bits = store.as_mut_bitslice::<BigEndian>();
	/// assert!(!bits[3]);
	/// bits.set(3, true);
	/// assert!(bits[3]);
	/// ```
	pub fn set(&mut self, index: usize, value: bool) {
		let len = self.len();
		assert!(index < len, "Index out of range: {} >= {}", index, len);
		unsafe { self.set_unchecked(index, value) };
	}

	/// Sets a bit at an index, without doing bounds checking.
	///
	/// This is generally not recommended; use with caution! For a safe
	/// alternative, see [`set`].
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The bit index to retrieve. This index is *not* checked
	///   against the length of `self`.
	///
	/// # Effects
	///
	/// The bit at `index` is set to `value`.
	///
	/// # Safety
	///
	/// This method is **not** safe. It performs raw pointer arithmetic to seek
	/// from the start of the slice to the requested index, and set the bit
	/// there. It does not inspect the length of `self`, and it is free to
	/// perform out-of-bounds memory *write* access.
	///
	/// Use this method **only** when you have already performed the bounds
	/// check, and can guarantee that the call occurs with a safely in-bounds
	/// index.
	///
	/// # Examples
	///
	/// This example uses a bit slice of length 2, and demonstrates
	/// out-of-bounds access to the last bit in the element.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// {
	///  let bits = &mut src.as_mut_bitslice::<BigEndian>()[2 .. 4];
	///  assert_eq!(bits.len(), 2);
	///  unsafe { bits.set_unchecked(5, true); }
	/// }
	/// assert_eq!(src, 1);
	/// ```
	///
	/// [`set`]: #method.set
	pub unsafe fn set_unchecked(&mut self, index: usize, value: bool) {
		let bitptr = self.bitptr();
		let (elt, bit) = bitptr.head().offset(index as isize);
		let data_ptr = bitptr.pointer().a();
		(&*data_ptr.offset(elt)).set::<C>(bit, value);
	}

	/// Produces a write reference to a single bit in the slice.
	///
	/// The structure returned by this method extends the borrow until it drops,
	/// which precludes parallel use.
	///
	/// The [`split_at_mut`] method allows splitting the borrows of a slice, and
	/// will enable safe parallel use of these write references. The `atomic`
	/// feature guarantees that parallel use does not cause data races when
	/// modifying the underlying slice.
	///
	/// # Lifetimes
	///
	/// - `'a` Propagates the lifetime of the referent slice to the single-bit
	///   reference produced.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The index of the bit in `self` selected.
	///
	/// # Returns
	///
	/// A write reference to the requested bit. Due to Rust limitations, this is
	/// not a native reference type, but is a custom structure that holds the
	/// address of the requested bit and its value. The produced structure
	/// implements `Deref` and `DerefMut` to its cached bit, and commits the
	/// cached bit to the parent slice on drop.
	///
	/// # Usage
	///
	/// You must use the dereference operator on the `.at()` expression in order
	/// to assign to it. In general, you should prefer immediately using and
	/// discarding the returned value, rather than binding it to a name and
	/// letting it live for more than one statement.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	///
	/// assert!(!bits[0]);
	/// *bits.at(0) = true;
	/// //  note the leading dereference.
	/// assert!(bits[0]);
	/// ```
	///
	/// This example shows multiple usage by using `split_at_mut`.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	///
	/// {
	///  let (mut a, rest) = bits.split_at_mut(2);
	///  let (mut b, rest) = rest.split_at_mut(3);
	///  *a.at(0) = true;
	///  *b.at(0) = true;
	///  *rest.at(0) = true;
	/// }
	///
	/// assert_eq!(bits.as_slice()[0], 0b1010_0100);
	/// //                               a b   rest
	/// ```
	///
	/// The above example splits the slice into three (the first, the second,
	/// and the rest) in order to hold multiple write references into the slice.
	///
	/// [`split_at_mut`]: #method.split_at_mut
	pub fn at(&mut self, index: usize) -> BitGuard<C, T> {
		BitGuard {
			_m: PhantomData,
			bit: self[index],
			slot: &mut self[index ..= index],
		}
	}

	/// Retrieves a read pointer to the start of the underlying data slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A pointer to the first element, partial or not, in the underlying store.
	///
	/// If `self` is empty, then the null pointer is returned.
	///
	/// # Safety
	///
	/// The caller must ensure that the slice outlives the pointer this function
	/// returns, or else it will dangle and point to garbage.
	///
	/// Modifying the container referenced by this slice may cause its buffer to
	/// reallocate, which would also make any pointers to it invalid.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8; 4];
	/// let bits = src.as_bitslice::<BigEndian>();
	/// assert_eq!(src.as_ptr(), bits.as_ptr());
	/// ```
	pub fn as_ptr(&self) -> *const T {
		if self.is_empty() {
			ptr::null()
		}
		else {
			self.bitptr().pointer().r()
		}
	}

	/// Retrieves a write pointer to the start of the underlying data slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A pointer to the first element, partial or not, in the underlying store.
	///
	/// If `self` is empty, then the null pointer is returned.
	///
	/// # Safety
	///
	/// The caller must ensure that the slice outlives the pointer this function
	/// returns, or else it will dangle and point to garbage.
	///
	/// Modifying the container referenced by this slice may cause its buffer to
	/// reallocate, which would also make any pointers to it invalid.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8; 4];
	/// let src_ptr = src.as_mut_ptr();
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// assert_eq!(src_ptr, bits.as_mut_ptr());
	/// ```
	pub fn as_mut_ptr(&mut self) -> *mut T {
		if self.is_empty() {
			ptr::null_mut()
		}
		else {
			self.bitptr().pointer().w()
		}
	}

	/// Swaps two bits in the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `a`: The first index to be swapped.
	/// - `b`: The second index to be swapped.
	///
	/// # Panics
	///
	/// Panics if either `a` or `b` are out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut store = 32u8;
	/// let bits = store.as_mut_bitslice::<BigEndian>();
	/// assert!(!bits[0]);
	/// assert!(bits[2]);
	/// bits.swap(0, 2);
	/// assert!(bits[0]);
	/// assert!(!bits[2]);
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) {
		assert!(a < self.len(), "Index {} out of bounds: {}", a, self.len());
		assert!(b < self.len(), "Index {} out of bounds: {}", b, self.len());
		let bit_a = self[a];
		let bit_b = self[b];
		self.set(a, bit_b);
		self.set(b, bit_a);
	}

	/// Reverses the order of bits in the slice, in place.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b1010_1010u8;
	/// {
	///   let bits = src.as_mut_bitslice::<BigEndian>();
	///   bits[1 .. 7].reverse();
	/// }
	/// eprintln!("{:b}", src);
	/// assert_eq!(src, 0b1101_0100);
	/// ```
	pub fn reverse(&mut self) {
		//  this is better implemented as a recursive algorithm, but Rust
		//  doesn’t yet flatten recursive tail calls into a loop, so, do it
		//  manually.
		let mut cur: &mut Self = self;
		loop {
			let len = cur.len();
			if len < 2 {
				return;
			}
			//  swap() has two assertions on each call, that reverse() knows it
			//  can bypass
			let (h, t) = (cur[0], cur[len - 1]);
			cur.set(0, t);
			cur.set(len - 1, h);
			cur = &mut cur[1 .. len - 1];
		}
	}

	/// Provides read-only iteration across the slice domain.
	///
	/// The iterator returned from this method implements `ExactSizeIterator`
	/// and `DoubleEndedIterator` just as the consuming `.into_iter()` method’s
	/// iterator does.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An iterator over all bits in the slice domain, in `C` and `T` ordering.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 64u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// let mut iter = bits[.. 2].iter();
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	pub fn iter(&self) -> Iter<C, T> {
		self.into_iter()
	}

	/// Produces a sliding iterator over consecutive windows in the slice. Each
	/// windows has the width `size`. The windows overlap. If the slice is
	/// shorter than `size`, the produced iterator is empty.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each window.
	///
	/// # Returns
	///
	/// An iterator which yields sliding views into the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// let mut windows = bits.windows(4);
	/// assert_eq!(windows.next(), Some(&bits[0 .. 4]));
	/// assert_eq!(windows.next(), Some(&bits[1 .. 5]));
	/// assert_eq!(windows.next(), Some(&bits[2 .. 6]));
	/// assert_eq!(windows.next(), Some(&bits[3 .. 7]));
	/// assert_eq!(windows.next(), Some(&bits[4 .. 8]));
	/// assert!(windows.next().is_none());
	/// ```
	pub fn windows(&self, size: usize) -> Windows<C, T> {
		assert_ne!(size, 0, "Window width cannot be zero");
		Windows {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// let mut chunks = bits.chunks(3);
	/// assert_eq!(chunks.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks.next(), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks.next(), Some(&bits[6 .. 8]));
	/// assert!(chunks.next().is_none());
	/// ```
	pub fn chunks(&self, size: usize) -> Chunks<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		Chunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk, except possibly the last, has the width `size`. The chunks do not
	/// overlap. If the slice is shorter than `size`, the produced iterator
	/// produces only one chunk.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if the `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.as_mut_bitslice::<BigEndian>();
	///  let mut chunks = bits.chunks_mut(3);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(2, true);
	///  chunks.next().unwrap().set(1, false);
	/// }
	/// assert_eq!(src, 0b0110_1110);
	/// ```
	pub fn chunks_mut(&mut self, size: usize) -> ChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk width cannot be zero");
		ChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks_exact.next(), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.next().is_none());
	/// assert_eq!(chunks_exact.remainder(), &bits[6 .. 8]);
	/// ```
	pub fn chunks_exact(&self, size: usize) -> ChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at(len);
		ChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice. Each
	/// chunk has the width `size`. If `size` does not evenly divide the slice,
	/// then the remainder is not part of the iteration, and can be accessed
	/// separately with the `.remainder()` method.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.as_mut_bitslice::<BigEndian>();
	///  let mut chunks_exact = bits.chunks_exact_mut(3);
	///  chunks_exact.next().unwrap().set(2, true);
	///  chunks_exact.next().unwrap().set(2, true);
	///  assert!(chunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0110_1111);
	/// ```
	pub fn chunks_exact_mut(&mut self, size: usize) -> ChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let rem = self.len() % size;
		let len = self.len() - rem;
		let (inner, extra) = self.split_at_mut(len);
		ChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0b0100_1011u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// let mut rchunks = bits.rchunks(3);
	/// assert_eq!(rchunks.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks.next(), Some(&bits[2 .. 5]));
	/// assert_eq!(rchunks.next(), Some(&bits[0 .. 2]));
	/// assert!(rchunks.next().is_none());
	/// ```
	pub fn rchunks(&self, size: usize) -> RChunks<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunks {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk, except possibly the front, has the
	/// width `size`. The chunks do not overlap. If the slice is shorter than
	/// `size`, then the iterator produces one item.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.as_mut_bitslice::<BigEndian>();
	///  let mut rchunks = bits.rchunks_mut(3);
	///  rchunks.next().unwrap().set(0, true);
	///  rchunks.next().unwrap().set(2, false);
	///  rchunks.next().unwrap().set(1, false);
	///  assert!(rchunks.next().is_none());
	/// }
	/// assert_eq!(src, 0b0000_0111);
	/// ```
	pub fn rchunks_mut(&mut self, size: usize) -> RChunksMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		RChunksMut {
			inner: self,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive chunks of the slice, from the back
	/// to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store: &[u8] = &[0b0100_1011];
	/// let bits: &BitSlice = store.into();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks_exact.next(), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.next().is_none());
	/// assert_eq!(rchunks_exact.remainder(), &bits[0 .. 2]);
	/// ```
	pub fn rchunks_exact(&self, size: usize) -> RChunksExact<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at(self.len() % size);
		RChunksExact {
			inner,
			extra,
			width: size,
		}
	}

	/// Produces a galloping iterator over consecutive chunks in the slice, from
	/// the back to the front. Each chunk has the width `size`. If `size` does
	/// not evenly divide the slice, then the remainder is not part of the
	/// iteration, and can be accessed separately with the `.remainder()`
	/// method.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `size`: The width of each chunk.
	///
	/// # Returns
	///
	/// An iterator which yields consecutive mutable chunks of the slice, from
	/// the back to the front.
	///
	/// # Panics
	///
	/// This function panics if `size` is zero.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0b0100_1011u8;
	/// {
	///  let bits = src.as_mut_bitslice::<BigEndian>();
	///  let mut rchunks_exact = bits.rchunks_exact_mut(3);
	///  rchunks_exact.next().unwrap().set(0, true);
	///  rchunks_exact.next().unwrap().set(2, false);
	///  assert!(rchunks_exact.next().is_none());
	/// }
	/// assert_eq!(src, 0b0100_0111);
	/// ```
	pub fn rchunks_exact_mut(&mut self, size: usize) -> RChunksExactMut<C, T> {
		assert_ne!(size, 0, "Chunk size cannot be zero");
		let (extra, inner) = self.split_at_mut(self.len() % size);
		RChunksExactMut {
			inner,
			extra,
			width: size,
		}
	}

	/// Divides one slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `mid`: The index at which to split
	///
	/// # Returns
	///
	/// - The bits up to but not including `mid`.
	/// - The bits from mid onwards.
	///
	/// # Panics
	///
	/// Panics if `mid > self.len()`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 15u8.as_bitslice::<BigEndian>();
	///
	/// let (l, r) = bits.split_at(0);
	/// assert!(l.is_empty());
	/// assert_eq!(r, bits);
	///
	/// let (l, r) = bits.split_at(4);
	/// assert_eq!(l, &bits[0 .. 4]);
	/// assert_eq!(r, &bits[4 .. 8]);
	///
	/// let (l, r) = bits.split_at(8);
	/// assert_eq!(l, bits);
	/// assert!(r.is_empty());
	/// ```
	pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
		let len = self.len();
		assert!(mid <= len, "Index {} out of bounds: {}", mid, len);
		if mid == len {
			(&self, Self::empty())
		}
		else {
			(&self[.. mid], &self[mid ..])
		}
	}

	/// Divides one slice into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (excluding the index
	/// `mid` itself) and the second will contain all indices from `[mid, len)`
	/// (excluding the index `len` itself).
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `mid`: The index at which to split
	///
	/// # Returns
	///
	/// - The bits up to but not including `mid`.
	/// - The bits from mid onwards.
	///
	/// # Panics
	///
	/// Panics if `mid > self.len()`.
	pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
		let (head, tail) = self.split_at(mid);
		(head.bitptr().into_bitslice_mut(), tail.bitptr().into_bitslice_mut())
	}

	/// Tests if the slice begins with the given prefix.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `prefix`: Any `BitSlice` against which `self` is tested. This is not
	///   required to have the same cursor or storage types as `self`.
	///
	/// # Returns
	///
	/// Whether `self` begins with `prefix`. This is true only if `self` is at
	/// least as long as `prefix` and their bits are semantically equal.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xA6u8.as_bitslice::<BigEndian>();
	/// assert!(bits.starts_with(&bits[.. 3]));
	/// assert!(!bits.starts_with(&bits[3 ..]));
	/// ```
	pub fn starts_with<D, U>(&self, prefix: &BitSlice<D, U>) -> bool
	where D: Cursor, U: BitStore {
		let plen = prefix.len();
		self.len() >= plen && prefix == self[.. plen]
	}

	/// Tests if the slice ends with the given suffix.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `suffix`: Any `BitSlice` against which `self` is tested. This is not
	///   required to have the same cursor or storage types as `self`.
	///
	/// # Returns
	///
	/// Whether `self` ends with `suffix`. This is true only if `self` is at
	/// least as long as `suffix` and their bits are semantically equal.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xA6u8.as_bitslice::<BigEndian>();
	/// assert!(bits.ends_with(&bits[5 ..]));
	/// assert!(!bits.ends_with(&bits[.. 5]));
	/// ```
	pub fn ends_with<D, U>(&self, suffix: &BitSlice<D, U>) -> bool
	where D: Cursor, U: BitStore {
		let slen = suffix.len();
		let len = self.len();
		len >= slen && suffix == self[len - slen ..]
	}

	/// Rotates the slice, in place, to the left.
	///
	/// After calling this method, the bits from `[.. by]` will be at the back
	/// of the slice, and the bits from `[by ..]` will be at the front. This
	/// operates fully in-place.
	///
	/// In-place rotation of bits requires this method to take `O(k × n)` time.
	/// It is impossible to use machine intrinsics to perform galloping rotation
	/// on bits.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The number of bits by which to rotate left. This must be in the
	///   range `0 ..= self.len()`. If it is `0` or `self.len()`, then this
	///   method is a no-op.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0xF0u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// bits.rotate_left(2);
	/// assert_eq!(bits.as_ref()[0], 0xC3);
	/// ```
	pub fn rotate_left(&mut self, by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == 0 || by == len {
			return;
		}

		for _ in 0 .. by {
			let tmp = self[0];
			for n in 1 .. len {
				let bit = self[n];
				self.set(n - 1, bit);
			}
			self.set(len - 1, tmp);
		}
	}

	/// Rotates the slice, in place, to the right.
	///
	/// After calling this method, the bits from `[self.len() - by ..]` will be
	/// at the front of the slice, and the bits from `[.. self.len() - by]` will
	/// be at the back. This operates fully in-place.
	///
	/// In-place rotation of bits requires this method to take `O(k × n)` time.
	/// It is impossible to use machine intrinsics to perform galloping rotation
	/// on bits.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The number of bits by which to rotate right. This must be in the
	///   range `0 ..= self.len()`. If it is `0` or `self.len`, then this method
	///   is a no-op.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0xF0u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// bits.rotate_right(2);
	/// assert_eq!(bits.as_ref()[0], 0x3C);
	/// ```
	pub fn rotate_right(&mut self, by: usize) {
		let len = self.len();
		assert!(by <= len, "Slices cannot be rotated by more than their length");
		if by == len {
			return;
		}

		//  Perform `by` repetitions,
		for _ in 0 .. by {
			let tmp = self[len - 1];
			//  of `len` steps
			for n in (0 .. len - 1).rev() {
				let bit = self[n];
				self.set(n + 1, bit);
			}
			self.set(0, tmp);
		}
	}

	/// Tests if *all* bits in the slice domain are set (logical `∧`).
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
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether all bits in the slice domain are set. The empty slice returns
	/// `true`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xFDu8.as_bitslice::<BigEndian>();
	/// assert!(bits[.. 4].all());
	/// assert!(!bits[4 ..].all());
	/// ```
	pub fn all(&self) -> bool {
		match self.bitptr().domain() {
			BitDomain::Empty => {},
			BitDomain::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					if !elt.get::<C>(n.idx()) {
						return false;
					}
				}
			},
			BitDomain::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					if !head.get::<C>(n.idx()) {
						return false;
					}
				}
				for n in 0 .. *t {
					if !tail.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					if !head.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::PartialTail(body, tail, t) => {
				for n in 0 .. *t {
					if !tail.get::<C>(n.idx()) {
						return false;
					}
				}
				return body.iter().all(|e| *e == T::bits(true));
			},
			BitDomain::Spanning(body) => {
				return body.iter().all(|e| *e == T::bits(true));
			},
		}
		true
	}

	/// Tests if *any* bit in the slice is set (logical `∨`).
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
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether any bit in the slice domain is set. The empty slice returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x40u8.as_bitslice::<BigEndian>();
	/// assert!(bits[.. 4].any());
	/// assert!(!bits[4 ..].any());
	/// ```
	pub fn any(&self) -> bool {
		match self.bitptr().domain() {
			BitDomain::Empty => {},
			BitDomain::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					if elt.get::<C>(n.idx()) {
						return true;
					}
				}
			},
			BitDomain::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					if head.get::<C>(n.idx()) {
						return true;
					}
				}
				for n in 0 .. *t {
					if tail.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					if head.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::PartialTail(body, tail, t) => {
				for n in 0 .. *t {
					if tail.get::<C>(n.idx()) {
						return true;
					}
				}
				return body.iter().any(|e| *e != T::bits(false));
			},
			BitDomain::Spanning(body) => {
				return body.iter().any(|e| *e != T::bits(false));
			},
		}
		false
	}

	/// Tests if *any* bit in the slice is unset (logical `¬∧`).
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
	/// # Parameters
	///
	/// - `&self
	///
	/// # Returns
	///
	/// Whether any bit in the slice domain is unset.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xFDu8.as_bitslice::<BigEndian>();
	/// assert!(!bits[.. 4].not_all());
	/// assert!(bits[4 ..].not_all());
	/// ```
	pub fn not_all(&self) -> bool {
		!self.all()
	}

	/// Tests if *all* bits in the slice are unset (logical `¬∨`).
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
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether all bits in the slice domain are unset.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x40u8.as_bitslice::<BigEndian>();
	/// assert!(!bits[.. 4].not_any());
	/// assert!(bits[4 ..].not_any());
	/// ```
	pub fn not_any(&self) -> bool {
		!self.any()
	}

	/// Tests whether the slice has some, but not all, bits set and some, but
	/// not all, bits unset.
	///
	/// This is `false` if either `all()` or `not_any()` are `true`.
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
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// Whether the slice domain has mixed content. The empty slice returns
	/// `false`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b111_000_10u8.as_bitslice::<BigEndian>();
	/// assert!(!bits[0 .. 3].some());
	/// assert!(!bits[3 .. 6].some());
	/// assert!(bits[6 ..].some());
	/// ```
	pub fn some(&self) -> bool {
		self.any() && self.not_all()
	}

	/// Counts how many bits are set high.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of high bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = [0xFDu8, 0x25].as_bitslice::<BigEndian>();
	/// assert_eq!(bits.count_ones(), 10);
	/// ```
	pub fn count_ones(&self) -> usize {
		match self.bitptr().domain() {
			BitDomain::Empty => 0,
			BitDomain::Minor(head, elt, tail) => {
				(*head .. *tail)
					.map(|n| elt.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::Major(h, head, body, tail, t) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| *b)
					.count() +
				body.iter()
					.map(T::count_ones)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::PartialHead(h, head, body) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| *b)
					.count() +
				body.iter()
					.map(T::count_ones)
					.sum::<usize>()
			},
			BitDomain::PartialTail(body, tail, t) => {
				body.iter()
					.map(T::count_ones)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| *b)
					.count()
			},
			BitDomain::Spanning(body) => {
				body.iter()
					.map(T::count_ones)
					.sum::<usize>()
			}
		}
	}

	/// Counts how many bits are set low.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of low bits in the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = [0xFDu8, 0x25].as_bitslice::<BigEndian>();
	/// assert_eq!(bits.count_zeros(), 6);
	/// ```
	pub fn count_zeros(&self) -> usize {
		match self.bitptr().domain() {
			BitDomain::Empty => 0,
			BitDomain::Minor(head, elt, tail) => {
				(*head .. *tail)
					.map(|n| !elt.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::Major(h, head, body, tail, t) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count() +
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::PartialHead(h, head, body) => {
				(*h .. T::BITS)
					.map(|n| head.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count() +
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>()
			},
			BitDomain::PartialTail(body, tail, t) => {
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>() +
				(0 .. *t)
					.map(|n| tail.get::<C>(n.idx()))
					.filter(|b| !*b)
					.count()
			},
			BitDomain::Spanning(body) => {
				body.iter()
					.map(T::count_zeros)
					.sum::<usize>()
			},
		}
	}

	/// Set all bits in the slice to a value.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `value`: The bit value to which all bits in the slice will be set.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// bits[2 .. 6].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b0011_1100]);
	/// bits[3 .. 5].set_all(false);
	/// assert_eq!(bits.as_ref(), &[0b0010_0100]);
	/// bits[.. 1].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b1010_0100]);
	/// ```
	pub fn set_all(&mut self, value: bool) {
		match self.bitptr().domain_mut() {
			BitDomainMut::Empty => {},
			BitDomainMut::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					elt.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					head.set::<C>(n.idx(), value);
				}
				for elt in body {
					*elt = T::bits(value);
				}
				for n in 0 .. *t {
					tail.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					head.set::<C>(n.idx(), value);
				}
				for elt in body {
					*elt = T::bits(value);
				}
			},
			BitDomainMut::PartialTail(body, tail, t) => {
				for elt in body {
					*elt = T::bits(value);
				}
				for n in 0 .. *t {
					tail.set::<C>(n.idx(), value);
				}
			},
			BitDomainMut::Spanning(body) => {
				for elt in body {
					*elt = T::bits(value);
				}
			},
		}
	}

	/// Provides mutable traversal of the collection.
	///
	/// It is impossible to implement `IndexMut` on `BitSlice`, because bits do
	/// not have addresses, so there can be no `&mut u1`. This method allows the
	/// client to receive an enumerated bit, and provide a new bit to set at
	/// each index.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `func`: A function which receives a `(usize, bool)` pair of index and
	///   value, and returns a bool. It receives the bit at each position, and
	///   the return value is written back at that position.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// {
	///  let bits = src.as_mut_bitslice::<BigEndian>();
	///  bits.for_each(|idx, _bit| idx % 3 == 0);
	/// }
	/// assert_eq!(src, 0b1001_0010);
	/// ```
	pub fn for_each<F>(&mut self, func: F)
	where F: Fn(usize, bool) -> bool {
		for idx in 0 .. self.len() {
			let tmp = self[idx];
			self.set(idx, func(idx, tmp));
		}
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This addition interprets the slice, and the other addend, as having its
	/// least significant bits first in the order and its most significant bits
	/// last. This is most likely to be numerically useful under a
	/// `LittleEndian` `Cursor` type.
	///
	/// # Parameters
	///
	/// - `&mut self`: The addition uses `self` as one addend, and writes the
	///   sum back into `self`.
	/// - `addend: impl IntoIterator<Item=bool>`: A stream of bits. When this is
	///   another `BitSlice`, iteration proceeds from left to right.
	///
	/// # Return
	///
	/// The final carry bit is returned
	///
	/// # Effects
	///
	/// Starting from index `0` and proceeding upwards until either `self` or
	/// `addend` expires, the carry-propagated addition of `self[i]` and
	/// `addend[i]` is written to `self[i]`.
	///
	/// ```text
	///   101111
	/// + 0010__ (the two missing bits are logically zero)
	/// --------
	///   100000 1 (the carry-out is returned)
	/// ```
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut a = 0b0000_1010u8;
	/// let     b = 0b0000_1100u8;
	/// //      s =      1 0110
	/// let ab = &mut a.as_mut_bitslice::<LittleEndian>()[.. 4];
	/// let bb = &    b.as_bitslice::<LittleEndian>()[.. 4];
	/// let c = ab.add_assign_reverse(bb);
	/// assert!(c);
	/// assert_eq!(ab.as_slice()[0], 0b0000_0110u8);
	/// ```
	///
	/// # Performance Notes
	///
	/// When using `LittleEndian` `Cursor` types, this can be accelerated by
	/// delegating the addition to the underlying types. This is a software
	/// implementation of the [ripple-carry adder], which has `O(n)` runtime in
	/// the number of bits. The CPU is much faster, as it has access to
	/// element-wise or vectorized addition operations.
	///
	/// If your use case sincerely needs binary-integer arithmetic operations on
	/// bit sets
	///
	/// [ripple-carry adder]: https://en.wikipedia.org/wiki/Ripple-carry_adder
	pub fn add_assign_reverse<I>(&mut self, addend: I) -> bool
	where I: IntoIterator<Item=bool> {
		//  See AddAssign::add_assign for algorithm details
		let mut c = false;
		let len = self.len();
		let zero = core::iter::repeat(false);
		for (i, b) in addend.into_iter().chain(zero).enumerate().take(len) {
			//  The iterator is clamped to the upper bound of `self`.
			let a = unsafe { self.get_unchecked(i) };
			let (y, z) = crate::rca1(a, b, c);
			//  Write the sum into `self`
			unsafe { self.set_unchecked(i, y); }
			//  Propagate the carry
			c = z;
		}
		c
	}

	/// Accesses the backing storage of the `BitSlice` as a slice of its
	/// elements.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all the elements that the `BitSlice` uses for storage.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [1u8, 66];
	/// let bits = src.as_bitslice::<BigEndian>();
	///
	/// let accum = bits.as_slice()
	///   .iter()
	///   .map(|elt| elt.count_ones())
	///   .sum::<usize>();
	/// assert_eq!(accum, 3);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		self.bitptr().as_slice()
	}

	/// Accesses the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1u8, 64];
	/// let bits = src.as_mut_bitslice::<BigEndian>();
	/// for elt in bits.as_mut_slice() {
	///   *elt |= 2;
	/// }
	/// assert_eq!(&[3, 66], bits.as_slice());
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		self.bitptr().as_mut_slice()
	}

	/// Changes the cursor type of the slice handle.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An equivalent slice handle with a new cursor type.
	///
	/// # Type Parameters
	///
	/// - `D: Cursor` The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 2u8;
	/// let bits = src.as_bitslice::<BigEndian>();
	/// assert!(bits[6]);
	/// let bits = bits.change_cursor::<LittleEndian>();
	/// assert!(bits[1]);
	/// ```
	pub fn change_cursor<D>(&self) -> &BitSlice<D, T>
	where D: Cursor {
		self.bitptr().into_bitslice()
	}

	/// Changes the cursor type of the slice handle.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// An equivalent slice handle with a new cursor type.
	///
	/// # Type Parameters
	///
	/// - `D: Cursor` The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// *src.as_mut_bitslice::<BigEndian>().at(1) = true;
	/// assert_eq!(src, 64);
	/// src.as_mut_bitslice::<BigEndian>()
	///    .change_cursor_mut::<LittleEndian>()
	///    .set(1, true);
	/// assert_eq!(src, 66);
	/// ```
	pub fn change_cursor_mut<D>(&mut self) -> &mut BitSlice<D, T>
	where D: Cursor {
		self.bitptr().into_bitslice_mut()
	}

	/// Accesses the underlying pointer structure.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The [`BitPtr`] structure of the slice handle.
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	pub fn bitptr(&self) -> BitPtr<T> {
		BitPtr::from_bitslice(self)
	}
}

/// Creates an owned `BitVec<C, T>` from a borrowed `BitSlice<C, T>`.
#[cfg(feature = "alloc")]
impl<C, T> ToOwned for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Owned = BitVec<C, T>;

	/// Clones a borrowed `BitSlice` into an owned `BitVec`.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let store = [0u8, 2];
	/// let src = store.as_bitslice::<LittleEndian>();
	/// let dst = src.to_owned();
	/// assert_eq!(src, dst);
	/// # }
	/// ```
	fn to_owned(&self) -> Self::Owned {
		Self::Owned::from_bitslice(self)
	}
}

impl<C, T> Eq for BitSlice<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.partial_cmp(rhs)
			.unwrap_or_else(|| unreachable!("`BitSlice` has a total ordering"))
	}
}

/// Tests if two `BitSlice`s are semantically — not bitwise — equal.
///
/// It is valid to compare two slices of different cursor or element types.
///
/// The equality condition requires that they have the same number of total bits
/// and that each pair of bits in semantic order are identical.
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
	/// let rsrc = [0x10_08_04_00u32];
	/// let lbits = lsrc.as_bitslice::<LittleEndian>();
	/// let rbits = rsrc.as_bitslice::<BigEndian>();
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

/// Allow comparison against the allocated form.
#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
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
	/// let bits = src.as_bitslice::<BigEndian>();
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

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		(*self).partial_cmp(rhs.as_bitslice())
	}
}

/// Provides write access to all elements in the underlying storage, including
/// the partial head and tail elements if present.
impl<C, T> AsMut<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutable slice of all storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8, 128];
	/// let bits = &mut src.as_mut_bitslice::<BigEndian>()[1 .. 9];
	///
	/// for elt in bits.as_mut() {
	///   *elt += 2;
	/// }
	///
	/// assert_eq!(&[2, 130], bits.as_ref());
	/// ```
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Provides read access to all elements in the underlying storage, including
/// the partial head and tail elements if present.
impl<C, T> AsRef<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An immutable slice of all storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, 128];
	/// let bits = &src.as_bitslice::<BigEndian>()[1 .. 9];
	/// assert_eq!(&[0, 128], bits.as_ref());
	/// ```
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<'a, C, T> From<&'a T> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a T) -> Self {
		BitSlice::<C, T>::from_element(src)
	}
}

impl<'a, C, T> From<&'a [T]> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a [T]) -> Self {
		BitSlice::<C, T>::from_slice(src)
	}
}

impl<'a, C, T> From<&'a mut T> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut T) -> Self {
		BitSlice::<C, T>::from_element_mut(src)
	}
}

impl<'a, C, T> From<&'a mut [T]> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut [T]) -> Self {
		BitSlice::<C, T>::from_slice_mut(src)
	}
}

impl<'a, C, T> Default for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty()
	}
}

impl<'a, C, T> Default for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty_mut()
	}
}

/// Prints the `BitSlice` for debugging.
///
/// The output is of the form `BitSlice<C, T> [ELT, *]` where `<C, T>` is the
/// cursor and element type, with square brackets on each end of the bits and
/// all the elements of the array printed in binary. The printout is always in
/// semantic order, and may not reflect the underlying buffer. To see the
/// underlying buffer, use `.as_ref()`.
///
/// The alternate character `{:#?}` prints each element on its own line, rather
/// than having all elements on the same line.
impl<C, T> Debug for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b0101_0000_1111_0101u16, 0b00000000_0000_0010];
	/// let bits = &src.as_bitslice::<LittleEndian>()[.. 18];
	/// assert_eq!(
    ///     "BitSlice<LittleEndian, u16> [1010111100001010, 01]",
	///     &format!("{:?}", bits),
	/// );
	/// # }
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitSlice<")?;
		f.write_str(C::TYPENAME)?;
		f.write_str(", ")?;
		f.write_str(T::TYPENAME)?;
		f.write_str("> ")?;
		Display::fmt(self, f)
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
impl<C, T> Display for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` contents for display.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `f`: The formatter into which `self` is written.
	///
	/// # Returns
	///
	/// The result of the formatting operation.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b01001011u8, 0b0100_0000];
	/// let bits = &src.as_bitslice::<BigEndian>()[.. 10];
	/// assert_eq!("[01001011, 01]", &format!("{}", bits));
	/// # }
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		struct Part<'a>(&'a str);
		impl<'a> Debug for Part<'a> {
			fn fmt(&self, f: &mut Formatter) -> fmt::Result {
				f.write_str(&self.0)
			}
		}

		let mut dbg = f.debug_list();
		if !self.is_empty() {
			//  Unfortunately, `T::BITS` cannot be used as the size for the
			//  array, due to limitations in the type system. As such, set it to
			//  the maximum used size.
			//
			//  This allows the writes to target a static buffer, rather
			//  than a dynamic string, making the formatter usable in
			//  `#![no_std]` contexts.
			let mut w: [u8; 64] = [b'0'; 64];
			fn writer<C, T>(
				l: &mut DebugList,
				w: &mut [u8; 64],
				e: &T,
				from: u8,
				to: u8,
			)
			where C: Cursor, T: BitStore {
				let (from, to) = (from as usize, to as usize);
				for (n, byte) in w.iter_mut().enumerate().take(to).skip(from) {
					*byte = b'0' + (e.get::<C>((n as u8).idx()) as u8);
				}
				l.entry(&Part(unsafe {
					str::from_utf8_unchecked(&w[from .. to])
				}));
			}
			match self.bitptr().domain() {
				BitDomain::Empty => {},
				BitDomain::Minor(head, elt, tail) => {
					writer::<C, T>(&mut dbg, &mut w, &elt.load(), *head, *tail)
				},
				BitDomain::Major(h, head, body, tail, t) => {
					writer::<C, T>(&mut dbg, &mut w, &head.load(), *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, &tail.load(), 0, *t);
				},
				BitDomain::PartialHead(h, head, body) => {
					writer::<C, T>(&mut dbg, &mut w, &head.load(), *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
				},
				BitDomain::PartialTail(body, tail, t) => {
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, &tail.load(), 0, *t);
				},
				BitDomain::Spanning(body) => {
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
				},
			}
		}
		dbg.finish()
	}
}

/// Writes the contents of the `BitSlice`, in semantic bit order, into a hasher.
impl<C, T> Hash for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Writes each bit of the `BitSlice`, as a full `bool`, into the hasher.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `hasher`: The hashing state into which the slice will be written.
	///
	/// # Type Parameters
	///
	/// - `H: Hasher`: The type of the hashing algorithm which receives the bits
	///   of `self`.
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
/// `ExactSizeIterator` as `BitSlice` has a known, fixed, length, and
/// `DoubleEndedIterator` as it has known ends.
impl<'a, C, T> IntoIterator for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;
	type IntoIter = Iter<'a, C, T>;

	/// Iterates over the slice.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An iterator over the slice domain.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0b1010_1100u8.as_bitslice::<BigEndian>();
	/// let mut count = 0;
	/// for bit in bits {
	///   if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		Iter {
			inner: self
		}
	}
}

/// `BitSlice` is safe to move across thread boundaries, when atomic operations
/// are enabled.
///
/// Consider this (contrived) example:
///
/// ```rust
/// # #[cfg(feature = "std")] {
/// use bitvec::prelude::*;
/// use std::thread;
///
/// static mut SRC: u8 = 0;
/// # {
/// let bits = unsafe { SRC.as_mut_bitslice::<BigEndian>() };
/// let (l, r) = bits.split_at_mut(4);
///
/// let a = thread::spawn(move || l.set(2, true));
/// let b = thread::spawn(move || r.set(2, true));
/// a.join();
/// b.join();
/// # }
///
/// println!("{:02X}", unsafe { SRC });
/// # }
/// ```
///
/// Without atomic operations, this is logically a data race. It *so happens*
/// that, on x86, the read/modify/write cycles used in the crate are *basically*
/// atomic by default, even when not specified as such. This is not necessarily
/// true on other architectures, however
#[cfg(feature = "atomic")]
unsafe impl<C, T> Send for BitSlice<C, T>
where C: Cursor, T: BitStore {}

/// `BitSlice` is safe to share between multiple threads.
unsafe impl<C, T> Sync for BitSlice<C, T>
where C: Cursor, T: BitStore {}

/// Performs unsigned addition in place on a `BitSlice`.
///
/// If the addend bitstream is shorter than `self`, the addend is zero-extended
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
///
/// # Type Parameters
///
/// - `I: IntoIterator<Item=bool, IntoIter: DoubleEndedIterator>`: The bitstream
///   to add into `self`. It must be finite and double-ended, since addition
///   operates in reverse.
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
			let a = unsafe { self.get_unchecked(i) };
			let (y, z) = crate::rca1(a, b, c);
			unsafe { self.set_unchecked(i, y); }
			c = z;
		}
	}
}

/// Performs the Boolean `AND` operation against another bitstream and writes
/// the result into `self`. If the other bitstream ends before `self,`, the
/// remaining bits of `self` are cleared.
///
/// # Type Parameters
///
/// - `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
///   or some other bit producer as desired.
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

/// Performs the Boolean `OR` operation against another bitstream and writes the
/// result into `self`. If the other bitstream ends before `self`, the remaining
/// bits of `self` are not affected.
///
/// # Type Parameters
///
/// - `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
///   or some other bit producer as desired.
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

/// Performs the Boolean `XOR` operation against another bitstream and writes
/// the result into `self`. If the other bitstream ends before `self`, the
/// remaining bits of `self` are not affected.
///
/// # Type Parameters
///
/// - `I: IntoIterator<Item=bool>`: A stream of bits, which may be a `BitSlice`
///   or some other bit producer as desired.
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

/// Indexes a single bit by semantic count. The index must be less than the
/// length of the `BitSlice`.
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

	fn index(&self, index: RangeInclusive<usize>) -> &Self::Output {
		let start = *index.start();
		//  This check can never fail, due to implementation details of
		//  `BitPtr<T>`.
		if let Some(end) = index.end().checked_add(1) {
			&self[start .. end]
		}
		else {
			&self[start ..]
		}
	}
}

impl<C, T> IndexMut<RangeInclusive<usize>> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, index: RangeInclusive<usize>) -> &mut Self::Output {
		let start = *index.start();
		//  This check can never fail, due to implementation details of
		//  `BitPtr<T>`.
		if let Some(end) = index.end().checked_add(1) {
			&mut self[start .. end]
		}
		else {
			&mut self[start ..]
		}
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
	fn index_mut(
		&mut self,
		RangeFrom { start }: RangeFrom<usize>,
	) -> &mut Self::Output {
		let len = self.len();
		&mut self[start .. len]
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
	fn index_mut(
		&mut self,
		RangeTo { end }: RangeTo<usize>,
	) -> &mut Self::Output {
		&mut self[0 .. end]
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
		RangeToInclusive { end }: RangeToInclusive<usize>,
	) -> &mut Self::Output {
		&mut self[0 ..= end]
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
	/// Negate an arbitrary positive number (first bit unset).
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
		let one: &[T] = &[T::bits(true)];
		let one_bs: &BitSlice<C, T> = one.into();
		AddAssign::add_assign(&mut *self, &one_bs[.. 1]);
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
	/// // assert_eq!(bits.as_ref(), &[!0, !0]);
	/// assert_eq!(new_bits.as_ref(), &[0x3F, 0xFC]);
	/// ```
	fn not(self) -> Self::Output {
		match self.bitptr().domain_mut() {
			BitDomainMut::Empty => {},
			BitDomainMut::Minor(head, elt, tail) => {
				for n in *head .. *tail {
					elt.invert_bit::<C>(n.idx());
				}
			},
			BitDomainMut::Major(h, head, body, tail, t) => {
				for n in *h .. T::BITS {
					head.invert_bit::<C>(n.idx());
				}
				for elt in body {
					*elt = !*elt;
				}
				for n in 0 .. *t {
					tail.invert_bit::<C>(n.idx());
				}
			},
			BitDomainMut::PartialHead(h, head, body) => {
				for n in *h .. T::BITS {
					head.invert_bit::<C>(n.idx());
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
					tail.invert_bit::<C>(n.idx());
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
	/// assert_eq!(bits.as_ref(), &[0b01_011_101, 0b001_000_01]);
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
		//  If the shift amount is an even multiple of the element width, use
		//  `ptr::copy` instead of a bitwise crawl.
		if shamt & T::MASK as usize == 0 {
			//  Compute the shift distance measured in elements.
			let offset = shamt.shr(T::INDX);
			//  Compute the number of elements that will remain.
			let rem = self.as_ref().len().saturating_sub(offset);
			//  Clear the bits after the tail cursor before the move.
			for n in *self.bitptr().tail() .. T::BITS {
				self.as_mut()[len.saturating_sub(1)].set::<C>(n.idx(), false);
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
			let body: *const T = &self.as_ref()[offset];
			//  Pointer to the back of the slice that will be zero-filled.
			let tail: *mut T = &mut self.as_mut()[rem];
			unsafe {
				ptr::copy(body, head, rem);
				ptr::write_bytes(tail, 0, offset);
			}
			return;
		}
		//  Otherwise, crawl.
		for (to, from) in (shamt .. len).enumerate() {
			let val = self[from];
			self.set(to, val);
		}
		for bit in (len.saturating_sub(shamt)) .. len {
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
	/// assert_eq!(bits.as_ref(), &[0b01_000_00_1, 0b011_101_01])
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
		//  IF the shift amount is an even multiple of the element width, use
		//  `ptr::copy` instead of a bitwise crawl.
		if shamt & T::MASK as usize == 0 {
			//  Compute the shift amount measured in elements.
			let offset = shamt >> T::INDX;
			// Compute the number of elements that will remain.
			let rem = self.as_ref().len().saturating_sub(offset);
			//  Clear the bits ahead of the head cursor before the move.
			for n in 0 .. *self.bitptr().head() {
				self.as_mut()[0].set::<C>(n.idx(), false);
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
			let body: *mut T = &mut self.as_mut()[offset];
			unsafe {
				ptr::copy(head, body, rem);
				ptr::write_bytes(head, 0, offset);
			}
			return;
		}
		//  Otherwise, crawl.
		for (from, to) in (shamt .. len).enumerate().rev() {
			let val = self[from];
			self.set(to, val);
		}
		for bit in 0 .. shamt {
			self.set(bit, false);
		}
	}
}

/** Write reference to a single bit.

Rust requires that `DerefMut` produce the plain address of a value which can be
written with a `memcpy`, so, there is no way to make plain write assignments
work nicely in Rust. This reference structure is the second best option.

It contains a write reference to a single-bit slice, and a local cache `bool`.
This structure `Deref`s to the local cache, and commits the cache to the slice
on drop. This allows writing to the guard with `=` assignment.
**/
#[derive(Debug)]
pub struct BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	slot: &'a mut BitSlice<C, T>,
	bit: bool,
	_m: PhantomData<*mut T>,
}

/// Read from the local cache.
impl<'a, C, T> Deref for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Target = bool;

	fn deref(&self) -> &Self::Target {
		&self.bit
	}
}

/// Write to the local cache.
impl<'a, C, T> DerefMut for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.bit
	}
}

/// Commit the local cache to the backing slice.
impl<'a, C, T> Drop for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn drop(&mut self) {
		self.slot.set(0, self.bit);
	}
}

/// This type is a mutable reference with extra steps, so, it should be moveable
/// but not shareable.
unsafe impl<'a, C, T> Send for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// State keeper for chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<BigEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.next_back(), Some(&bits[5 ..]));
	/// assert_eq!(chunks.next_back(), Some(&bits[.. 5]));
	/// assert!(chunks.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Chunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<LittleEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.next(), Some(&bits[.. 5]));
	/// assert_eq!(chunks.next(), Some(&bits[5 ..]));
	/// assert!(chunks.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut chunks = bits.chunks(5);
	/// assert_eq!(chunks.size_hint(), (2, Some(2)));
	/// chunks.next();
	/// assert_eq!(chunks.size_hint(), (1, Some(1)));
	/// chunks.next();
	/// assert_eq!(chunks.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.chunks(3).count(), 3);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut chunks = bits.chunks(3);
	/// assert_eq!(chunks.nth(1), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks.nth(0), Some(&bits[6 ..]));
	/// assert!(chunks.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		use core::cmp::min;
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| min(s, len))
			.unwrap_or(len);
		let out = &self.inner[start .. end];
		self.inner = &self.inner[end ..];
		Some(out)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.chunks(3).last(), Some(&bits[6 ..]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Debug)]
pub struct ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(len - size);
		self.inner = head;
		Some(tail)
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (n, r) = (len / self.width, len % self.width);
		let len = n + (r > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		use core::cmp::min;
		let (start, ovf) = n.overflowing_mul(self.width);
		let len = self.inner.len();
		if start >= len || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let end = start.checked_add(self.width)
			.map(|s| min(s, len))
			.unwrap_or(len);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (_, nth) = head.split_at_mut(end - start);
		self.inner = tail;
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for exact chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.remainder(), &bits[6 ..]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next_back(), Some(&bits[3 .. 6]));
	/// assert_eq!(chunks_exact.next_back(), Some(&bits[0 .. 3]));
	/// assert!(chunks_exact.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
		Some(tail)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<LittleEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.next(), Some(&bits[0 .. 3]));
	/// assert_eq!(chunks_exact.next(), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.size_hint(), (2, Some(2)));
	/// chunks_exact.next();
	/// assert_eq!(chunks_exact.size_hint(), (1, Some(1)));
	/// chunks_exact.next();
	/// assert_eq!(chunks_exact.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.chunks_exact(3).count(), 2);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.as_bitslice::<BigEndian>();
	/// let mut chunks_exact = bits.chunks_exact(3);
	/// assert_eq!(chunks_exact.nth(1), Some(&bits[3 .. 6]));
	/// assert!(chunks_exact.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (_, tail) = self.inner.split_at(start);
		self.inner = tail;
		self.next()
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.chunks_exact(3).last(), Some(&bits[3 .. 6]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable exact chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Debug)]
pub struct ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the back of th eslice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		unimplemented!()
	}
}

impl<'a, C, T> ExactSizeIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for ChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len() / self.width;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (_, tail) = tmp.split_at_mut(start);
		self.inner = tail;
		self.next()
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
}

impl<'a, C, T> Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Accesses the `BitPtr` representation of the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The `BitPtr` representation of the remaining slice.
	//  The linter is incorrect; this method is absolutely used.
	#[allow(dead_code)]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		self.inner.bitptr()
	}
}

impl<'a, C, T> DoubleEndedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next bit from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last bit in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.as_bitslice::<BigEndian>()[6 ..];
	/// let mut iter = bits.iter();
	/// assert!(iter.next_back().unwrap());
	/// assert!(!iter.next_back().unwrap());
	/// assert!(iter.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		self.inner.split_last().map(|(b, r)| {
			self.inner = r;
			b
		})
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Iter<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	/// Advances the iterator by one, returning the first bit in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading bit in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.as_bitslice::<LittleEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.split_first().map(|(b, r)| {
			self.inner = r;
			b
		})
	}

	/// Hints at the number of bits remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum bits remaining.
	/// - `Option<usize>`: The maximum bits remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &0x4Bu8.as_bitslice::<BigEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		(len, Some(len))
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of bits remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.iter().count(), 8);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` bits, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of bits to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// bits.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.as_bitslice::<BigEndian>();
	/// let mut iter = bits.iter();
	/// assert!(iter.nth(6).unwrap());
	/// assert!(!iter.nth(0).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		self.inner = &self.inner[n ..];
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert!(bits.iter().last().unwrap());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for reverse chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<BigEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.next_back(), Some(&bits[.. 3]));
	/// assert_eq!(rchunks.next_back(), Some(&bits[3 ..]));
	/// assert!(rchunks.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let rem = len % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let (head, tail) = self.inner.split_at(size);
		self.inner = tail;
		Some(head)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunks<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<LittleEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.next(), Some(&bits[3 ..]));
	/// assert_eq!(rchunks.next(), Some(&bits[.. 3]));
	/// assert!(rchunks.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let len = self.inner.len();
		let size = min(len, self.width);
		let (head, tail) = self.inner.split_at(len - size);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut rchunks = bits.rchunks(5);
	/// assert_eq!(rchunks.size_hint(), (2, Some(2)));
	/// rchunks.next();
	/// assert_eq!(rchunks.size_hint(), (1, Some(1)));
	/// rchunks.next();
	/// assert_eq!(rchunks.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.rchunks(3).count(), 3);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.as_bitslice::<BigEndian>();
	/// let mut rchunks = bits.rchunks(3);
	/// assert_eq!(rchunks.nth(2), Some(&bits[0 .. 2]));
	/// assert!(rchunks.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		// Can't underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let nth = &self.inner[start .. end];
		self.inner = &self.inner[.. start];
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.rchunks(3).last(), Some(&bits[.. 2]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable reverse chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Debug)]
pub struct RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() {
			return None;
		}
		let rem = self.inner.len() % self.width;
		let size = if rem == 0 { self.width } else { rem };
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(size);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		use core::cmp::min;
		if self.inner.is_empty() {
			return None;
		}
		let size = min(self.inner.len(), self.width);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - size);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.inner.is_empty() {
			return (0, Some(0));
		}
		let len = self.inner.len();
		let (len, rem) = (len / self.width, len % self.width);
		let len = len + (rem > 0) as usize;
		(len, Some(len))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		// Can't underflow because of the check above
		let end = self.inner.len() - end;
		let start = end.checked_sub(self.width).unwrap_or(0);
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(start);
		let (nth, _) = tail.split_at_mut(end - start);
		self.inner = head;
		Some(nth)
	}

	/// Consumes the iterator, returning only the final chunk.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last chunk in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for reverse exact iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The remaining slice that the iteration will not include.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.remainder(), &bits[.. 2]);
	/// ```
	pub fn remainder(&self) -> &'a BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next_back(), Some(&bits[2 .. 5]));
	/// assert_eq!(rchunks_exact.next_back(), Some(&bits[5 .. 8]));
	/// assert!(rchunks_exact.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.width);
		self.inner = tail;
		Some(head)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExact<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 1u8.as_bitslice::<LittleEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.next(), Some(&bits[5 .. 8]));
	/// assert_eq!(rchunks_exact.next(), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, tail) = self.inner.split_at(self.inner.len() - self.width);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.size_hint(), (2, Some(2)));
	/// rchunks_exact.next();
	/// assert_eq!(rchunks_exact.size_hint(), (1, Some(1)));
	/// rchunks_exact.next();
	/// assert_eq!(rchunks_exact.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.rchunks_exact(3).count(), 2);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// let mut rchunks_exact = bits.rchunks_exact(3);
	/// assert_eq!(rchunks_exact.nth(1), Some(&bits[2 .. 5]));
	/// assert!(rchunks_exact.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let (head, _) = self.inner.split_at(self.inner.len() - end);
		self.inner = head;
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert!(bits.iter().last().unwrap());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for mutable reverse exact chunked iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Debug)]
pub struct RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a mut BitSlice<C, T>,
	/// The excess of the original `BitSlice`, which is not iterated.
	extra: &'a mut BitSlice<C, T>,
	/// The width of the chunks.
	width: usize,
}

impl<'a, C, T> RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the remainder of the original slice, which will not be included
	/// in the iteration.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The remaining slice that iteration will not include.
	pub fn into_remainder(self) -> &'a mut BitSlice<C, T> {
		self.extra
	}
}

impl<'a, C, T> DoubleEndedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next chunk from the front of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last chunk in the slice, if any.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let (head, tail) = tmp.split_at_mut(self.width);
		self.inner = tail;
		Some(head)
	}
}

impl<'a, C, T> ExactSizeIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for RChunksExactMut<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a mut BitSlice<C, T>;

	/// Advances the iterator by one, returning the first chunk in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading chunk in the iterator, if any.
	fn next(&mut self) -> Option<Self::Item> {
		if self.inner.len() < self.width {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, tail) = tmp.split_at_mut(tlen - self.width);
		self.inner = head;
		Some(tail)
	}

	/// Hints at the number of chunks remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum chunks remaining.
	/// - `Option<usize>`: The maximum chunks remaining.
	fn size_hint(&self) -> (usize, Option<usize>) {
		let n = self.inner.len() / self.width;
		(n, Some(n))
	}

	/// Counts how many chunks are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of chunks remaining in the iterator.
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` chunks, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of chunks to skip, before producing the next bit after
	///   skips. If this overshoots the iterator’s remaining length, then the
	///   iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// chunks.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_mul(self.width);
		if end >= self.inner.len() || ovf {
			self.inner = BitSlice::empty_mut();
			return None;
		}
		let tmp = mem::replace(&mut self.inner, BitSlice::empty_mut());
		let tlen = tmp.len();
		let (head, _) = tmp.split_at_mut(tlen - end);
		self.inner = head;
		self.next()
	}

	/// Consumes the iterator, returning only the final bit.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last bit in the iterator slice, if any.
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/// State keeper for sliding-window iteration over a `BitSlice`.
///
/// # Type Parameters
///
/// - `C: Cursor`: The bit-order type of the underlying `BitSlice`.
/// - `T: 'a + BitStore`: The storage type of the underlying `BitSlice`.
///
/// # Lifetimes
///
/// - `'a`: The lifetime of the underlying `BitSlice`.
#[derive(Clone, Debug)]
pub struct Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// The `BitSlice` being iterated.
	inner: &'a BitSlice<C, T>,
	/// The width of the windows.
	width: usize,
}

impl<'a, C, T> DoubleEndedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Produces the next window from the back of the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The last window in the slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let store: &[u8] = &[0b0010_1101];
	/// let bits: &BitSlice = store.into();
	/// let mut windows = bits[2 .. 7].windows(3);
	/// assert_eq!(windows.next_back(), Some(&bits[4 .. 7]));
	/// assert_eq!(windows.next_back(), Some(&bits[3 .. 6]));
	/// assert_eq!(windows.next_back(), Some(&bits[2 .. 5]));
	/// assert!(windows.next_back().is_none());
	/// ```
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.inner.is_empty() || self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			return None;
		}
		let len = self.inner.len();
		let out = &self.inner[len - self.width ..];
		self.inner = &self.inner[.. len - 1];
		Some(out)
	}
}

/// Mark that the iterator has an exact size.
impl<'a, C, T> ExactSizeIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

/// Mark that the iterator will not resume after halting.
impl<'a, C, T> FusedIterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Windows<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a BitSlice<C, T>;

	/// Advances the iterator by one, returning the first window in it (if any).
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// The leading window in the iterator, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &1u8.as_bitslice::<LittleEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.inner.len() {
			self.inner = BitSlice::empty();
			None
		}
		else {
			let out = &self.inner[.. self.width];
			self.inner = &self.inner[1 ..];
			Some(out)
		}
	}

	/// Hints at the number of windows remaining in the iterator.
	///
	/// Because the exact size is always known, this always produces
	/// `(len, Some(len))`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// - `usize`: The minimum windows remaining.
	/// - `Option<usize>`: The maximum windows remaining.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = &0x4Bu8.as_bitslice::<BigEndian>()[.. 2];
	/// let mut iter = bits.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.inner.len();
		if self.width > len {
			(0, Some(0))
		}
		else {
			let len = len - self.width + 1;
			(len, Some(len))
		}
	}

	/// Counts how many windows are live in the iterator, consuming it.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of windows remaining in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.iter().count(), 8);
	/// ```
	fn count(self) -> usize {
		self.len()
	}

	/// Advances the iterator by `n` windows, starting from zero.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `n`: The number of windows to skip, before producing the next bit
	///   after the skips. If this overshoots the iterator’s remaining length,
	///   then the iterator is marked empty before returning `None`.
	///
	/// # Returns
	///
	/// If `n` does not overshoot the iterator’s bounds, this produces the `n`th
	/// bit after advancing the iterator to it, discarding the intermediate
	/// windows.
	///
	/// If `n` does overshoot the iterator’s bounds, this empties the iterator
	/// and returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 2u8.as_bitslice::<BigEndian>();
	/// let mut iter = bits.iter();
	/// assert!(iter.nth(6).unwrap());
	/// assert!(!iter.nth(0).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = n.overflowing_add(self.width);
		if end > self.inner.len() || ovf {
			self.inner = BitSlice::empty();
			return None;
		}
		let out = &self.inner[n .. end];
		self.inner = &self.inner[n + 1 ..];
		Some(out)
	}

	/// Consumes the iterator, returning only the final window.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The last window in the iterator slice, if any.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x4Bu8.as_bitslice::<BigEndian>();
	/// assert_eq!(bits.windows(3).last(), Some(&bits[5 ..]));
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}
