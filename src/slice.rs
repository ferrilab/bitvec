/*! `BitSlice` Wide Reference

This module defines semantic operations on `[u1]`, in contrast to the mechanical
operations defined in `BitPtr`.

The `&BitSlice` handle has the same size and general layout as the standard Rust
slice handle `&[T]`. Its binary layout is wholly incompatible with the layout of
Rust slices, and must never be interchanged except through the provided APIs.
!*/

use crate::{
	bits::BitsMut,
	cursor::{
		Cursor,
		Local,
	},
	domain::*,
	pointer::BitPtr,
	store::{
		BitAccess,
		BitStore,
		IntoBitIdx,
		Word,
	},
};

#[cfg(feature = "alloc")]
use {
	crate::vec::BitVec,
	alloc::borrow::ToOwned,
};

use core::{
	cmp,
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
	marker::PhantomData,
	ops::{
		Deref,
		DerefMut,
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
let bslice: &BitSlice<Local, u8> = [1u8, 254].bits::<Local>();
```

Bit slices are either mutable or shared. The shared slice type is
`&BitSlice<C, T>`, while the mutable slice type is `&mut BitSlice<C, T>`. For
example, you can mutate bits in the memory to which a mutable `BitSlice` points:

```rust
use bitvec::prelude::*;

let mut base = [0u8, 0, 0, 0];
{
 let bs = base.bits_mut::<BigEndian>();
 bs.set(13, true);
 eprintln!("{:?}", bs.as_ref());
 assert!(bs[13]);
}
assert_eq!(base[1], 4);
```

# Type Parameters

- `C`: An implementor of the `Cursor` trait. This type is used to convert
  semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T`: An implementor of the `BitStore` trait: `u8`, `u16`, `u32`, or `u64`
  (64-bit systems only). This is the actual type in memory that the slice will
  use to store data.

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
pub struct BitSlice<C = Local, T = Word>
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
	/// # Lifetimes
	///
	/// The lifetime is dictated by the bind site into which the slice is
	/// returned. As empty slices are essentially statics, and can never refer
	/// to data, this is not a soundness hole.
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
	/// # Lifetimes
	///
	/// The lifetime is dictated by the bind site into which the slice is
	/// returned. As empty slices are essentially statics, and can never refer
	/// to data, this is not a soundness hole.
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

	/// Produces an immutable `BitSlice` reference over a single element.
	///
	/// This is a reference transformation: the `&BitSlice` constructed by this
	/// method will govern the element referred to by the reference parameter.
	///
	/// The cursor must be specified at the call site. The element type cannot
	/// be changed. The [`Bits::bits`] method performs the same operation and
	/// may be easier to call.
	///
	/// # Parameters
	///
	/// - `elt`: A reference to an element over which the `&BitSlice` will be
	///   created.
	///
	/// # Returns
	///
	/// A `&BitSlice` reference spanning the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let elt: Word = 0;
	/// let bs: &BitSlice = BitSlice::from_element(&elt);
	/// assert_eq!(bs.as_ptr(), &elt);
	/// ```
	///
	/// [`Bits::bits`]: ../bits/trait.Bits.html#tymethod.bits
	pub fn from_element(elt: &T) -> &Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0.idx(), T::BITS as usize)
		}.into_bitslice()
	}

	/// Produces a mutable `BitSlice` reference over a single element.
	///
	/// The cursor must be specified at the call site. The element type cannot
	/// be changed. The [`BitsMut::bits_mut`] method performs the same
	/// operation and may be easier to call.
	///
	/// # Parameters
	///
	/// - `elt`: A mutable reference to an element over which the
	///   `&mut BitSlice` will be created.
	///
	/// # Returns
	///
	/// A `&mut BitSlice` reference spanning the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut elt: Word = 0;
	/// let eltptr = &elt as *const Word;
	/// let bs = BitSlice::<LittleEndian, _>::from_element_mut(&mut elt);
	/// assert_eq!(bs.as_ptr(), eltptr);
	/// assert!(bs.not_any());
	/// bs.set(0, true);
	/// assert!(bs.any());
	/// assert_eq!(elt, 1);
	/// ```
	///
	/// [`BitsMut::bits_mut`]: ../bits/trait.BitsMut.html#tymethod.bits_mut
	pub fn from_element_mut(elt: &mut T) -> &mut Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0.idx(), T::BITS as usize)
		}.into_bitslice_mut()
	}

	/// Wraps a `&[T]` slice reference in a `&BitSlice<C, T>`.
	///
	/// The cursor must be specified at the call site. The element type cannot
	/// be changed. The [`Bits::as_bits`] method performs the same operation
	/// and may be easier to call.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `&BitSlice` reference spanning the provided slice.
	///
	/// # Edge Cases
	///
	/// If `src` is exactly the maximum number of elements that a bit slice can
	/// possibly represent, then the slice will be constructed, but it will not
	/// be able to address the final bit.
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
	/// [`Bits::bits`]: ../bits/trait.Bits.html#tymethod.bits
	pub fn from_slice(slice: &[T]) -> &Self {
		let len = slice.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"BitSlice cannot address {} full elements",
			len,
		);
		//  This shift will never overflow, because `BitPtr::MAX_ELTS`
		//  constrains `len` to be `(!0 >> (3 + T::INDX)) + 1`, so upshifting
		//  back up by `T::INDX` is infallible.
		let bits = len << (T::INDX as usize);
		//  However, at `MAX_ELTS`, `bits` overflows `MAX_INDX`, and must be
		//  clamped.
		BitPtr::new(
			slice.as_ptr(),
			0.idx(),
			cmp::min(bits, BitPtr::<T>::MAX_INDX),
		).into_bitslice()
	}

	/// Wraps a `&mut [T]` in a `&mut BitSlice<C, T>`.
	///
	/// The cursor must be specified at the call site. The element type cannot
	/// be changed. The [`BitsMut::as_bits_mut`] method performs the same
	/// operation and may be easier to call.
	///
	/// # Parameters
	///
	/// - `src`: The elements over which the new `BitSlice` will operate.
	///
	/// # Returns
	///
	/// A `&mut BitSlice` reference spanning the provided slice.
	///
	/// # Edge Cases
	///
	/// If `src` is exactly the maximum number of elements that a bit slice can
	/// possibly represent, then the slice will be constructed, but it will not
	/// be able to address the final bit.
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
	/// [`BitsMut::bits_mut`]: ../bits/trait.BitsMut.html#tymethod.bits_mut
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
	/// let bs = store.bits::<BigEndian>();
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
	/// let bs = 0u8.bits::<BigEndian>();
	/// assert!(!bs.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.bitptr().is_empty()
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
	/// assert!(128u8.bits::<BigEndian>().first().unwrap());
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
	/// let bits = store.bits::<BigEndian>();
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
			return None;
		}
		//  Implementation note: `incr_head` is faster than going through the
		//  `Index<Range<_>>` implementations, which are required to perform
		//  bounds checks.
		unsafe {
			Some((
				self.get_unchecked(0),
				self.bitptr().incr_head().into_bitslice(),
			))
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
	/// let bits = store.bits_mut::<LittleEndian>();
	/// assert!(!bits[0]);
	/// *bits.at(0) = true;
	/// let (h, t) = bits.split_first_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(bool, &mut Self)> {
		if self.is_empty() {
			return None;
		}
		unsafe {
			Some((
				self.get_unchecked(0),
				self.bitptr().incr_head().into_bitslice_mut(),
			))
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
	/// let bits = 1u8.bits::<BigEndian>();
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
		match self.len() {
			0 => None,
			len => unsafe {
				Some((
					self.get_unchecked(len - 1),
					self.bitptr().decr_tail().into_bitslice(),
				))
			},
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
	/// let bits = store.bits_mut::<LittleEndian>();
	/// assert!(!bits[7]);
	/// *bits.at(7) = true;
	/// let (h, t) = bits.split_last_mut().unwrap();
	/// assert!(h);
	/// assert_eq!(t.len(), 7);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(bool, &mut Self)> {
		match self.len() {
			0 => None,
			len => unsafe {
				Some((
					self.get_unchecked(len - 1),
					self.bitptr().decr_tail().into_bitslice_mut(),
				))
			},
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
	/// assert!(1u8.bits::<BigEndian>().last().unwrap());
	/// ```
	pub fn last(&self) -> Option<bool> {
		match self.len() {
			0 => None,
			len => self.get(len - 1),
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
	/// let bits = 8u8.bits::<BigEndian>();
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
	/// let bits = &src.bits::<BigEndian>()[2 .. 4];
	/// assert_eq!(bits.len(), 2);
	/// assert!(unsafe { bits.get_unchecked(5) });
	/// ```
	///
	/// [`get`]: #method.get
	pub unsafe fn get_unchecked(&self, index: usize) -> bool {
		let bitptr = self.bitptr();
		let (elt, bit) = bitptr.head().offset(index as isize);
		let data_ptr = bitptr.pointer().n();
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
	/// let bits = store.bits_mut::<BigEndian>();
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
	///  let bits = &mut src.bits_mut::<BigEndian>()[2 .. 4];
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
		let data_ptr = bitptr.pointer().n();
		(&*(data_ptr.offset(elt))).set::<C>(bit, value);
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
	/// - `&mut self`: The slice handle will be locked until the structure
	///   produced by this method goes out of scope. See the Usage section.
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
	/// let bits = src.bits_mut::<BigEndian>();
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
	/// let bits = src.bits_mut::<BigEndian>();
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
	/// let bits = src.bits::<BigEndian>();
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
	/// The pointer produced by this function is not required to uniquely reach
	/// the referent element; a neighboring `&mut BitSlice` may also produce a
	/// pointer to it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8; 4];
	/// let src_ptr = src.as_mut_ptr();
	/// let bits = src.bits_mut::<BigEndian>();
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
	/// let bits = store.bits_mut::<BigEndian>();
	/// assert!(!bits[0]);
	/// assert!(bits[2]);
	/// bits.swap(0, 2);
	/// assert!(bits[0]);
	/// assert!(!bits[2]);
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) {
		assert!(a < self.len(), "Index {} out of bounds: {}", a, self.len());
		assert!(b < self.len(), "Index {} out of bounds: {}", b, self.len());
		unsafe {
			let (bit_a, bit_b) = (self.get_unchecked(a), self.get_unchecked(b));
			self.set_unchecked(a, bit_b);
			self.set_unchecked(b, bit_a);
		}
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
	///   let bits = src.bits_mut::<BigEndian>();
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
			//  At this point in the loop body, the indices are known to be good
			//  and can have their bounds checks completely elided.
			let end = len - 1;
			unsafe {
				//  Access the bits
				let (h, t) = (cur.get_unchecked(0), cur.get_unchecked(end));
				//  Set the bits
				cur.set_unchecked(0, t);
				cur.set_unchecked(end, h);
				//  Shrink the slice.
				cur = cur.bitptr().incr_head().decr_tail().into_bitslice_mut();
			}
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
	/// let bits = 15u8.bits::<BigEndian>();
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
	/// let bits = 0xA6u8.bits::<BigEndian>();
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
	/// let bits = 0xA6u8.bits::<BigEndian>();
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
	/// let bits = src.bits_mut::<BigEndian>();
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
			let tmp = unsafe { self.get_unchecked(0) };
			for n in 1 .. len {
				unsafe {
					let bit = self.get_unchecked(n);
					self.set_unchecked(n - 1, bit);
				}
			}
			unsafe { self.set_unchecked(len - 1, tmp); }
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
	/// let bits = src.bits_mut::<BigEndian>();
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
			let tmp = unsafe { self.get_unchecked(len - 1) };
			//  of `len` steps
			for n in (0 .. len - 1).rev() {
				unsafe {
					let bit = self.get_unchecked(n);
					self.set_unchecked(n + 1, bit);
				}
			}
			unsafe { self.set_unchecked(0, tmp); }
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
	/// let bits = 0xFDu8.bits::<BigEndian>();
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
	/// let bits = 0x40u8.bits::<BigEndian>();
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

	/// Tests if *any* bit in the slice is clear (logical `¬∧`).
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
	/// Whether any bit in the slice domain is clear.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0xFDu8.bits::<BigEndian>();
	/// assert!(!bits[.. 4].not_all());
	/// assert!(bits[4 ..].not_all());
	/// ```
	pub fn not_all(&self) -> bool {
		!self.all()
	}

	/// Tests if *all* bits in the slice are clear (logical `¬∨`).
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
	/// Whether all bits in the slice domain are clear.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x40u8.bits::<BigEndian>();
	/// assert!(!bits[.. 4].not_any());
	/// assert!(bits[4 ..].not_any());
	/// ```
	pub fn not_any(&self) -> bool {
		!self.any()
	}

	/// Tests whether the slice has some, but not all, bits set and some, but
	/// not all, bits clear.
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
	/// let bits = 0b111_000_10u8.bits::<BigEndian>();
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
	/// let bits = [0xFDu8, 0x25].bits::<BigEndian>();
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
	/// let bits = [0xFDu8, 0x25].bits::<BigEndian>();
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
	/// let bits = src.bits_mut::<BigEndian>();
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
	///  let bits = src.bits_mut::<BigEndian>();
	///  bits.for_each(|idx, _bit| idx % 3 == 0);
	/// }
	/// assert_eq!(src, 0b1001_0010);
	/// ```
	pub fn for_each<F>(&mut self, func: F)
	where F: Fn(usize, bool) -> bool {
		for idx in 0 .. self.len() {
			unsafe {
				let tmp = self.get_unchecked(idx);
				self.set_unchecked(idx, func(idx, tmp));
			}
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
	/// - `addend`: A stream of bits. When this is another `BitSlice`, iteration
	///   proceeds from left to right.
	///
	/// # Return
	///
	/// The final carry bit is returned as the carry-out signal.
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
	/// let ab = &mut a.bits_mut::<LittleEndian>()[.. 4];
	/// let bb = &    b.bits::<LittleEndian>()[.. 4];
	/// let c = ab.add_assign_reverse(bb);
	/// assert!(c);
	/// assert_eq!(a, 0b0000_0110u8);
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
	/// bit sets, you should probably use a crate that directly targets that
	/// behavior.
	///
	/// [ripple-carry adder]: https://en.wikipedia.org/wiki/Ripple-carry_adder
	pub fn add_assign_reverse<I>(&mut self, addend: I) -> bool
	where I: IntoIterator<Item=bool> {
		use core::iter;
		//  See AddAssign::add_assign for algorithm details
		let mut c = false;
		let len = self.len();
		let zero = iter::repeat(false);
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

	/// Collects a `BitSlice` into native memory elements.
	///
	/// This produces an immediate value of the underlying memory type, filled
	/// with the contents of `self` according to the `Cursor` type of `self`.
	///
	/// Use [`as_native_with_cursor`] if you need to collect a bitslice with one
	/// cursor into an immediate value using another cursor.
	///
	/// If `self` is shorter than `B`’s bit capacity, the remaining bits in the
	/// return object `B` will be zero; if `self` is longer, then the remaining
	/// bits in `self` are ignored.
	///
	/// Note that this method always begins at the `Cursor` 0-index of the
	/// returned data; for example, the `BigEndian` cursor writes from the MSbit
	/// down to the LSbit, so you would have to downshift the returned value in
	/// order for it to have the numeric value you might expect.
	///
	/// # Parameters
	///
	/// - `&self`: A handle to any `BitSlice` which will be collected into an
	///   immediate memory value. This handle is not required to describe a
	///   bit-slice starting at the edge of a memory element; any span of bits
	///   in memory is valid.
	///
	/// # Returns
	///
	/// An instance of `B` that has had `self` transcribed into it. This method
	/// is semantically equivalent to `Iterator::collect`, but unlike most such
	/// implementations, it works with an immediate value on the call stack
	/// rather than a heap allocation.
	///
	/// # Type Parameters
	///
	/// - `B`: Some type which implements both `BitsMut` and `Default`. In
	///   practice, this is any of the four `T: BitStore` fundamentals, and
	///   arrays of them from length 0 up to and including 32. Note that this
	///   type is constrained to use the same fundamental as the slice itself
	///   does: A `BitSlice<_, u16>` cannot be collected into a `[u8; 2]`, for
	///   instance.
	///
	/// When type-level integers stabilize, this method will be able to produce
	/// any size array of `T: BitStore`. Until then, if you need to collect
	/// bit-slices longer than `[T: BitStore; 32]`, you will have to enable the
	/// `alloc` feature and use a `BitVec`.
	///
	/// [`as_native_with_cursor`]: #method.as_native_with_cursor
	///
	/// # Examples
	///
	/// These examples demonstrate that writing any `BitSlice` into native
	/// memory always starts at the native memory’s origin, even if the slice
	/// being copied does not.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bits = &(!0u8).bits::<BigEndian>()[2 ..];
	/// assert_eq!(bits.as_native::<[u8; 1]>(), [0xFC]);
	///
	/// let bits = &(!0u8).bits::<LittleEndian>()[2 ..];
	/// assert_eq!(bits.as_native::<[u8; 2]>(), [0x3F, 0]);
	/// ```
	pub fn as_native<B>(&self) -> B
	where B: BitsMut<Store = T> + Default {
		self.as_native_with_cursor::<B, C>()
	}

	/// Collects a `BitSlice` into native memory elements with some `Cursor`.
	///
	/// This method is exactly equivalent to [`as_native`], except that you may
	/// also specify the `Cursor` used to write bits from `self` into the
	/// produced object. This behavior is useful if you need to collect into a
	/// different `Cursor` ordering than the slice may be using, as
	/// [`change_cursor`] will only affect the order in which a bit-slice is
	/// iterated, but not the underlying memory representation.
	///
	/// See `as_native` for parameter and return documentation.
	///
	/// # Type Parameters
	///
	/// - `D`: The `Cursor` type to use when writing the bits of `self` into the
	///   return value `B`.
	///
	/// [`as_native`]: #method.as_native
	/// [`change_cursor`]: #method.change_cursor
	///
	/// # Examples
	///
	/// This example shows the result of using a different cursor than the
	/// original slice when collecting a slice into native memory.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = 0x2358u16.bits::<BigEndian>();
	/// let native = bits.as_native_with_cursor::<u16, LittleEndian>();
	/// assert_eq!(native, 0x1AC4);
	/// ```
	///
	/// This example traversed the bit pattern of `bits` from MSbit to LSbit,
	/// but collected that pattern into `native` from `LSbit` to `MSbit`,
	/// inverting its order.
	pub fn as_native_with_cursor<B, D>(&self) -> B
	where B: BitsMut<Store = T> + Default, D: Cursor {
		let mut out = B::default();
		let bits = out.bits_mut::<D>();
		for (idx, bit) in self.into_iter().enumerate().take(bits.len()) {
			unsafe { bits.set_unchecked(idx, bit); }
		}
		out
	}

	/// Accesses the backing storage of the `BitSlice` as a slice of its
	/// elements.
	///
	/// Note that this does *not* include any partial elements of the `BitSlice`
	/// in the produced element slice. `BitSlice` regions are permitted to be
	/// adjacent and to occupy different parts of the same element; as such,
	/// using them to obtain a view of the entire element beyond their
	/// boundaries is a memory safety violation.
	///
	/// Heuristically, this restriction is not considered likely to be a serious
	/// detriment in practice. If you need to view the underlying elements of a
	/// `BitSlice`, you likely also do not have a region with partial elements.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all the full elements that the `BitSlice` uses for storage.
	/// Partial elements at either edge are not included.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [1u8, 66];
	/// let bits = src.bits::<BigEndian>();
	///
	/// let accum = bits.as_slice()
	///   .iter()
	///   .map(|elt| elt.count_ones())
	///   .sum::<usize>();
	/// assert_eq!(accum, 3);
	/// ```
	///
	/// This demonstrates that the partial edges are not in the output slice.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, 1, 2];
	/// let bits = &src.bits::<BigEndian>()[4 .. 20];
	/// assert_eq!(bits.as_slice(), &[1]);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		match self.bitptr().domain() {
			| BitDomain::Empty
			| BitDomain::Minor(..) => &[],
			| BitDomain::Major(_, _, s, _, _)
			| BitDomain::PartialHead(_, _, s)
			| BitDomain::PartialTail(s, _, _)
			| BitDomain::Spanning(s)=> s,
		}
	}

	/// Accesses the underlying element store, including partial elements.
	///
	/// # Safety
	///
	/// This function is marked `unsafe` because it will access the entirety of
	/// elements to which the `BitSlice` handle does not necessarily have
	/// complete access. Two adjacent `BitSlice` handles that do not consider
	/// themselves aliasing because they govern different *bits* can
	/// nevertheless produce element slices that do alias the same element.
	///
	/// While this immutable references are free to alias each other, Rust
	/// forbids the construction of an immutable reference that aliases a
	/// mutable reference. This function is permitted to do so, and thus must be
	/// marked unsafe.
	///
	/// Note that constructing aliasing mutable references is undefined
	/// behavior, and the compiler is permitted to miscompile your crate if it
	/// can prove that you are doing so.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all elements, full and partial, in the `BitSlice`’s domain.
	pub unsafe fn as_total_slice(&self) -> &[T] {
		self.bitptr().as_slice()
	}

	/// Accesses the underlying store.
	///
	/// Note that this does *not* include any partial elements of the `BitSlice`
	/// in the produced element slice. `BitSlice` regions are permitted to be
	/// adjacent and to occupy different parts of the same element; as such,
	/// using them to obtain a view of the entire element beyond their
	/// boundaries is a memory safety violation.
	///
	/// Heuristically, this restriction is not considered likely to be a serious
	/// detriment in practice. If you need to view the underlying elements of a
	/// `BitSlice`, you likely also do not have a region with partial elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1u8, 64];
	/// let bits = src.bits_mut::<BigEndian>();
	/// for elt in bits.as_mut_slice() {
	///   *elt |= 2;
	/// }
	/// assert_eq!(&[3, 66], bits.as_slice());
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		match self.bitptr().domain_mut() {
			| BitDomainMut::Empty
			| BitDomainMut::Minor(..) => &mut [],
			| BitDomainMut::Major(_, _, s, _, _)
			| BitDomainMut::PartialHead(_, _, s)
			| BitDomainMut::PartialTail(s, _, _)
			| BitDomainMut::Spanning(s) => s
		}
	}

	/// Accesses the underlying element store, including partial elements.
	///
	/// # Safety
	///
	/// This function is marked `unsafe` because it will access the entirety of
	/// elements to which the `BitSlice` handle does not necessarily have
	/// complete access. Two adjacent `BitSlice` handles that do not consider
	/// themselves aliasing because they govern different *bits* can
	/// nevertheless produce element slices that do alias the same element.
	///
	/// Mutable references are never allowed to alias any other reference, but
	/// this function may create an aliased mutable reference if used
	/// improperly.
	///
	/// Note that constructing aliasing mutable references is undefined
	/// behavior, and the compiler is permitted to miscompile your crate if it
	/// can prove that you are doing so.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A slice of all elements, full and partial, in the `BitSlice`’s domain.
	pub unsafe fn as_total_mut_slice(&mut self) -> &mut [T] {
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
	/// - `D`: The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 2u8;
	/// let bits = src.bits::<BigEndian>();
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
	/// - `D` The new cursor type to use for the handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// *src.bits_mut::<BigEndian>().at(1) = true;
	/// assert_eq!(src, 64);
	/// src.bits_mut::<BigEndian>()
	///    .change_cursor_mut::<LittleEndian>()
	///    .set(1, true);
	/// assert_eq!(src, 66);
	/// ```
	pub fn change_cursor_mut<D>(&mut self) -> &mut BitSlice<D, T>
	where D: Cursor {
		self.bitptr().into_bitslice_mut()
	}

	/// Unconditionally copies a bit from one index to another.
	///
	/// This is equivalent to `self[to] = self[from]`.
	///
	/// # Safety
	///
	/// This function performs no bounds checks. It must only be called from
	/// within a checked context.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `from`: The index at which a bit will be unconditionally fetched.
	/// - `to`: The index at which the fetched bit will be unconditionally set.
	#[inline]
	pub(crate) unsafe fn copy(&mut self, from: usize, to: usize) {
		let bit = self.get_unchecked(from);
		self.set_unchecked(to, bit);
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
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
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
	/// let src = store.bits::<LittleEndian>();
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
	fn cmp(&self, rhs: &Self) -> cmp::Ordering {
		self.partial_cmp(rhs)
			.unwrap_or_else(|| unreachable!("`BitSlice` has a total ordering"))
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
	/// let rsrc = [0x10_08_04_00u32];
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

/// Allow comparison against the allocated form.
#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bits())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialEq<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bits())
	}
}

/** Compares two `BitSlice`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one slice to have a set bit where
the other has a clear bit. If the slices are different, the slice with the set
bit sorts greater than the slice with the clear bit.

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
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<cmp::Ordering> {
		for (l, r) in self.iter().zip(rhs.iter()) {
			match (l, r) {
				(true, false) => return Some(cmp::Ordering::Greater),
				(false, true) => return Some(cmp::Ordering::Less),
				_ => continue,
			}
		}
		self.len().partial_cmp(&rhs.len())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<cmp::Ordering> {
		(*self).partial_cmp(rhs)
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<cmp::Ordering> {
		self.partial_cmp(rhs.as_bits())
	}
}

#[cfg(feature = "alloc")]
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<cmp::Ordering> {
		self.partial_cmp(rhs.as_bits())
	}
}

/** Provides write access to all elements in the underlying storage, including
the partial head and tail elements if present.
**/
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
	/// let bits = src.bits_mut::<BigEndian>();
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

/** Provides read access to all elements in the underlying storage, including
the partial head and tail elements if present.
**/
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
	/// let bits = src.bits::<BigEndian>();
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

/** Prints the `BitSlice` for debugging.

The output is of the form `BitSlice<C, T> [ELT, *]` where `<C, T>` is the cursor
and element type, with square brackets on each end of the bits and all the
elements of the array printed in binary. The printout is always in semantic
order, and may not reflect the underlying buffer. To see the underlying buffer,
use `.as_ref()`.

The alternate character `{:#?}` prints each element on its own line, rather than
having all elements on the same line.
**/
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
	/// let bits = &src.bits::<LittleEndian>()[.. 18];
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

/** Prints the `BitSlice` for displaying.

This prints each element in turn, formatted in binary in semantic order (so the
first bit seen is printed first and the last bit seen is printed last). Each
element of storage is separated by a space for ease of reading.

The alternate character `{:#}` prints each element on its own line.

To see the in-memory representation, use `.as_ref()` to get access to the raw
elements and print that slice instead.
**/
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
	/// let bits = &src.bits::<BigEndian>()[.. 10];
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
					writer::<C, T>(&mut dbg, &mut w, elt, *head, *tail)
				},
				BitDomain::Major(h, head, body, tail, t) => {
					writer::<C, T>(&mut dbg, &mut w, head, *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, tail, 0, *t);
				},
				BitDomain::PartialHead(h, head, body) => {
					writer::<C, T>(&mut dbg, &mut w, head, *h, T::BITS);
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
				},
				BitDomain::PartialTail(body, tail, t) => {
					for elt in body {
						writer::<C, T>(&mut dbg, &mut w, elt, 0, T::BITS);
					}
					writer::<C, T>(&mut dbg, &mut w, tail, 0, *t);
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
	/// - `H`: The type of the hashing algorithm which receives the bits of
	///   `self`.
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		for bit in self {
			hasher.write_u8(bit as u8);
		}
	}
}

/** `BitSlice` is safe to move across thread boundaries, when atomic operations
 are enabled.

Consider this (contrived) example:

```rust
# #[cfg(feature = "std")] {
use bitvec::prelude::*;
use std::thread;

static mut SRC: u8 = 0;
# {
let bits = unsafe { SRC.bits_mut::<BigEndian>() };
let (l, r) = bits.split_at_mut(4);

let a = thread::spawn(move || l.set(2, true));
let b = thread::spawn(move || r.set(2, true));
a.join();
b.join();
# }

println!("{:02X}", unsafe { SRC });
# }
```

Without atomic operations, this is logically a data race. It *so happens*
that, on x86, the read/modify/write cycles used in the crate are *basically*
atomic by default, even when not specified as such. This is not necessarily
true on other architectures, however
**/
#[cfg(feature = "atomic")]
unsafe impl<C, T> Send for BitSlice<C, T>
where C: Cursor, T: BitStore {}

/** Unsynchronized racing reads are undefined behavior.

Because `BitSlice` can create aliasing pointers to the same underlying memory
element, sending a *read* reference to another thread is still a data race in
the event that a `&mut BitSlice` was fractured in a manner that created an
alias condition, one alias was frozen and sent to another thread, and then the
**non**-frozen alias, which remained on the origin thread, was used to write to
the aliased element.

Without enabling bit-granular access analysis in the compiler, this restriction
must remain in place even though *this library* knows that read operations will
never observe racing writes that *change memory*.
**/
#[cfg(feature = "atomic")]
unsafe impl<C, T> Sync for BitSlice<C, T>
where C: Cursor, T: BitStore {}

/** Write reference to a single bit.

Rust requires that `DerefMut` produce the plain address of a value which can be
written with a `memcpy`, so, there is no way to make plain write assignments
work nicely in Rust. This reference structure is the second best option.

It contains a write reference to a single-bit slice, and a local cache `bool`.
This structure `Deref`s to the local cache, and commits the cache to the slice
on drop. This allows writing to the guard with `=` assignment.

# Type Parameters

- `C`: The `Cursor` implementation of the `BitSlice` this guards.
- `T`: The `BitStore` implementation of the `BitSlice` this guards.

# Lifetimes

- `'a`: The lifetime of the `BitSlice` this guards.
**/
#[derive(Debug)]
pub struct BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	slot: &'a mut BitSlice<C, T>,
	bit: bool,
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
		unsafe { self.slot.set_unchecked(0, self.bit) };
	}
}

/// This type is a mutable reference with extra steps, so, it should be moveable
/// but not shareable.
#[cfg(feature = "atomic")]
unsafe impl<'a, C, T> Send for BitGuard<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

mod iter;
mod ops;

pub use iter::*;

#[cfg(test)]
mod tests;
