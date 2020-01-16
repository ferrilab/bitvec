/*! `BitSlice` Wide Reference

This module defines semantic operations on `[u1]`, in contrast to the mechanical
operations defined in `BitPtr`.

The `&BitSlice` handle has the same size and general layout as the standard Rust
slice handle `&[T]`. Its binary layout is wholly incompatible with the layout of
Rust slices, and must never be interchanged except through the provided APIs.
!*/

use crate::{
	access::BitAccess,
	domain::*,
	indices::Indexable,
	order::{
		BitOrder,
		Local,
	},
	pointer::BitPtr,
	store::BitStore,
};

use core::marker::PhantomData;

use either::Either;

/** A compact slice of bits, whose order and storage types can be customized.

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
let bslice: &BitSlice<_, _> = [1u8, 254u8].bits::<Msb0>();
```

Bit slices are either mutable or shared. The shared slice type is
`&BitSlice<O, T>`, while the mutable slice type is `&mut BitSlice<O, T>`. For
example, you can mutate bits in the memory to which a mutable `BitSlice` points:

```rust
use bitvec::prelude::*;

let mut base = [0u8, 0, 0, 0];
{
 let bs: &mut BitSlice<_, _> = base.bits_mut::<Msb0>();
 bs.set(13, true);
 eprintln!("{:?}", bs.as_ref());
 assert!(bs[13]);
}
assert_eq!(base[1], 4);
```

# Type Parameters

- `O`: An implementor of the `BitOrder` trait. This type is used to convert
  semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T`: An implementor of the `BitStore` trait: `u8`, `u16`, `u32`, or `u64`
  (64-bit systems only). This is the actual type in memory that the slice will
  use to store data.

# Safety

The `&BitSlice` reference handle has the same *size* as standard Rust slice
handles, but it is ***extremely value-incompatible*** with them. Attempting to
treat `&BitSlice<_, T>` as `&[T]` in any manner except through the provided APIs
is ***catastrophically*** unsafe and unsound.

[`BitVec`]: ../vec/struct.BitVec.html
[`Bits`]: ../bits/trait.Bits.html
[`BitsMut`]: ../bits/trait.BitsMut.html
[`From`]: https://doc.rust-lang.org/stable/std/convert/trait.From.html
[`bitvec!`]: ../macro.bitvec.html
**/
#[repr(transparent)]
pub struct BitSlice<O = Local, T = usize>
where O: BitOrder, T: BitStore {
	/// BitOrder type for selecting bits inside an element.
	_kind: PhantomData<O>,
	/// Element type of the slice.
	///
	/// eddyb recommends using `PhantomData<T>` and `[()]` instead of `[T]`
	/// alone.
	_type: PhantomData<T>,
	/// Slice of elements `T` over which the `BitSlice` has usage.
	_elts: [()],
}

impl<O, T> BitSlice<O, T>
where O: BitOrder, T: BitStore {
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
	#[inline]
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
	#[inline]
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
	/// let bs: &BitSlice<Local, _> = BitSlice::from_element(&elt);
	/// assert!(bs.all());
	/// ```
	#[inline]
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
	/// let bs: &mut BitSlice<Local, _> = BitSlice::from_element_mut(&mut elt);
	/// bs.set(0, false);
	/// assert!(!bs.all());
	/// ```
	#[inline]
	pub fn from_element_mut(elt: &mut T) -> &mut Self {
		unsafe {
			BitPtr::new_unchecked(elt, 0u8.idx(), T::BITS as usize)
		}.into_bitslice_mut()
	}

	/// Wraps a `&[T: BitStore]` in a `&BitSlice<O: BitOrder, T>`. The order must
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
	/// let bits = BitSlice::<Msb0, u8>::from_slice(&src[..]);
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

	/// Wraps a `&mut [T: BitStore]` in a `&mut BitSlice<O: BitOrder, T>`. The
	/// order must be specified by the call site. The element type cannot
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
	/// let bits = BitSlice::<Lsb0, u8>::from_slice_mut(&mut src[..]);
	/// //  The first bit is the LSb of the first element.
	/// assert!(bits[0]);
	/// bits.set(0, false);
	/// assert!(!bits[0]);
	/// assert_eq!(bits.as_ref(), &[0, 2, 3]);
	/// ```
	///
	/// [`BitPtr`]: ../pointer/struct.BitPtr.html
	#[inline]
	pub fn from_slice_mut(slice: &mut [T]) -> &mut Self {
		Self::from_slice(slice).bitptr().into_bitslice_mut()
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
	/// let bits = store.bits_mut::<Msb0>();
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
	///  let bits = &mut src.bits_mut::<Msb0>()[2 .. 4];
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
		(*data_ptr.offset(elt)).set::<O>(bit, value);
	}

	/// Produces a write reference to a region of the slice.
	///
	/// This method corresponds to [`Index::index`], except that it produces a
	/// writable reference rather than a read-only reference. See
	/// [`BitSliceIndex`] for the possible types of the produced reference.
	///
	/// Use of this method locks the `&mut BitSlice` for the duration of the
	/// produced reference’s lifetime. If you need multiple **non-overlapping**
	/// write references into a single source `&mut BitSlice`, see the
	/// [`::split_at_mut`] method.
	///
	/// # Lifetimes
	///
	/// - `'a`: Propagates the lifetime of the referent slice to the interior
	///   reference produced.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: Some value whose type can be used to index `BitSlice`s.
	///
	/// # Returns
	///
	/// A writable reference into `self`, whose exact type is determined by
	/// `index`’s implementation of [`BitSliceIndex`]. This may be either a
	/// smaller `&mut BitSlice` when `index` is a range, or a [`BitMut`] proxy
	/// type when `index` is a `usize`. See the [`BitMut`] documentation for
	/// information on how to use it.
	///
	/// # Panics
	///
	/// This panics if `index` is out of bounds of `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 0u8;
	/// let bits = src.bits_mut::<Msb0>();
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
	/// let bits = src.bits_mut::<Msb0>();
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
	/// [`BitSliceIndex`]: trait.BitSliceIndex.html
	/// [`::get`]: #method.get
	/// [`::split_at_mut`]: #method.split_at_mut
	#[deprecated(since = "0.18.0", note = "Use `.get_mut()` instead")]
	#[inline]
	pub fn at<'a, I>(&'a mut self, index: I) -> I::Mut
	where I: BitSliceIndex<'a, O, T> {
		index.index_mut(self)
	}

	/// Version of [`at`](#method.at) that does not perform boundary checking.
	///
	/// # Safety
	///
	/// If `index` is outside the boundaries of `self`, then this function will
	/// induce safety violations. The caller must ensure that `index` is within
	/// the boundaries of `self` before calling.
	#[deprecated(since = "0.18.0", note = "Use `.get_unchecked_mut()` instead")]
	#[inline]
	pub unsafe fn at_unchecked<'a, I>(&'a mut self, index: I) -> I::Mut
	where I: BitSliceIndex<'a, O, T> {
		index.get_unchecked_mut(self)
	}

	/// Version of [`split_at`](#method.split_at) that does not perform boundary
	/// checking.
	///
	/// # Safety
	///
	/// If `mid` is outside the boundaries of `self`, then this function will
	/// induce safety violations. The caller must ensure that `mid` is within
	/// the boundaries of `self` before calling.
	pub unsafe fn split_at_unchecked(&self, mid: usize) -> (&Self, &Self) {
		match mid {
			0 => (BitSlice::empty(), self),
			n if n == self.len() => (self, BitSlice::empty()),
			_ => (self.get_unchecked(.. mid), self.get_unchecked(mid ..)),
		}
	}

	/// Version of [`split_at_mut`](#method.split_at_mut) that does not perform
	/// boundary checking.
	///
	/// # Safety
	///
	/// If `mid` is outside the boundaries of `self`, then this function will
	/// induce safety violations. The caller must ensure that `mid` is within
	/// the boundaries of `self` before calling.
	#[inline]
	pub unsafe fn split_at_mut_unchecked(
		&mut self,
		mid: usize,
	) -> (&mut Self, &mut Self) {
		let (head, tail) = self.split_at_unchecked(mid);
		(head.bitptr().into_bitslice_mut(), tail.bitptr().into_bitslice_mut())
	}

	/// Version of [`swap`](#method.swap) that does not perform boundary checks.
	///
	/// # Safety
	///
	/// `a` and `b` must be within the bounds of `self`, otherwise, the memory
	/// access is unsound and may induce undefined behavior.
	#[inline]
	pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
		let bit_a = *self.get_unchecked(a);
		let bit_b = *self.get_unchecked(b);
		self.set_unchecked(a, bit_b);
		self.set_unchecked(b, bit_a);
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
	/// let bits = 0xFDu8.bits::<Msb0>();
	/// assert!(bits[.. 4].all());
	/// assert!(!bits[4 ..].all());
	/// ```
	pub fn all(&self) -> bool {
		match self.bitptr().domain().splat() {
			Either::Right((h, e, t)) => {
				let elt = e.load();
				(*h .. *t).all(|n| elt.get::<O>(n.idx()))
			},
			Either::Left((h, b, t)) => {
				if let Some((h, head)) = h {
					let elt = head.load();
					if !(*h .. T::BITS).all(|n| elt.get::<O>(n.idx())) {
						return false;
					}
				}
				if let Some(body) = b {
					if !body.iter().all(|e| e.load() == T::TRUE) {
						return false;
					}
				}
				if let Some((tail, t)) = t {
					let elt = tail.load();
					if !(0 .. *t).all(|n| elt.get::<O>(n.idx())) {
						return false;
					}
				}
				true
			},
		}
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
	/// let bits = 0x40u8.bits::<Msb0>();
	/// assert!(bits[.. 4].any());
	/// assert!(!bits[4 ..].any());
	/// ```
	pub fn any(&self) -> bool {
		match self.bitptr().domain().splat() {
			Either::Right((h, e, t)) => {
				let elt = e.load();
				(*h .. *t).any(|n| elt.get::<O>(n.idx()))
			},
			Either::Left((h, b, t)) => {
				if let Some((h, head)) = h {
					let elt = head.load();
					if (*h .. T::BITS).any(|n| elt.get::<O>(n.idx())) {
						return true;
					}
				}
				if let Some(body) = b {
					if body.iter().any(|elt| elt.load() != T::FALSE) {
						return true;
					}
				}
				if let Some((tail, t)) = t {
					let elt = tail.load();
					if (0 .. *t).any(|n| elt.get::<O>(n.idx())) {
						return true;
					}
				}
				false
			},
		}
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
	/// let bits = 0xFDu8.bits::<Msb0>();
	/// assert!(!bits[.. 4].not_all());
	/// assert!(bits[4 ..].not_all());
	/// ```
	#[inline]
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
	/// let bits = 0x40u8.bits::<Msb0>();
	/// assert!(!bits[.. 4].not_any());
	/// assert!(bits[4 ..].not_any());
	/// ```
	#[inline]
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
	/// let bits = 0b111_000_10u8.bits::<Msb0>();
	/// assert!(!bits[0 .. 3].some());
	/// assert!(!bits[3 .. 6].some());
	/// assert!(bits[6 ..].some());
	/// ```
	#[inline]
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
	/// let bits = [0xFDu8, 0x25].bits::<Msb0>();
	/// assert_eq!(bits.count_ones(), 10);
	/// ```
	pub fn count_ones(&self) -> usize {
		match self.bitptr().domain().splat() {
			Either::Right((h, e, t)) => {
				let elt = e.load();
				(*h .. *t).filter(|n| elt.get::<O>(n.idx())).count()
			},
			Either::Left((h, b, t)) => {
				let mut out = 0usize;
				if let Some((h, head)) = h {
					let elt = head.load();
					out += (*h .. T::BITS)
						.filter(|n| elt.get::<O>(n.idx()))
						.count();
				}
				if let Some(body) = b {
					out += body.iter()
						.map(BitAccess::load)
						.map(T::count_ones)
						.sum::<usize>();
				}
				if let Some((tail, t)) = t {
					let elt = tail.load();
					out += (0 .. *t)
						.filter(|n| elt.get::<O>(n.idx()))
						.count();
				}
				out
			},
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
	/// let bits = [0xFDu8, 0x25].bits::<Msb0>();
	/// assert_eq!(bits.count_zeros(), 6);
	/// ```
	pub fn count_zeros(&self) -> usize {
		self.len() - self.count_ones()
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
	/// let bits = src.bits_mut::<Msb0>();
	/// bits[2 .. 6].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b0011_1100]);
	/// bits[3 .. 5].set_all(false);
	/// assert_eq!(bits.as_ref(), &[0b0010_0100]);
	/// bits[.. 1].set_all(true);
	/// assert_eq!(bits.as_ref(), &[0b1010_0100]);
	/// ```
	pub fn set_all(&mut self, value: bool) {
		match self.bitptr().domain().splat() {
			Either::Right((h, e, t)) => {
				for n in *h .. *t {
					e.set::<O>(n.idx(), value);
				}
			},
			Either::Left((h, b, t)) => {
				if let Some((h, head)) = h {
					for n in *h .. T::BITS {
						head.set::<O>(n.idx(), value);
					}
				}
				if let Some(body) = b {
					for elt in body {
						elt.store(if value { T::TRUE } else { T::FALSE });
					}
				}
				if let Some((tail, t)) = t {
					for n in 0 .. *t {
						tail.set::<O>(n.idx(), value);
					}
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
	///  let bits = src.bits_mut::<Msb0>();
	///  bits.for_each(|idx, _bit| idx % 3 == 0);
	/// }
	/// assert_eq!(src, 0b1001_0010);
	/// ```
	pub fn for_each<F>(&mut self, func: F)
	where F: Fn(usize, bool) -> bool {
		for idx in 0 .. self.len() {
			unsafe {
				let tmp = *self.get_unchecked(idx);
				let new = func(idx, tmp);
				self.set_unchecked(idx, new);
			}
		}
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This addition interprets the slice, and the other addend, as having its
	/// least significant bits first in the order and its most significant bits
	/// last. This is most likely to be numerically useful under a
	/// `Lsb0` `BitOrder` type.
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
	/// let ab = &mut a.bits_mut::<Lsb0>()[.. 4];
	/// let bb = &    b.bits::<Lsb0>()[.. 4];
	/// let c = ab.add_assign_reverse(bb.iter().copied());
	/// assert!(c);
	/// assert_eq!(a, 0b0000_0110u8);
	/// ```
	///
	/// # Performance Notes
	///
	/// When using `Lsb0` `BitOrder` types, this can be accelerated by
	/// delegating the addition to the underlying types. This is a software
	/// implementation of the [ripple-carry adder], which has `O(n)` runtime in
	/// the number of bits. The CPU is much faster, as it has access to
	/// element-wise or vectorized addition operations.
	///
	/// If your use case sincerely needs binary-integer arithmetic operations on
	/// bit sets, please file an issue.
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
			c = unsafe {
				let a = *self.get_unchecked(i);
				let (y, z) = crate::rca1(a, b, c);
				//  Write the sum into `self`
				self.set_unchecked(i, y);
				//  Propagate the carry
				z
			};
		}
		c
	}

	/// Accesses the backing storage of the `BitSlice` as a slice of its
	/// elements.
	///
	/// This will not include partially-owned edge elements, as they may be
	/// contended by other slice handles.
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
	/// let bits = src.bits::<Msb0>();
	///
	/// let accum = bits.as_slice()
	///   .iter()
	///   .map(|elt| elt.count_ones())
	///   .sum::<u32>();
	/// assert_eq!(accum, 3);
	/// ```
	pub fn as_slice(&self) -> &[T] {
		&* unsafe { BitAccess::as_slice_mut(match self.bitptr().domain() {
			| BitDomain::Empty
			| BitDomain::Minor(_, _, _) => &[],
			| BitDomain::PartialHead(_, _, body)
			| BitDomain::PartialTail(body, _, _)
			| BitDomain::Major(_, _, body, _, _)
			| BitDomain::Spanning(body) => body,
		}) }
	}

	/// Accesses the underlying store.
	///
	/// This will not include partially-owned edge elements, as they may be
	/// contended by other slice handles.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [1u8, 64];
	/// let bits = src.bits_mut::<Msb0>();
	/// for elt in bits.as_mut_slice() {
	///   *elt |= 2;
	/// }
	/// assert_eq!(&[3, 66], bits.as_slice());
	/// ```
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		unsafe { BitAccess::as_slice_mut(match self.bitptr().domain() {
			| BitDomain::Empty
			| BitDomain::Minor(_, _, _) => &[],
			| BitDomain::PartialHead(_, _, body)
			| BitDomain::PartialTail(body, _, _)
			| BitDomain::Major(_, _, body, _, _)
			| BitDomain::Spanning(body) => body,
		}) }
	}

	/// Accesses the underlying store, including contended partial elements.
	///
	/// This produces a slice of element wrappers that permit shared mutation,
	/// rather than a slice of the bare `T` fundamentals.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice of all elements under the bit span, including any
	/// partially-owned edge elements, wrapped in safe shared-mutation types.
	#[inline]
	pub fn as_total_slice(&self) -> &[T::Access] {
		self.bitptr().as_access_slice()
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
	#[inline]
	pub(crate) fn bitptr(&self) -> BitPtr<T> {
		BitPtr::from_bitslice(self)
	}

	/// Copy a bit from one location in a slice to another.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `from`: The index of the bit to be copied.
	/// - `to`: The index at which the copied bit will be written.
	///
	/// # Safety
	///
	/// `from` and `to` must be within the bounds of `self`. This is not
	/// checked.
	#[inline]
	pub(crate) unsafe fn copy_unchecked(&mut self, from: usize, to: usize) {
		self.set_unchecked(to, *self.get_unchecked(from));
	}
}

/** Allows a type to be used as a sequence of immutable bits.

# Requirements

This trait can only be implemented by contiguous structures: individual
fundamentals, and sequences (arrays or slices) of them.
**/
pub trait AsBits {
	/// The underlying fundamental type of the implementor.
	type Store: BitStore;

	/// Constructs a `BitSlice` reference over data.
	///
	/// # Type Parameters
	///
	/// - `O: BitOrder`: The `BitOrder` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `BitOrder`
	/// type and using `Self::Store` as the data type.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 8u8;
	/// let bits = src.bits::<Msb0>();
	/// assert!(bits[4]);
	/// ```
	fn bits<O>(&self) -> &BitSlice<O, Self::Store>
	where O: BitOrder;

	/// Constructs a mutable `BitSlice` reference over data.
	///
	/// # Type Parameters
	///
	/// - `O: BitOrder`: The `BitOrder` type used to index within the slice.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A `BitSlice` handle over `self`’s data, using the provided `BitOrder`
	/// type and using `Self::Store` as the data type.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = 8u8;
	/// let bits = src.bits_mut::<Lsb0>();
	/// assert!(bits[3]);
	/// *bits.at(3) = false;
	/// assert!(!bits[3]);
	/// ```
	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, Self::Store>
	where O: BitOrder;
}

impl<T> AsBits for T
where T: BitStore {
	type Store = T;
	fn bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element(self)
	}

	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_element_mut(self)
	}
}

impl<T> AsBits for [T]
where T: BitStore {
	type Store = T;
	fn bits<O>(&self) -> &BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice(self)
	}

	fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
	where O: BitOrder {
		BitSlice::from_slice_mut(self)
	}
}

macro_rules! impl_bits_for {
	($( $n:expr ),* ) => { $(
		impl<T> AsBits for [T; $n]
		where T: BitStore {
			type Store = T;
			fn bits<O>(&self) -> &BitSlice<O, T>
			where O: BitOrder {
				BitSlice::from_slice(self)
			}
			fn bits_mut<O>(&mut self) -> &mut BitSlice<O, T>
			where O: BitOrder {
				BitSlice::from_slice_mut(self)
			}
		}
	)* };
}

impl_bits_for![
	0, 1, 2, 3, 4, 5, 6, 7,
	8, 9, 10, 11, 12, 13, 14, 15,
	16, 17, 18, 19, 20, 21, 22, 23,
	24, 25, 26, 27, 28, 29, 30, 31,
	32
];

mod api;
pub(crate) mod iter;
mod ops;
mod proxy;
mod traits;

//  Match the `core::slice` API module topology.

pub use self::api::*;
pub use self::iter::*;
pub use self::proxy::*;

#[cfg(test)]
mod tests;
