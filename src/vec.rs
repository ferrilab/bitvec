/*! `BitVec` structure

This module holds the main working type of the library. Clients can use
`BitSlice` directly, but `BitVec` is much more useful for most work.

The `BitSlice` module discusses the design decisions for the separation between
slice and vector types.
!*/

#![cfg(feature = "alloc")]

use crate::{
	boxed::BitBox,
	cursor::{
		Cursor,
		Local,
	},
	indices::IntoBitIdx,
	pointer::BitPtr,
	slice::BitSlice,
	store::{
		BitStore,
		Word,
	},
};

use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
	},
};

use core::{
	cmp,
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
	marker::{
		PhantomData,
	},
	mem,
	ops::RangeBounds,
	ptr::NonNull,
	slice,
};

#[cfg(not(feature = "std"))]
use alloc::{
	borrow::ToOwned,
	boxed::Box,
	vec::Vec,
};

#[cfg(feature = "std")]
use std::{
	io::{
		self,
		Write,
	},
};

/** A compact [`Vec`] of bits, whose cursor and storage type can be customized.

`BitVec` is a newtype wrapper over `Vec`, and as such is exactly three words in
size on the stack.

# Examples

```rust
use bitvec::prelude::*;

let mut bv: BitVec = BitVec::new();
bv.push(false);
bv.push(true);

assert_eq!(bv.len(), 2);
assert_eq!(bv[0], false);

assert_eq!(bv.pop(), Some(true));
assert_eq!(bv.len(), 1);

bv.set(0, true);
assert_eq!(bv[0], true);

bv.extend([0u8, 1, 0].iter().map(|n| *n != 0u8));
for bit in &*bv {
  println!("{}", bit);
}
assert_eq!(bv, bitvec![1, 0, 1, 0]);
```

The [`bitvec!`] macro is provided to make initialization more convenient.

```rust
use bitvec::prelude::*;

let mut bv = bitvec![0, 1, 2, 3];
bv.push(false);
assert_eq!(bv, bitvec![0, 1, 1, 1, 0]);
```

It can also initialize each element of a `BitVec<_, T>` with a given value. This
may be more efficient than performing allocation and initialization in separate
steps, especially when initializing a vector of zeros:

```rust
use bitvec::prelude::*;

let bv = bitvec![0; 15];
assert_eq!(bv, bitvec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

// The following is equivalent, but potentially slower:
let mut bv1: BitVec = BitVec::with_capacity(15);
bv1.resize(15, false);
```

Use a `BitVec<T>` as an efficient stack:

```rust
use bitvec::prelude::*;
let mut stack: BitVec = BitVec::new();

stack.push(false);
stack.push(true);
stack.push(true);

while let Some(top) = stack.pop() {
  //  Prints true, true, false
  println!("{}", top);
}
```

# Indexing

The `BitVec` type allows you to access values by index, because it implements
the [`Index`] trait. An example will be more explicit:

```rust
use bitvec::prelude::*;

let bv = bitvec![0, 0, 1, 1];
println!("{}", bv[1]); // it will display 'false'
```

However, be careful: if you try to access an index which isn’t in the `BitVec`,
your software will panic! You cannot do this:

```rust,should_panic
use bitvec::prelude::*;

let bv = bitvec![0, 1, 0, 1];
println!("{}", bv[6]); // it will panic!
```

In conclusion: always check if the index you want to get really exists before
doing it.

# Slicing

A `BitVec` is growable. A [`BitSlice`], on the other hand, is fixed size. To get
a bit slice, use `&`. Example:

```rust
use bitvec::prelude::*;
fn read_bitslice(slice: &BitSlice) {
	// use slice
}

let bv = bitvec![0, 1];
read_bitslice(&bv);

// … and that’s all!
// you can also do it like this:
let bs : &BitSlice = &bv;
```

In Rust, it’s more common to pass slices as arguments rather than vectors when
you do not want to grow or shrink it. The same goes for [`Vec`] and [`&[]`], and
[`String`] and [`&str`].

# Capacity and Reallocation

The capacity of a bit vector is the amount of space allocated for any future
bits that will be added onto the vector. This is not to be confused with the
*length* of a vector, which specifies the number of live, useful bits within the
vector. If a vector’s length exceeds its capacity, its capacity will
automatically be increased, but its storage elements will have to be
reallocated.

For example, a bit vector with capacity 10 and length 0 would be an allocated,
but uninhabited, vector, with space for ten more bits. Pushing ten or fewer bits
onto the vector will not change its capacity or cause reallocation to occur.
However, if the vector’s length is increased to eleven, it will have to
reallocate, which can be slow. For this reason, it is recommended to use
[`with_capacity`] whenever possible to specify how big the bit vector is
expected to get.

# Guarantees

Due to its incredibly fundamental nature, `BitVec` makes a lot of guarantees
about its design. This ensures that it is as low-overhead as possible in the
general case, and can be correctly manipulated in fundamental ways by `unsafe`
code.

Most fundamentally, `BitVec` is and always will be a `(`BitPtr`, capacity)`
doublet. No more, no less. The order of these fields is unspecified, and you
should **only** interact with the members through the provided APIs. Note that
`BitPtr` is ***not directly manipulable***, and must ***never*** be written or
interpreted as anything but opaque binary data by user code.

When a `BitVec` has allocated memory, then the memory to which it points is on
the heap (as defined by the allocator Rust is configured to use by default), and
its pointer points to [`len`] initialized bits in order of the `Cursor` type
parameter, followed by `capacity - len` logically uninitialized bits.

`BitVec` will never perform a “small optimization” where elements are stored in
its handle representation, for two reasons:

- It would make it more difficult for user code to correctly manipulate a
  `BitVec`. The contents of the `BitVec` would not have a stable address if the
  handle were moved, and it would be more difficult to determine if a `BitVec`
  had allocated memory.

- It would penalize the general, heap-allocated, case by incurring a branch on
  every access.

`BitVec` will never automatically shrink itself, even if it is emptied. This
ensures that no unnecessary allocations or deallocations occur. Emptying a
`BitVec` and then refilling it to the same length will incur no calls to the
allocator. If you wish to free up unused memory, use [`shrink_to_fit`].

## Erasure

`BitVec` will not specifically overwrite any data that is removed from it, nor
will it specifically preserve it. Its uninitialized memory is scratch space that
may be used however the implementation desires, and must not be relied upon as
stable. Do not rely on removed data to be erased for security purposes. Even if
you drop a `BitVec`, its buffer may simply be reused for other data structures
in your program. Even if you zero a `BitVec`’s memory first, that may not
actually occur if the optimizer does not consider this an observable side
effect. There is one case that will never break, however: using `unsafe` to
construct a `[T]` slice over the `BitVec`’s capacity, and writing to the excess
space, then increasing the length to match, is always valid.

# Type Parameters

- `C`: An implementor of the `Cursor` trait. This type is used to convert
  semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T`: An implementor of the `BitStore` trait: `u8`, `u16`, `u32`, or `u64`
  (64-bit systems only). This is the actual type in memory that the vector will
  use to store data.

# Safety

The `BitVec` handle has the same *size* as standard Rust `Vec` handles, but it
is ***extremely binary incompatible*** with them. Attempting to treat
`BitVec<_, T>` as `Vec<T>` in any manner except through the provided APIs is
***catastrophically*** unsafe and unsound.

[`BitSlice`]: ../slice/struct.BitSlice.html
[`BitVec::with_capacity`]: #method.with_capacity
[`Index`]: https://doc.rust-lang.org/stable/std/ops/trait.Index.html
[`String`]: https://doc.rust-lang.org/stable/std/string/struct.String.html
[`Vec`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html
[`bitvec!`]: ../macro.bitvec.html
[`clear_on_drop`]: https://docs.rs/clear_on_drop
[`len`]: #method.len
[`shrink_to_fit`]: #method.shrink_to_fit
[`with_capacity`]: #method.with_capacity
[`&str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
[`&[]`]: https://doc.rust-lang.org/stable/std/primitive.slice.html
**/
#[repr(C)]
pub struct BitVec<C = Local, T = Word>
where C: Cursor, T: BitStore {
	/// Phantom `Cursor` member to satisfy the constraint checker.
	_cursor: PhantomData<C>,
	/// Slice pointer over the owned memory.
	pointer: BitPtr<T>,
	/// The number of *elements* this vector has allocated.
	capacity: usize,
}

impl<C, T> BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Constructs a new, empty, `BitVec<C, T>`.
	///
	/// The vector does not allocate until bits are written into it.
	///
	/// # Returns
	///
	/// An empty, unallocated, `BitVec` handle.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// assert_eq!(bv.capacity(), 0);
	/// ```
	pub fn new() -> Self {
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::empty(),
			capacity: 0,
		}
	}

	/// Constructs a new, empty, `BitVec<T>` with the specified capacity.
	///
	/// The new vector will be able to hold at least `capacity` elements before
	/// it reallocates. If `capacity` is `0`, it will not allocate.
	///
	/// # Parameters
	///
	/// - `capacity`: The minimum number of bits that the new vector will need
	///   to be able to hold.
	///
	/// # Returns
	///
	/// An empty vector with at least the given capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec = BitVec::with_capacity(10);
	/// assert!(bv.is_empty());
	/// assert!(bv.capacity() >= 10);
	/// ```
	pub fn with_capacity(capacity: usize) -> Self {
		//  Find the number of elements needed to store the requested capacity
		//  of bits.
		let (cap, _) = 0.idx::<T>().span(capacity);
		//  Acquire a region of memory large enough for that element number.
		let (ptr, cap) = {
			let v = Vec::with_capacity(cap);
			let (ptr, cap) = (v.as_ptr(), v.capacity());
			mem::forget(v);
			(ptr, cap)
		};
		//  Take ownership of that region as an owned BitPtr
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::uninhabited(ptr),
			capacity: cap,
		}
	}

	/// Constructs a `BitVec` from a single element.
	///
	/// The produced `BitVec` will span the element, and include all bits in it.
	///
	/// # Parameters
	///
	/// - `elt`: The source element.
	///
	/// # Returns
	///
	/// A `BitVec` over the provided element.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = BitVec::<BigEndian, u8>::from_element(5);
	/// assert_eq!(bv.count_ones(), 2);
	/// ```
	pub fn from_element(elt: T) -> Self {
		Self::from_vec({
			let mut v = Vec::with_capacity(1);
			v.push(elt);
			v
		})
	}

	/// Constructs a `BitVec` from a slice of elements.
	///
	/// The produced `BitVec` will span the provided slice.
	///
	/// # Parameters
	///
	/// - `slice`: The source elements to copy into the new `BitVec`.
	///
	/// # Returns
	///
	/// A `BitVec` set to the provided slice values.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [5, 10];
	/// let bv = BitVec::<BigEndian, u8>::from_slice(&src[..]);
	/// assert!(bv[5]);
	/// assert!(bv[7]);
	/// assert!(bv[12]);
	/// assert!(bv[14]);
	/// ```
	pub fn from_slice(slice: &[T]) -> Self {
		BitSlice::<C, T>::from_slice(slice).to_owned()
	}

	/// Consumes a `Vec<T>` and creates a `BitVec<C, T>` from it.
	///
	/// # Parameters
	///
	/// - `vec`: The source vector whose memory will be used.
	///
	/// # Returns
	///
	/// A new `BitVec` using the `vec` `Vec`’s memory.
	///
	/// # Panics
	///
	/// Panics if the source vector would cause the `BitVec` to overflow
	/// capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = BitVec::<BigEndian, u8>::from_vec(vec![1, 2, 4, 8]);
	/// assert_eq!(
	///   "[00000001, 00000010, 00000100, 00001000]",
	///   &format!("{}", bv),
	/// );
	/// ```
	pub fn from_vec(vec: Vec<T>) -> Self {
		let len = vec.len();
		assert!(
			len <= BitPtr::<T>::MAX_ELTS,
			"Vector length {} overflows {}",
			len,
			BitPtr::<T>::MAX_ELTS,
		);
		let bs = BitSlice::<C, T>::from_slice(&vec[..]);
		let pointer = bs.bitptr();
		let capacity = vec.capacity();
		mem::forget(vec);
		Self {
			_cursor: PhantomData,
			pointer,
			capacity,
		}
	}

	/// Clones a `&BitSlice` into a `BitVec`.
	///
	/// This method is the only mechanism by which a `BitVec` can be created
	/// whose first live bit is not at the `0` index. This behavior, though
	/// unconventional in common uses of `BitVec`, allows for a convenient clone
	/// of any `BitSlice` reference without having to shift every bit down.
	///
	/// When a `BitVec` created with a non-zero head bit is emptied, its head
	/// reverts to `0` and will begin there at future fills.
	///
	/// The [`::force_align`] method will shift the `BitVec`’s contents to begin
	/// at the zero index if you need to ensure this property.
	///
	/// # Parameters
	///
	/// - `slice`: The source bit-slice. This may have any head index, and its
	///   memory will be directly `memcpy`ed into the allocation.
	///
	/// # Returns
	///
	/// A `BitVec` containing the same bits as the source slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bs = [0u8, !0].bits::<BigEndian>();
	/// let bv = BitVec::from_bitslice(bs);
	/// assert_eq!(bv.len(), 16);
	/// assert!(bv.some());
	/// ```
	///
	/// [`::force_align`]: #method.force_align
	pub fn from_bitslice(slice: &BitSlice<C, T>) -> Self {
		//  Clone the slice’s underlying storage into a `Vec`.
		let v = unsafe { slice.as_total_slice() }.to_owned();
		//  Get a copy of the slice’s `BitPtr`.
		let mut pointer = slice.bitptr();
		//  Retarget the `BitPtr` at the allocation block. The `head` and `bits`
		//  counters are unaffected.
		unsafe { pointer.set_pointer(v.as_ptr()); }
		let capacity = v.capacity();
		mem::forget(v);
		Self {
			_cursor: PhantomData,
			pointer,
			capacity,
		}
	}

	/// Converts a frozen `BitBox` allocation into a growable `BitVec`.
	///
	/// This does not copy or reallocate.
	///
	/// # Parameters
	///
	/// - `slice`: A `BitBox` to be thawed.
	///
	/// # Returns
	///
	/// A growable collection over the original memory of the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = BitVec::from_boxed_bitslice(bitbox![0, 1]);
	/// assert_eq!(bv.len(), 2);
	/// assert!(bv.some());
	/// ```
	pub fn from_boxed_bitslice(slice: BitBox<C, T>) -> Self {
		let bitptr = slice.bitptr();
		mem::forget(slice);
		unsafe { Self::from_raw_parts(bitptr, bitptr.elements()) }
	}

	/// Creates a new `BitVec<C, T>` directly from the raw parts of another.
	///
	/// # Parameters
	///
	/// - `pointer`: The `BitPtr<T>` to use.
	/// - `capacity`: The number of `T` elements *allocated* in that slab.
	///
	/// # Returns
	///
	/// A `BitVec` over the given slab of memory.
	///
	/// # Safety
	///
	/// This is ***highly*** unsafe, due to the number of invariants that aren’t
	/// checked:
	///
	/// - `pointer` needs to have been previously allocated by some allocating
	///   type.
	/// - `pointer`’s `T` needs to have the same size ***and alignment*** as it
	///   was initially allocated.
	/// - `pointer`’s element count needs to be less than or equal to the
	///   original allocation capacity.
	/// - `capacity` needs to be the original allocation capacity for the
	///   vector. This is *not* the value produced by `.capacity()`.
	///
	/// Violating these ***will*** cause problems, like corrupting the handle’s
	/// concept of memory, the allocator’s internal data structures, and the
	/// sanity of your program. It is ***absolutely*** not safe to construct a
	/// `BitVec` whose `T` differs from the type used for the initial
	/// allocation.
	///
	/// The ownership of `pointer` is effectively transferred to the
	/// `BitVec<C, T>` which may then deallocate, reallocate, or modify the
	/// contents of the referent slice at will. Ensure that nothing else uses
	/// the pointer after calling this function.
	pub unsafe fn from_raw_parts(pointer: BitPtr<T>, capacity: usize) -> Self {
		Self {
			_cursor: PhantomData,
			pointer,
			capacity,
		}
	}

	/// Returns the number of bits the vector can hold without reallocating.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The number of bits that the vector can hold before reallocating.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec = BitVec::with_capacity(10);
	/// assert!(bv.is_empty());
	/// assert!(bv.capacity() >= 10);
	/// ```
	pub fn capacity(&self) -> usize {
		self.capacity
			.checked_mul(T::BITS as usize)
			.expect("Vector capacity overflow")
	}

	/// Returns the number of elements the vector can hold without reallocating.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec<BigEndian, u16> = BitVec::with_capacity(40);
	/// assert!(bv.is_empty());
	/// assert!(bv.element_capacity() >= 3);
	/// ```
	pub fn element_capacity(&self) -> usize {
		self.capacity
	}

	/// Reserves capacity for at least `additional` more bits to be inserted.
	///
	/// The collection may reserve more space to avoid frequent reallocations.
	/// After calling `reserve`, capacity will be greater than or equal to
	/// `self.len() + additional`. Does nothing if the capacity is already
	/// sufficient.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `additional`: The number of extra bits to be granted space.
	///
	/// # Panics
	///
	/// Panics if the new capacity would overflow the vector’s limits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 5];
	/// assert!(bv.capacity() >= 5);
	/// bv.reserve(10);
	/// assert!(bv.capacity() >= 15);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		let newlen = self.len().saturating_add(additional);
		assert!(
			newlen <= BitPtr::<T>::MAX_INDX,
			"Capacity overflow: {} exceeds {}",
			newlen,
			BitPtr::<T>::MAX_INDX,
		);
		let tail = self.pointer.tail();
		//  If the additional bits would not depart the last element, do nothing
		if *tail as usize + additional <= T::BITS as usize {
			return;
		}
		//  Compute the number of additional elements needed to store the
		//  requested number of additional bits.
		let (e, _) = tail.span(additional);
		self.do_unto_vec(|v| v.reserve(e));
	}

	/// Reserves the minimum capacity for at least `additional` more bits.
	///
	/// After calling `reserve_exact`, the capacity will be greater than or
	/// equal to `self.len() + additional`. Does nothing if the capacity is
	/// already sufficient.
	///
	/// Note that the allocator may give the collection more space than it
	/// requests. Therefore, the capacity cannot be relied upon to be precisely
	/// minimal. Prefer `reserve` if future insertions are expected.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `additional`: The number of extra bits to be granted space.
	///
	/// # Panics
	///
	/// Panics if the new capacity would overflow the vector’s limits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 5];
	/// assert!(bv.capacity() >= 5);
	/// bv.reserve_exact(10);
	/// assert!(bv.capacity() >= 15);
	/// ```
	pub fn reserve_exact(&mut self, additional: usize) {
		let newlen = self.len() + additional;
		assert!(
			newlen <= BitPtr::<T>::MAX_INDX,
			"Capacity overflow: {} exceeds {}",
			newlen,
			BitPtr::<T>::MAX_INDX,
		);
		let tail = self.pointer.tail();
		if *tail as usize + additional <= T::BITS as usize {
			return;
		}
		let (e, _) = tail.span(additional);
		self.do_unto_vec(|v| v.reserve_exact(e));
	}

	/// Shrinks the capacity of the vector as much as possible.
	///
	/// It will drop down as close as possible to the length, but the allocator
	/// may still inform the vector that there is space for bits.
	///
	/// This does not modify the contents of the memory store! It will not zero
	/// any memory that had been used and then removed from the vector’s live
	/// count.
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
	/// let mut bv = bitvec![1; 100];
	/// let cap = bv.capacity();
	/// bv.truncate(10);
	/// bv.shrink_to_fit();
	/// assert!(bv.capacity() <= cap);
	/// ```
	pub fn shrink_to_fit(&mut self) {
		self.do_unto_vec(Vec::shrink_to_fit);
	}

	/// Shortens the vector, keeping the first `len` bits and dropping the rest.
	///
	/// If `len` is greater than the vector’s current length, this has no
	/// effect.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `len`: The new length of the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 15];
	/// bv.truncate(10);
	/// assert_eq!(bv.len(), 10);
	///
	/// bv.truncate(15);
	/// assert_eq!(bv.len(), 10);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		if len < self.len() {
			unsafe { self.pointer.set_len(len); }
		}
	}

	/// Produces a `BitSlice` containing the entire vector.
	///
	/// Equivalent to `&s[..]`.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A `BitSlice` over the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 1, 0];
	/// let bs = bv.as_bits();
	/// ```
	pub fn as_bits(&self) -> &BitSlice<C, T> {
		self.pointer.into_bitslice()
	}

	/// Produces a mutable `BitSlice` containing the entire vector.
	///
	/// Equivalent to `&mut s[..]`.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutable `BitSlice` over the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 1, 0];
	/// let bs = bv.as_bits_mut();
	/// ```
	pub fn as_bits_mut(&mut self) -> &mut BitSlice<C, T> {
		self.pointer.into_bitslice_mut()
	}

	/// Sets the length of the vector.
	///
	/// This unconditionally sets the size of the vector, without modifying its
	/// contents. It is up to the caller to ensure that the vector’s buffer can
	/// hold the new size.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `len`: The new length of the vector. This must be less than the
	///   maximum number of bits that the vector can hold.
	///
	/// # Panics
	///
	/// This panics if `len` overflows the vector's intrinsic *or allocated*
	/// capacities.
	///
	/// # Safety
	///
	/// The caller must ensure that the new length is sound for the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::with_capacity(15);
	/// assert!(bv.is_empty());
	/// unsafe { bv.set_len(10) };
	/// assert_eq!(bv.len(), 10);
	/// ```
	pub unsafe fn set_len(&mut self, len: usize) {
		assert!(
			len <= BitPtr::<T>::MAX_INDX,
			"Capacity overflow: {} overflows maximum length {}",
			len,
			BitPtr::<T>::MAX_INDX,
		);
		assert!(
			len <= self.capacity(),
			"Capacity overflow: {} overflows allocation size {}",
			len,
			self.capacity(),
		);
		self.pointer.set_len(len);
	}

	/// Removes a bit from the vector and returns it.
	///
	/// The removed bit is replaced by the last bit in the vector.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The index whose bit is to be returned, and replaced by the
	///   tail.
	///
	/// # Returns
	///
	/// The bit at the requested index.
	///
	/// # Panics
	///
	/// Panics if the index is out of bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 0, 0, 1];
	/// assert!(!bv[2]);
	/// assert_eq!(bv.len(), 5);
	/// assert!(!bv.swap_remove(2));
	/// assert!(bv[2]);
	/// assert_eq!(bv.len(), 4);
	/// ```
	pub fn swap_remove(&mut self, index: usize) -> bool {
		let len = self.len();
		assert!(index < len, "Index {} out of bounds: {}", index, len);
		if index < len - 1 {
			self.swap(index, len - 1);
		}
		self.pop()
			.expect("BitVec::swap_remove cannot fail after index validation")
	}

	/// Inserts a bit at a position, shifting all bits after it to the right.
	///
	/// Note that this is `O(n)` runtime.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The position at which to insert. This may be any value from
	///   `0` up to *and including* `self.len()`. At `self.len()`, it is
	///   equivalent to calling `self.push(value)`.
	/// - `value`: The bit to be inserted.
	///
	/// # Panics
	///
	/// Panics if `index` is greater than the length.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 0, 0];
	/// bv.insert(2, true);
	/// assert_eq!(bv, bitvec![0, 0, 1, 0, 0]);
	/// bv.insert(5, true);
	/// assert_eq!(bv, bitvec![0, 0, 1, 0, 0, 1]);
	/// ```
	pub fn insert(&mut self, index: usize, value: bool) {
		let len = self.len();
		assert!(index <= len, "Index {} is out of bounds: {}", index, len);
		self.push(value);
		self[index ..].rotate_right(1);
	}

	/// Removes and returns the bit at position `index`, shifting all bits after
	/// it to the left.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `index`: The position whose bit is to be removed. This must be in the
	///   domain `0 .. self.len()`.
	///
	/// # Returns
	///
	/// The bit at the requested index.
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds for the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 1, 0, 0];
	/// assert!(bv.remove(2));
	/// assert_eq!(bv, bitvec![0, 0, 0, 0]);
	/// ```
	pub fn remove(&mut self, index: usize) -> bool {
		let len = self.len();
		assert!(index < len, "Index {} is out of bounds: {}", index, len);
		self[index ..].rotate_left(1);
		self.pop()
			.expect("BitVec::remove cannot fail after index validation")
	}

	/// Retains only the bits that pass the predicate.
	///
	/// This removes all bits `b` where `f(e)` returns `false`. This method
	/// operates in place and preserves the order of the retained bits. Because
	/// it is in-place, it operates in `O(n²)` time.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `pred`: The testing predicate for each bit.
	///
	/// # Type Parameters
	///
	/// - `F`: A function that can be invoked on each bit, returning whether the
	///   bit should be kept or not. Receives the index (following
	///   [`BitSlice::for_each`]) to provide additional context to determine
	///   whether the entry satisfies the condition.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 1, 0, 1, 0, 1];
	/// bv.retain(|_, b| b);
	/// assert_eq!(bv, bitvec![1, 1, 1]);
	/// ```
	///
	/// [`BitSlice::for_each`]: ../slice/struct.BitSlice.html#method.for_each
	pub fn retain<F>(&mut self, mut pred: F)
	where F: FnMut(usize, bool) -> bool {
		for n in (0 .. self.len()).rev() {
			if !pred(n, unsafe { self.get_unchecked(n) }) {
				self.remove(n);
			}
		}
	}

	/// Appends a bit to the back of the vector.
	///
	/// If the vector is at capacity, this may cause a reallocation.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `value`: The bit value to append.
	///
	/// # Panics
	///
	/// This will panic if the push will cause the vector to allocate above
	/// `BitPtr<T>` or machine capacity.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	/// ```
	pub fn push(&mut self, value: bool) {
		let len = self.len();
		assert!(
			len <= BitPtr::<T>::MAX_INDX,
			"Capacity overflow: {} >= {}",
			len,
			BitPtr::<T>::MAX_INDX,
		);
		//  If self is empty *or* tail is at the back edge of an element, push
		//  an element onto the vector.
		if self.is_empty() || *self.pointer.tail() == T::BITS {
			self.do_unto_vec(|v| v.push(0.into()));
		}
		//  At this point, it is always safe to increment the tail, and then
		//  write to the newly live bit.
		unsafe {
			self.pointer = self.pointer.incr_tail();
			self.set_unchecked(len, value);
		}
	}

	/// Removes the last bit from the collection, if present.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// If the vector is not empty, this returns the last bit; if it is empty,
	/// this returns `None`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	///
	/// assert!(bv.pop().unwrap());
	/// assert!(bv.is_empty());
	/// assert!(bv.pop().is_none());
	/// ```
	pub fn pop(&mut self) -> Option<bool> {
		match self.len() {
			0 => None,
			len => unsafe {
				let new_len = len - 1;
				let out = self.get_unchecked(new_len);
				self.pointer.set_len(new_len);
				Some(out)
			},
		}
	}

	/// Moves all the elements of `other` into `self`, leaving `other` empty.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `other`: A `BitVec` of any order and storage type. Its bits are
	///   appended to `self`.
	///
	/// # Panics
	///
	/// Panics if the joined vector is too large.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv1 = bitvec![0; 10];
	/// let mut bv2 = bitvec![1; 10];
	/// bv1.append(&mut bv2);
	/// assert_eq!(bv1.len(), 20);
	/// assert!(bv1[10]);
	/// assert!(bv2.is_empty());
	/// ```
	pub fn append<D, U>(&mut self, other: &mut BitVec<D, U>)
	where D: Cursor, U: BitStore {
		self.extend(other.iter());
		other.clear();
	}

	/// Creates a draining iterator that removes the specified range from the
	/// vector and yields the removed bits.
	///
	/// # Notes
	///
	/// 1. The element range is removed, regardless of whether the iterator is
	///    consumed.
	/// 2. The amount of items removed from the vector if the draining iterator
	///    is leaked, is left unspecified.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `range`: any range literal, which is used to define the range of the
	///   vector that is drained.
	///
	/// # Returns
	///
	/// An iterator over the specified range.
	///
	/// # Panics
	///
	/// Panics if the range is ill-formed, or if it is beyond the vector bounds.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0, 0, 1, 1, 1, 0, 0];
	/// assert_eq!(bv.len(), 7);
	/// for bit in bv.drain(2 .. 5) {
	///   assert!(bit);
	/// }
	/// assert!(bv.not_any());
	/// assert_eq!(bv.len(), 4);
	/// ```
	pub fn drain<R>(&mut self, range: R) -> iter::Drain<C, T>
	where R: RangeBounds<usize> {
		use core::ops::Bound::*;
		let len = self.len();
		let from = match range.start_bound() {
			Included(&n) => n,
			Excluded(&n) => n + 1,
			Unbounded   => 0,
		};
		//  First index beyond the end of the drain.
		let upto = match range.end_bound() {
			Included(&n) => n + 1,
			Excluded(&n) => n,
			Unbounded    => len,
		};
		assert!(from <= upto, "The drain start must be below the drain end");
		assert!(upto <= len, "The drain end must be within the vector bounds");

		unsafe {
			let ranging: &BitSlice<C, T> = self
				.as_bits()[from .. upto]
				//  remove the lifetime and borrow awareness
				.bitptr()
				.into_bitslice();
			self.set_len(from);

			iter::Drain {
				bitvec: NonNull::from(self),
				iter: ranging.iter(),
				tail_start: upto,
				tail_len: len - upto,
			}
		}
	}

	/// Clears the vector, removing all values.
	///
	/// Note that this method has no effect on the allocated capacity of the
	/// vector.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Effects
	///
	/// Becomes an uninhabited slice.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![1; 30];
	/// assert_eq!(bv.len(), 30);
	/// assert!(bv.iter().all(|b| b));
	/// bv.clear();
	/// assert!(bv.is_empty());
	/// ```
	///
	/// After calling `clear()`, `bv` will no longer show raw memory, so the
	/// above test cannot show that the underlying memory is not altered. This
	/// is also an implementation detail on which you should not rely.
	pub fn clear(&mut self) {
		unsafe { self.set_len(0) }
	}

	/// Splits the collection into two at the given index.
	///
	/// Returns a newly allocated `Self`. `self` contains elements `[0, at)`,
	/// and the returned `Self` contains elements `[at, self.len())`.
	///
	/// Note that the capacity of `self` does not change.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `at`: The index at which to perform the split. This must be in the
	///   domain `0 ..= self.len()`. When it is `self.len()`, an empty vector is
	///   returned.
	///
	/// # Returns
	///
	/// A new `BitVec` containing all the elements from `at` onwards.
	///
	/// # Panics
	///
	/// Panics if `at` is beyond `self.len()`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv1 = bitvec![0, 0, 0, 1, 1, 1];
	/// let bv2 = bv1.split_off(3);
	/// assert_eq!(bv1, bitvec![0, 0, 0]);
	/// assert_eq!(bv2, bitvec![1, 1, 1]);
	/// ```
	pub fn split_off(&mut self, at: usize) -> Self {
		let len = self.len();
		assert!(at <= len, "Index out of bounds: {} is beyond {}", at, len);
		match at {
			0 => mem::replace(self, Self::new()),
			n if n == len => Self::new(),
			_ => {
				let out = self.as_bits()[at ..].to_owned();
				self.truncate(at);
				out
			},
		}
	}

	/// Resizes the `BitVec` in place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, then  the vector is extended by the
	/// difference, and filled with the provided value. If `new_len` is less
	/// than `len`, then the vector is just truncated.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `new_len`: The new length of the vector.
	/// - `value`: The fill value if the vector is to be extended.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0; 4];
	/// bv.resize(8, true);
	/// assert_eq!(bv, bitvec![0, 0, 0, 0, 1, 1, 1, 1]);
	/// bv.resize(5, false);
	/// assert_eq!(bv, bitvec![0, 0, 0, 0, 1]);
	/// ```
	pub fn resize(&mut self, new_len: usize, value: bool) {
		let len = self.len();
		if new_len < len {
			self.truncate(new_len);
		}
		else if new_len > len {
			self.extend(core::iter::repeat(value).take(new_len - len));
		}
	}

	/// Creates a splicing iterator that exchanges the specified range for the
	/// `replacement` iterator, yielding the removed items. The range and its
	/// replacement do not need to be the same size.
	///
	/// # Notes
	///
	/// 1. The element range is removed and replaced even if the iterator
	///    produced by this method is not fully consumed.
	/// 2. It is unspecified how many bits are removed from the `BitVec` if the
	///    returned iterator is leaked.
	/// 3. The input iterator `replacement` is only consumed when the returned
	///    iterator is dropped.
	/// 4. This is optimal if:
	///    - the tail (elements in the `BitVec` after `range`) is empty,
	///    - `replace_with` yields fewer characters than `range`’s length,
	///    - the lower bound of `replacement.size_hint()` is exact.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `range`: A range of indices in the `BitVec` to pull out of the
	///   collection.
	/// - `replacement`: Something which can be used to provide new bits to
	///   replace the removed range.
	///
	/// The entirety of `replacement` will be inserted into the slot marked by
	/// `range`. If `replacement` is an infinite iterator, then this will hang,
	/// and crash your program.
	///
	/// # Returns
	///
	/// An iterator over the bits marked by `range`.
	///
	/// # Panics
	///
	/// Panics if the range is ill-formed, or extends past the end of the
	/// `BitVec`.
	///
	/// # Examples
	///
	/// This example starts with six bits of zero, and then splices out bits 2
	/// and 3 and replaces them with four bits of one.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![0; 6];
	/// let bv2 = bitvec![1; 4];
	///
	/// let s = bv.splice(2 .. 4, bv2).collect::<BitVec>();
	/// assert_eq!(s.len(), 2);
	/// assert!(!s[0]);
	/// assert_eq!(bv, bitvec![0, 0, 1, 1, 1, 1, 0, 0]);
	/// ```
	pub fn splice<R, I>(
		&mut self,
		range: R,
		replacement: I,
	) -> iter::Splice<C, T, <I as IntoIterator>::IntoIter>
	where R: RangeBounds<usize>, I: IntoIterator<Item=bool> {
		iter::Splice {
			drain: self.drain(range),
			splice: replacement.into_iter(),
		}
	}

	/// Sets the backing storage to the provided element.
	///
	/// This unconditionally sets each allocated element in the backing storage
	/// to the provided value, without altering the `BitVec` length or capacity.
	/// It operates on the underlying `Vec`’s memory region directly, and will
	/// ignore the `BitVec`’s cursors.
	///
	/// This has the unobservable effect of setting the allocated, but dead,
	/// bits beyond the end of the vector’s *length*, up to its *capacity*.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `element`: The value to which each allocated element in the backing
	///   store will be set.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![Local, u8; 0; 10];
	/// assert_eq!(bv.as_slice(), &[0, 0]);
	/// bv.set_elements(0xA5);
	/// assert_eq!(bv.as_slice(), &[0xA5, 0xA5]);
	/// ```
	pub fn set_elements(&mut self, element: T) {
		let ptr = self.pointer.pointer().w();
		let cap = self.capacity;
		for elt in unsafe { slice::from_raw_parts_mut(ptr, cap) } {
			*elt = element;
		}
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This addition traverses the addends from left to right, performing
	/// the addition at each index and writing the sum into `self`.
	///
	/// If `addend` expires before `self` does, `addend` is zero-extended and
	/// the carry propagates through the rest of `self`. If `self` expires
	/// before `addend`, then `self` is zero-extended and the carry propagates
	/// through the rest of `addend`, growing `self` until `addend` expires.
	///
	/// An infinite `addend` will cause unbounded memory growth until the vector
	/// overflows and panics.
	///
	/// # Parameters
	///
	/// - `self`
	/// - `addend: impl IntoIterator<Item=bool>`: A stream of bits to add into
	///   `self`, from left to right.
	///
	/// # Returns
	///
	/// The sum vector of `self` and `addend`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 0, 1];
	/// let b = bitvec![0, 0, 1, 1];
	/// let c = a.add_reverse(b);
	/// assert_eq!(c, bitvec![0, 1, 1, 0, 1]);
	/// ```
	pub fn add_reverse<I>(mut self, addend: I) -> Self
	where I: IntoIterator<Item=bool> {
		self.add_assign_reverse(addend);
		self
	}

	/// Performs “reverse” addition (left to right instead of right to left).
	///
	/// This addition traverses the addends from left to right, performing
	/// the addition at each index and writing the sum into `self`.
	///
	/// If `addend` expires before `self` does, `addend` is zero-extended and
	/// the carry propagates through the rest of `self`. If `self` expires
	/// before `addend`, then `self` is zero-extended and the carry propagates
	/// through the rest of `addend`, growing `self` until `addend` expires.
	///
	/// An infinite `addend` will cause unbounded memory growth until the vector
	/// overflows and panics.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `addend: impl IntoIterator<Item=bool>`: A stream of bits to add into
	///   `self`, from left to right.
	///
	/// # Effects
	///
	/// `self` may grow as a result of the final carry-out bit being `1` and
	/// pushed onto the right end.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut a = bitvec![0, 1, 0, 1];
	/// let     b = bitvec![0, 0, 1, 1];
	/// a.add_assign_reverse(&b);
	/// assert_eq!(a, bitvec![0, 1, 1, 0, 1]);
	/// ```
	pub fn add_assign_reverse<I>(&mut self, addend: I)
	where I: IntoIterator<Item=bool> {
		//  Set up iteration over the addend
		let mut addend = addend.into_iter().fuse();
		//  Delegate to the `BitSlice` implementation for the initial addition.
		//  If `addend` expires first, it zero-extends; if `self` expires first,
		//  `addend` will still have its remnant for the next stage.
		let mut c = self.as_bits_mut().add_assign_reverse(addend.by_ref());
		//  If `addend` still has bits to provide, zero-extend `self` and add
		//  them in.
		for b in addend {
			let (y, z) = crate::rca1(false, b, c);
			self.push(y);
			c = z;
		}
		if c {
			self.push(true);
		}
	}

	/// Force the live region of the underlying `BitSlice` to begin at `0`.
	///
	/// This method uses `BitSlice::rotate_left` to move all the live bits in
	/// the slice down to the front edge of the allocation. It exits immediately
	/// if the vector is already aligned.
	///
	/// It is not required to clear bits that have become garbage.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = &0x7Eu8.bits::<BigEndian>()[1 .. 7];
	/// assert_eq!(src.len(), 6);
	/// let mut bv = src.to_owned();
	/// assert_eq!(bv.len(), 6);
	/// assert_eq!(bv.as_slice(), &[0x7E]);
	/// assert_eq!(&bv, &0xFCu8.bits::<BigEndian>()[.. 6]);
	/// bv.force_align();
	/// assert_eq!(bv.as_slice(), &[0xFE]);
	/// ```
	pub fn force_align(&mut self) {
		let (_, head, bits) = self.pointer.raw_parts();
		let head = *head as usize;
		if head == 0 {
			return;
		}
		//  Extend the span to include the front of the head element
		let full = bits + head;
		unsafe {
			self.pointer.set_head(0.idx());
			self.pointer.set_len(full);
		}
		//  Shift everything down
		for (to, from) in (head ..).take(bits).enumerate() {
			unsafe { self.copy(from, to); }
		}
		//  And discard the garbage now at the back.
		unsafe { self.pointer.set_len(bits); }
	}

	/// Changes the cursor type on the vector handle, without changing its
	/// contents.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An equivalent vector handle with a new cursor type. The contents of the
	/// backing storage are unchanged.
	///
	/// To reorder the bits in memory, drain this vector into a new handle with
	/// the desired cursor type.
	pub fn change_cursor<D>(self) -> BitVec<D, T>
	where D: Cursor {
		let (bp, cap) = (self.pointer, self.capacity);
		mem::forget(self);
		unsafe { BitVec::from_raw_parts(bp, cap) }
	}

	/// Degrades a `BitVec` to a `BitBox`, freezing its size.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// Itself, with its size frozen and ungrowable.
	pub fn into_boxed_bitslice(self) -> BitBox<C, T> {
		let pointer = self.pointer;
		//  Convert the Vec allocation into a Box<[T]> allocation
		mem::forget(self.into_boxed_slice());
		unsafe { BitBox::from_raw(pointer) }
	}

	/// Degrades a `BitVec` to a standard boxed slice.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// A boxed slice of the data the `BitVec` had owned.
	pub fn into_boxed_slice(self) -> Box<[T]> {
		self.into_vec().into_boxed_slice()
	}

	/// Degrades a `BitVec` to a standard `Vec`.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The plain vector underlying the `BitVec`.
	pub fn into_vec(mut self) -> Vec<T> {
		self.force_align();
		let slice = self.as_mut_slice();
		let out = unsafe {
			Vec::from_raw_parts(slice.as_mut_ptr(), slice.len(), self.capacity)
		};
		mem::forget(self);
		out
	}

	/// Permits a function to modify the `Vec<T>` underneath a `BitVec<_, T>`.
	///
	/// This produces a `Vec<T>` structure referring to the same data region as
	/// the `BitVec<_, T>`, allows a function to mutably view it, and then
	/// forgets the `Vec<T>` after the function concludes.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `func`: A function which receives a mutable borrow to the `Vec<T>`
	///   underlying the `BitVec<_, T>`.
	///
	/// # Type Parameters
	///
	/// - `F: FnOnce(&mut Vec<T>) -> R`: Any callable object (function or
	///   closure) which receives a mutable borrow of a `Vec<T>`.
	///
	/// - `R`: The return value from the called function or closure.
	fn do_unto_vec<F, R>(&mut self, func: F) -> R
	where F: FnOnce(&mut Vec<T>) -> R {
		let slice = self.pointer.as_mut_slice();
		let mut v = unsafe {
			Vec::from_raw_parts(slice.as_mut_ptr(), slice.len(), self.capacity)
		};
		let out = func(&mut v);
		//  The only change is that the pointer might relocate. The region data
		//  will remain untouched. Vec guarantees it will never produce an
		//  invalid pointer.
		unsafe { self.pointer.set_pointer(v.as_ptr()); }
		// self.pointer = unsafe { BitPtr::new_unchecked(v.as_ptr(), e, h, t) };
		self.capacity = v.capacity();
		mem::forget(v);
		out
	}

	/// Permits a function to view the `Vec<T>` underneath a `BitVec<_, T>`.
	///
	/// This produces a `Vec<T>` structure referring to the same data region as
	/// the `BitVec<_, T>`, allows a function to immutably view it, and then
	/// forgets the `Vec<T>` after the function concludes.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `func`: A function which receives an immutable borrow to the `Vec<T>`
	///   underlying the `BitVec<_, T>`.
	///
	/// # Returns
	///
	/// The return value of `func`.
	///
	/// # Type Parameters
	///
	/// - `F: FnOnce(&Vec<T>)`: Any callable object (function or closure) which
	///   receives an immutable borrow of a `Vec<T>` and returns nothing.
	///
	/// # Safety
	///
	/// This produces an empty `Vec<T>` if the `BitVec<_, T>` is empty.
	fn do_with_vec<F, R>(&self, func: F) -> R
	where F: FnOnce(&Vec<T>) -> R {
		let slice = self.pointer.as_mut_slice();
		let v: Vec<T> = unsafe {
			Vec::from_raw_parts(slice.as_mut_ptr(), slice.len(), self.capacity)
		};
		let out = func(&v);
		mem::forget(v);
		out
	}
}

/// Signifies that `BitSlice` is the borrowed form of `BitVec`.
impl<C, T> Borrow<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
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
	fn borrow(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

/// Signifies that `BitSlice` is the borrowed form of `BitVec`.
impl<C, T> BorrowMut<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
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
	fn borrow_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

impl<C, T> Clone for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn clone(&self) -> Self {
		let new_vec = self.do_with_vec(Clone::clone);
		let capacity = new_vec.capacity();
		let mut pointer = self.pointer;
		unsafe { pointer.set_pointer(new_vec.as_ptr()); }
		mem::forget(new_vec);
		Self {
			_cursor: PhantomData,
			pointer, // unsafe { BitPtr::new_unchecked(ptr, e, h, t) },
			capacity,
		}
	}

	fn clone_from(&mut self, other: &Self) {
		let slice = other.pointer.as_slice();
		self.clear();
		//  Copy the other data region into the underlying vector, then grab its
		//  pointer and capacity values.
		let (ptr, capacity) = self.do_unto_vec(|v| {
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

impl<C, T> Eq for BitVec<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> cmp::Ordering {
		self.as_bits().cmp(rhs.as_bits())
	}
}

/** Tests if two `BitVec`s are semantically — not bitwise — equal.

It is valid to compare two vectors of different cursor or element types.

The equality condition requires that they have the same number of stored bits
and that each pair of bits in semantic order are identical.
**/
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
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
	/// let l: BitVec<LittleEndian, u16> = bitvec![LittleEndian, u16; 0, 1, 0, 1];
	/// let r: BitVec<BigEndian, u32> = bitvec![BigEndian, u32; 0, 1, 0, 1];
	/// assert!(l == r);
	/// ```
	///
	/// This example uses the same types to prove that raw, bitwise, values are
	/// not used for equality comparison.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let l: BitVec<BigEndian, u8> = bitvec![BigEndian, u8; 0, 1, 0, 1];
	/// let r: BitVec<LittleEndian, u8> = bitvec![LittleEndian, u8; 0, 1, 0, 1];
	///
	/// assert_eq!(l, r);
	/// assert_ne!(l.as_slice(), r.as_slice());
	/// ```
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.as_bits().eq(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bits().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.as_bits().eq(*rhs)
	}
}

/** Compares two `BitVec`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one vector to have a set bit
where the other vector has a clear bit. If the vectors are different, the vector
with the set bit sorts greater than the vector with the clear bit.

If one of the vectors is exhausted before they differ, the longer vector is
greater.
**/
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
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
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<cmp::Ordering> {
		self.as_bits().partial_cmp(rhs.as_bits())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<cmp::Ordering> {
		self.as_bits().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<cmp::Ordering> {
		self.as_bits().partial_cmp(*rhs)
	}
}

impl<C, T> AsMut<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_bits_mut()
	}
}

/// Gives write access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<C, T> AsMut<[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

impl<C, T> AsRef<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.as_bits()
	}
}

/// Gives read access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<C, T> AsRef<[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// assert_eq!(&[0, 0b1000_0000], bv.as_slice());
	/// ```
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<C, T> From<&BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

/** Builds a `BitVec` out of a slice of `bool`.

This is primarily for the `bitvec!` macro; it is not recommended for general
use.
**/
impl<C, T> From<&[bool]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[bool]) -> Self {
		src.iter().cloned().collect()
	}
}

impl<C, T> From<BitBox<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: BitBox<C, T>) -> Self {
		Self::from_boxed_bitslice(src)
	}
}

impl<C, T> From<&[T]> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<C, T> From<Box<[T]>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_bitslice(BitBox::from_boxed_slice(src))
	}
}

impl<C, T> Into<Box<[T]>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

/** Builds a `BitVec` out of a `Vec` of elements.

This moves the memory as-is from the source buffer into the new `BitVec`. The
source buffer will be unchanged by this operation, so you don't need to worry
about using the correct cursor type.
**/
impl<C, T> From<Vec<T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Vec<T>) -> Self {
		Self::from_vec(src)
	}
}

impl<C, T> Into<Vec<T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Vec<T> {
		self.into_vec()
	}
}

impl<C, T> Default for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn default() -> Self {
		Self::new()
	}
}

/** Prints the `BitVec` for debugging.

The output is of the form `BitVec<C, T> [ELT, *]`, where `<C, T>` is the cursor
and element type, with square brackets on each end of the bits and all the live
elements in the vector printed in binary. The printout is always in semantic
order, and may not reflect the underlying store. To see the underlying store,
use `format!("{:?}", self.as_slice());` instead.

The alternate character `{:#?}` prints each element on its own line, rather than
separated by a space.
**/
impl<C, T> Debug for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitVec` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![LittleEndian, u16;
	///   0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1
	/// ];
	/// assert_eq!(
	///   "BitVec<LittleEndian, u16> [0101000011110101]",
	///   &format!("{:?}", bv)
	/// );
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		f.write_str("BitVec<")?;
		f.write_str(C::TYPENAME)?;
		f.write_str(", ")?;
		f.write_str(T::TYPENAME)?;
		f.write_str("> ")?;
		Display::fmt(self.as_bits(), f)
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
impl<C, T> Display for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitVec` contents for display.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 0, 1, 0, 0, 1, 0, 1, 1, 0, 1];
	/// assert_eq!("[01001011, 01]", &format!("{}", bv));
	/// ```
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bits(), f)
	}
}

/// Writes the contents of the `BitVec`, in semantic bit order, into a hasher.
impl<C, T> Hash for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Writes each bit of the `BitVec`, as a full `bool`, into the hasher.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `hasher`: The hashing pool into which the vector is written.
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		<BitSlice<C, T> as Hash>::hash(self, hasher)
	}
}

#[cfg(feature = "std")]
impl<C, T> Write for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let amt = cmp::min(
			buf.len(),
			BitPtr::<T>::MAX_INDX - self.as_slice().len(),
		);
		let bits = BitSlice::<C, u8>::from_slice(buf);
		self.reserve(bits.len());
		self.extend(bits);
		Ok(amt)
	}

	fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// `BitVec` is safe to move across thread boundaries, as is `&mut BitVec`.
unsafe impl<C, T> Send for BitVec<C, T>
where C: Cursor, T: BitStore {}

/// `&BitVec` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitVec<C, T>
where C: Cursor, T: BitStore {}

mod r#override;
mod iter;
mod ops;

#[cfg(test)]
mod tests;
