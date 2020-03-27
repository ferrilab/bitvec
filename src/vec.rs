/*! `BitVec` structure

This module holds the main working type of the library. Clients can use
`BitSlice` directly, but `BitVec` is much more useful for most work.

The `BitSlice` module discusses the design decisions for the separation between
slice and vector types.
!*/

#![cfg(feature = "alloc")]

use crate::{
	access::BitAccess,
	boxed::BitBox,
	indices::Indexable,
	order::{
		BitOrder,
		Local,
	},
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
};

use alloc::{
	borrow::ToOwned,
	vec::Vec,
};

use core::{
	marker::PhantomData,
	mem,
};

/** A compact [`Vec`] of bits, whose order and storage type can be customized.

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
let bs: &BitSlice = &bv;
```

In Rust, it’s more common to pass slices as arguments rather than vectors when
you do not want to grow or shrink it. The same goes for [`Vec`] and [`&[]`], and
[`String`] and [`&str`].

# Capacity and reallocation

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
[`BitVec::with_capacity`] whenever possible to specify how big the bit vector is
expected to get.

# Guarantees

Due to its incredibly fundamental nature, `BitVec` makes a lot of guarantees
about its design. This ensures that it is as low-overhead as possible in the
general case, and can be correctly manipulated in fundamental ways by `unsafe`
code.

Most fundamentally, `BitVec` is and always will be a `([`BitPtr`], capacity)`
doublet. No more, no less. The order of these fields is unspecified, and you
should **only** interact with the members through the provided APIs. Note that
`BitPtr` is ***not directly manipulable***, and must ***never*** be written or
interpreted as anything but opaque binary data by user code.

When a `BitVec` has allocated memory, then the memory to which it points is on
the heap (as defined by the allocator Rust is configured to use by default), and
its pointer points to [`len`] initialized bits in order of the [`BitOrder`] type
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

- `O: BitOrder`: An implementor of the [`BitOrder`] trait. This type is used to
  convert semantic indices into concrete bit positions in elements, and store or
  retrieve bit values from the storage type.
- `T: BitStore`: An implementor of the [`BitStore`] trait: `u8`, `u16`, `u32`,
  or `u64` (64-bit systems only). This is the actual type in memory that the
  vector will use to store data.

# Safety

The `BitVec` handle has the same *size* as standard Rust `Vec` handles, but it
is ***extremely binary incompatible*** with them. Attempting to treat
`BitVec<_, T>` as `Vec<T>` in any manner except through the provided APIs is
***catastrophically*** unsafe and unsound.

[`BitSlice`]: ../slice/struct.BitSlice.html
[`BitVec::with_capacity`]: #method.with_capacity
[`BitStore`]: ../store/trait.BitStore.html
[`BitOrder`]: ../order/trait.BitOrder.html
[`Index`]: https://doc.rust-lang.org/stable/std/ops/trait.Index.html
[`String`]: https://doc.rust-lang.org/stable/std/string/struct.String.html
[`Vec`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html
[`bitvec!`]: ../macro.bitvec.html
[`clear_on_drop`]: https://docs.rs/clear_on_drop
[`len`]: #method.len
[`shrink_to_fit`]: #method.shrink_to_fit
[`&str`]: https://doc.rust-lang.org/stable/std/primitive.str.html
[`&[]`]: https://doc.rust-lang.org/stable/std/primitive.slice.html
**/
#[repr(C)]
pub struct BitVec<O = Local, T = usize>
where O: BitOrder, T: BitStore {
	/// Phantom `BitOrder` member to satisfy the constraint checker.
	_order: PhantomData<O>,
	/// Slice pointer over the owned memory.
	pointer: BitPtr<T>,
	/// The number of *elements* this vector has allocated.
	capacity: usize,
}

impl<O, T> BitVec<O, T>
where O: BitOrder, T: BitStore {
	/// Constructs a `BitVec` from a value repeated many times.
	///
	/// This function is equivalent to the `bitvec![O, T; bit; len]` macro call,
	/// and is in fact the implementation of that macro syntax.
	///
	/// # Parameters
	///
	/// - `bit`: The bit value to which all `len` allocated bits will be set.
	/// - `len`: The number of live bits in the constructed `BitVec`.
	///
	/// # Returns
	///
	/// A `BitVec` with `len` live bits, all set to `bit`.
	pub fn repeat(bit: bool, len: usize) -> Self {
		let mut out = Self::with_capacity(len);
		unsafe { out.set_len(len); }
		out.set_elements(if bit { T::TRUE } else { T::FALSE });
		out
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
	/// let bv = BitVec::<Msb0, u8>::from_element(5);
	/// assert_eq!(bv.count_ones(), 2);
	/// ```
	#[inline]
	pub fn from_element(elt: T) -> Self {
		let mut v = Vec::with_capacity(1);
		v.push(elt);
		Self::from_vec(v)
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
	/// let bv = BitVec::<Msb0, u8>::from_slice(&src[..]);
	/// assert!(bv[5]);
	/// assert!(bv[7]);
	/// assert!(bv[12]);
	/// assert!(bv[14]);
	/// ```
	#[inline]
	pub fn from_slice(slice: &[T]) -> Self {
		Self::from_vec(slice.to_owned())
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
	/// let bv = BitVec::<Msb0, u8>::from_vec(vec![1, 2, 4, 8]);
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
		let bs = BitSlice::<O, T>::from_slice(&vec[..]);
		let pointer = bs.bitptr();
		let capacity = vec.capacity();
		mem::forget(vec);
		Self {
			_order: PhantomData,
			pointer,
			capacity,
		}
	}

	/// Clones a `&BitSlice` into a `BitVec`.
	///
	/// This is the only method by which a `BitVec` can be created whose first
	/// live bit is not at the `0` position. This behavior, though
	/// unconventional for common uses of `BitVec`, allows for a more efficient
	/// clone of any `BitSlice` region without shifting each bit in the region
	/// down to fit the `0` starting position.
	///
	/// Misaligned `BitVec`s **do not** have any adverse effect on usage other
	/// than the in-memory representation.
	///
	/// Whenever a `BitVec` is emptied, its head index is always set to `0`, and
	/// will begin from the aligned position on future refills.
	///
	/// The [`::force_align`] method will shift the `BitVec`’s data to begin at
	/// the `0` index, if you require this property.
	///
	/// # Parameters
	///
	/// - `slice`: The source `BitSlice` region. This may have any head index,
	///   and its memory will be copied element-wise into the new buffer.
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
	/// let bs = [0u8, !0].bits::<Msb0>();
	/// let bv = BitVec::from_bitslice(bs);
	/// assert_eq!(bv.len(), 16);
	/// assert!(bv.some());
	/// ```
	///
	/// [`::force_align`]: #method.force_align
	pub fn from_bitslice(slice: &BitSlice<O, T>) -> Self {
		let mut pointer = slice.bitptr();
		let source = pointer.as_access_slice();

		//  Create a blank buffer into which the source will be copied.
		let mut v = Vec::with_capacity(source.len());

		//  Copy the source into the buffer. This must be done per-element, so
		//  that atomic systems will correctly synchronize.
		source.iter().for_each(|elt| v.push(elt.load()));

		/* Target the copied pointer to the buffer’s region, preserving its
		length and offset information. This enables `BitVec` to efficiently
		lift from any `&BitSlice`, without having to reälign the source per-bit.
		*/
		unsafe { pointer.set_pointer(v.as_ptr() as *const T); }

		let capacity = v.capacity();
		mem::forget(v);
		Self {
			_order: PhantomData,
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
	pub fn from_boxed_bitslice(slice: BitBox<O, T>) -> Self {
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
	#[inline]
	pub unsafe fn from_raw_parts(pointer: BitPtr<T>, capacity: usize) -> Self {
		Self {
			_order: PhantomData,
			pointer,
			capacity,
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
	/// let bs = bv.as_bitslice();
	/// ```
	#[inline]
	pub fn as_bitslice(&self) -> &BitSlice<O, T> {
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
	/// let bs = bv.as_mut_bitslice();
	/// ```
	#[inline]
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<O, T> {
		self.pointer.into_bitslice_mut()
	}

	/// Sets the backing storage to the provided element.
	///
	/// This unconditionally sets each live element in the backing buffer to the
	/// provided value, without altering the `BitVec` length or capacity. It
	/// operates on the underlying `Vec`’s memory buffer directly, and ignores
	/// the `BitVec`’s cursors.
	///
	/// It is an implementation detail as to whether this affects the value of
	/// allocated, but not currently used, elements in the buffer. Behavior of
	/// this method on elements not visible through `self.as_slice()` is not
	/// specified.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `element`: The value to which each live element in the backing store
	///   will be set.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![Local, u8; 0; 10];
	/// //  note: the second element is not required to be zero, only to have
	/// //  bits `0` and `1` according to `Local` be `0`.
	/// assert_eq!(bv.as_slice()[0], 0);
	/// bv.set_elements(0xA5);
	/// assert_eq!(bv.as_slice(), &[0xA5, 0xA5]);
	/// ```
	#[inline]
	pub fn set_elements(&mut self, element: T) {
		self.as_mut_slice().iter_mut().for_each(|elt| *elt = element);
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
	/// a.add_assign_reverse(b.iter().copied());
	/// assert_eq!(a, bitvec![0, 1, 1, 0, 1]);
	/// ```
	pub fn add_assign_reverse<I>(&mut self, addend: I)
	where I: IntoIterator<Item=bool> {
		//  Set up iteration over the addend
		let mut addend = addend.into_iter().fuse();
		//  Delegate to the `BitSlice` implementation for the initial addition.
		//  If `addend` expires first, it zero-extends; if `self` expires first,
		//  `addend` will still have its remnant for the next stage.
		let mut c = self.as_mut_bitslice().add_assign_reverse(addend.by_ref());
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

	/// Changes the order type on the vector handle, without changing its
	/// contents.
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// An equivalent vector handle with a new order type. The contents of the
	/// backing storage are unchanged.
	///
	/// To reorder the bits in memory, drain this vector into a new handle with
	/// the desired order type.
	pub fn change_order<P>(self) -> BitVec<P, T>
	where P: BitOrder {
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
	pub fn into_boxed_bitslice(self) -> BitBox<O, T> {
		let (_, head, bits) = self.bitptr().raw_parts();
		let boxed = self.into_vec().into_boxed_slice();
		let addr = boxed.as_ptr();
		mem::forget(boxed);
		unsafe {
			BitBox::from_raw(
				BitPtr::new_unchecked(addr, head, bits).as_mut_ptr(),
			)
		}
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
	pub fn into_vec(self) -> Vec<T> {
		let slice = self.pointer.as_mut_slice();
		let out = unsafe {
			Vec::from_raw_parts(slice.as_mut_ptr(), slice.len(), self.capacity)
		};
		mem::forget(self);
		out
	}

	/// Ensures that the live region of the underlying memory begins at the `0`
	/// bit position.
	///
	/// # Notes
	///
	/// This method is currently implemented as a linear traversal that moves
	/// each bit individually from its original index to its final position.
	/// This is `O(n)` in the bit length of the vector.
	///
	/// It is possible to create an optimized rotation behavior that only moves
	/// a few bits individually, then moves elements in a gallop. The speed
	/// difference is proportional to the width of the element type.
	///
	/// When this behavior is implemented, `force_align` will be rewritten to
	/// take advantage of it. For now, it remains slow.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = &bits![Msb0, u8; 1, 0, 1, 1, 0, 1, 1, 0][1 .. 7];
	/// assert_eq!(src.len(), 6);
	/// let mut bv = src.to_owned();
	/// assert_eq!(bv.len(), 6);
	/// assert_eq!(bv.as_slice()[0], 0xB6);
	/// bv.force_align();
	/// assert_eq!(bv.as_slice()[0], 0x6E);
	/// ```
	pub fn force_align(&mut self) {
		let (_, head, bits) = self.pointer.raw_parts();
		let head = *head as usize;
		if head == 0 {
			return;
		}
		let tail = head + bits;
		unsafe {
			self.pointer.set_head(0.idx());
			self.pointer.set_len(tail);
			for (to, from) in (head .. tail).enumerate() {
				self.copy_unchecked(from, to);
			}
			self.pointer.set_len(bits);
		}
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
	fn with_vec<F, R>(&mut self, func: F) -> R
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
}

mod api;
mod iter;
mod ops;
mod traits;

pub use api::*;
pub use iter::*;
