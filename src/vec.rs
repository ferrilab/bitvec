/*! `BitVec` structure

This module holds the main working type of the library. Clients can use
`BitSlice` directly, but `BitVec` is much more useful for most work.

The `BitSlice` module discusses the design decisions for the separation between
slice and vector types.
!*/

#![cfg(any(feature = "alloc", feature = "std"))]

use crate::{
	boxed::BitBox,
	cursor::{
		Cursor,
		Local,
	},
	indices::Indexable,
	pointer::BitPtr,
	slice::BitSlice,
	store::{
		BitStore,
		Word,
	},
};

#[cfg(feature = "alloc")]
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
	clone::Clone,
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
		Display,
		Formatter,
	},
	hash::{
		Hash,
		Hasher,
	},
	iter::{
		self,
		DoubleEndedIterator,
		ExactSizeIterator,
		Extend,
		FromIterator,
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
		Drop,
		Index,
		IndexMut,
		Range,
		RangeBounds,
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
		Sub,
		SubAssign,
	},
	ptr::{
		self,
		NonNull,
	},
	slice,
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
its pointer points to [`len`] initialized bits in order of the [`Cursor`] type
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

- `C: Cursor`: An implementor of the [`Cursor`] trait. This type is used to
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

[`BitSlice`]: ../struct.BitSlice.html
[`BitVec::with_capacity`]: #method.with_capacity
[`BitStore`]: ../trait.BitStore.html
[`Cursor`]: ../trait.Cursor.html
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
	/// # Parameters
	///
	/// - `slice`
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
	pub fn from_bitslice(slice: &BitSlice<C, T>) -> Self {
		let mut out = Self::with_capacity(slice.len());
		out.extend(slice.iter().copied());
		out
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
	pub fn as_bitslice(&self) -> &BitSlice<C, T> {
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
	pub fn as_mut_bitslice(&mut self) -> &mut BitSlice<C, T> {
		self.pointer.into_bitslice_mut()
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
		self.do_unto_vec(|v| {
			let (ptr, cap) = (v.as_mut_ptr(), v.capacity());
			for elt in unsafe { slice::from_raw_parts_mut(ptr, cap) } {
				*elt = element;
			}
		})
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
		self.as_bitslice()
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
		self.as_mut_bitslice()
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
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bitslice().cmp(rhs.as_bitslice())
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
		self.as_bitslice().eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(*rhs)
	}
}

// impl<A, B, C, D> PartialEq<&mut BitSlice<C, D>> for BitVec<A, B>
// where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
// 	fn eq(&self, rhs: &&mut BitSlice<C, D>) -> bool {
// 		self.as_bitslice().eq(*rhs)
// 	}
// }

impl<A, B, C, D> PartialEq<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

// impl<A, B, C, D> PartialEq<BitVec<C, D>> for &mut BitSlice<A, B>
// where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
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
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitVec<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(*rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

// impl<A, B, C, D> PartialOrd<&mut BitSlice<C, D>> for BitVec<A, B>
// where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
// 	fn partial_cmp(&self, rhs: &&mut BitSlice<C, D>) -> Option<Ordering> {
// 		self.as_bitslice().partial_cmp(*rhs)
// 	}
// }

// impl<A, B, C, D> PartialOrd<BitVec<C, D>> for &mut BitSlice<A, B>
// where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
// 	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
// 		(**self).partial_cmp(rhs.as_bitslice())
// 	}
// }

impl<C, T> AsMut<BitSlice<C, T>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_mut_bitslice()
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
		self.as_bitslice()
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
		Display::fmt(&**self, f)
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
		use std::cmp;
		let amt = cmp::min(buf.len(), BitPtr::<T>::MAX_BITS - self.len());
		self.extend(<&BitSlice<C, u8>>::from(buf).iter().copied());
		Ok(amt)
	}

	fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/** Extends a `BitVec` with the contents of another bitstream.

At present, this just calls `.push()` in a loop. When specialization becomes
available, it will be able to more intelligently perform bulk moves from the
source into `self` when the source is `BitSlice`-compatible.
**/
impl<C, T> Extend<bool> for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Extends a `BitVec` from another bitstream.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `src`: A source bitstream.
	///
	/// # Type Parameters
	///
	/// - `I: IntoIterator<Item=bool>`: The source bitstream with which to
	///   extend `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![BigEndian, u8; 0; 4];
	/// bv.extend(bitvec![1; 4]);
	/// assert_eq!(0x0F, bv.as_slice()[0]);
	/// ```
	fn extend<I: IntoIterator<Item=bool>>(&mut self, src: I) {
		let iter = src.into_iter();
		match iter.size_hint() {
			(_, Some(hi)) => self.reserve(hi),
			(lo, None) => self.reserve(lo),
		}
		iter.for_each(|b| self.push(b));
	}
}

/// Permits the construction of a `BitVec` by using `.collect()` on an iterator
/// of `bool`.
impl<C, T> FromIterator<bool> for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Collects an iterator of `bool` into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// use std::iter::repeat;
	/// let bv: BitVec<BigEndian, u8> = repeat(true)
	///   .take(4)
	///   .chain(repeat(false).take(4))
	///   .collect();
	/// assert_eq!(bv.as_slice()[0], 0xF0);
	/// ```
	fn from_iter<I: IntoIterator<Item=bool>>(src: I) -> Self {
		let iter = src.into_iter();
		let mut bv = match iter.size_hint() {
			| (_, Some(len))
			| (len, _)
			=> Self::with_capacity(len),
		};
		for bit in iter {
			bv.push(bit);
		}
		bv
	}
}

/** Produces an iterator over all the bits in the vector.

This iterator follows the ordering in the vector type, and implements
`ExactSizeIterator`, since `BitVec`s always know exactly how large they are, and
`DoubleEndedIterator`, since they have known ends.
**/
impl<C, T> IntoIterator for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Item = bool;
	type IntoIter = IntoIter<C, T>;

	/// Iterates over the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 1, 1, 1, 1, 0, 0, 0, 0];
	/// let mut count = 0;
	/// for bit in bv {
	///   if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			region: self.pointer,
			bitvec: self,
		}
	}
}

impl<'a, C, T> IntoIterator for &'a BitVec<C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = &'a bool;
	type IntoIter = <&'a BitSlice<C, T> as IntoIterator>::IntoIter;

	fn into_iter(self) -> Self::IntoIter {
		<&'a BitSlice<C, T> as IntoIterator>::into_iter(self)
	}
}

/// `BitVec` is safe to move across thread boundaries, as is `&mut BitVec`.
unsafe impl<C, T> Send for BitVec<C, T>
where C: Cursor, T: BitStore {}

/// `&BitVec` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitVec<C, T>
where C: Cursor, T: BitStore {}

/** Adds two `BitVec`s together, zero-extending the shorter.

`BitVec` addition works just like adding numbers longhand on paper. The first
bits in the `BitVec` are the highest, so addition works from right to left, and
the shorter `BitVec` is assumed to be extended to the left with zero.

The output `BitVec` may be one bit longer than the longer input, if addition
overflowed.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<C, T> Add for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Adds two `BitVec`s.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 0, 1];
	/// let b = bitvec![0, 0, 1, 1];
	/// let s = a + b;
	/// assert_eq!(bitvec![1, 0, 0, 0], s);
	/// ```
	///
	/// This example demonstrates the addition of differently-sized `BitVec`s,
	/// and will overflow.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![1; 4];
	/// let b = bitvec![1; 1];
	/// let s = b + a;
	/// assert_eq!(bitvec![1, 0, 0, 0, 0], s);
	/// ```
	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

/** Adds another `BitVec` into `self`, zero-extending the shorter.

`BitVec` addition works just like adding numbers longhand on paper. The first
bits in the `BitVec` are the highest, so addition works from right to left, and
the shorter `BitVec` is assumed to be extended to the left with zero.

The output `BitVec` may be one bit longer than the longer input, if addition
overflowed.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<C, T> AddAssign for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Adds another `BitVec` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut a = bitvec![1, 0, 0, 1];
	/// let b = bitvec![0, 1, 1, 1];
	/// a += b;
	/// assert_eq!(a, bitvec![1, 0, 0, 0, 0]);
	/// ```
	fn add_assign(&mut self, mut addend: Self) {
		use core::iter::repeat;
		//  If the other vec is longer, swap them before continuing.
		if addend.len() > self.len() {
			mem::swap(self, &mut addend);
		}
		//  Now that self.len() >= addend.len(), proceed with addition.
		let mut c = false;
		let mut stack = BitVec::<C, T>::with_capacity(self.len());
		let addend = addend.into_iter().rev().chain(repeat(false));
		for (a, b) in self.iter().copied().rev().zip(addend) {
			let (y, z) = crate::rca1(a, b, c);
			stack.push(y);
			c = z;
		}
		//  If the carry made it to the end, push it.
		if c {
			stack.push(true);
		}
		//  Unwind the stack into `self`.
		self.clear();
		self.extend(stack.into_iter().rev());
	}
}

/** Performs the Boolean `AND` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<C, T, I> BitAnd<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `AND`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![BigEndian, u8; 0, 1, 0, 1];
	/// let rhs = bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// let and = lhs & rhs;
	/// assert_eq!("[0001]", &format!("{}", and));
	/// ```
	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

/** Performs the Boolean `AND` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<C, T, I> BitAndAssign<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `AND`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![BigEndian, u8; 0, 1, 0, 1];
	///         src &= bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// assert_eq!("[0001]", &format!("{}", src));
	/// ```
	fn bitand_assign(&mut self, rhs: I) {
		// let mut len = 0;
		// for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
		// 	let val = self[idx] & other;
		// 	self.set(idx, val);
		// 	len += 1;
		// }
		let len = rhs.into_iter()
			.take(self.len())
			.enumerate()
			.map(|(i, r)| {
				let l = unsafe { *self.get_unchecked(i) };
				unsafe { self.set_unchecked(i, l & r); }
			})
			.count();
		self.truncate(len);
	}
}

/** Performs the Boolean `OR` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<C, T, I> BitOr<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `OR`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![0, 1, 0, 1];
	/// let rhs = bitvec![0, 0, 1, 1];
	/// let or  = lhs | rhs;
	/// assert_eq!("[0111]", &format!("{}", or));
	/// ```
	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

/** Performs the Boolean `OR` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<C, T, I> BitOrAssign<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `OR`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![0, 1, 0, 1];
	///         src |= bitvec![0, 0, 1, 1];
	/// assert_eq!("[0111]", &format!("{}", src));
	/// ```
	fn bitor_assign(&mut self, rhs: I) {
		// let mut len = 0;
		// for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
		// 	let val = self[idx] | other;
		// 	self.set(idx, val);
		// 	len += 1;
		// }
		let len = rhs.into_iter()
			.take(self.len())
			.enumerate()
			.map(|(i, r)| {
				let l = unsafe { *self.get_unchecked(i) };
				unsafe { self.set_unchecked(i, l | r); }
			})
			.count();
		self.truncate(len);
	}
}

/** Performs the Boolean `XOR` operation between each element of a `BitVec` and
anything that can provide a stream of `bool` values (such as another `BitVec`,
or any `bool` generator of your choice). The `BitVec` emitted will have the
length of the shorter sequence of bits -- if one is longer than the other, the
extra bits will be ignored.
**/
impl<C, T, I> BitXor<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// `XOR`s a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lhs = bitvec![0, 1, 0, 1];
	/// let rhs = bitvec![0, 0, 1, 1];
	/// let xor = lhs ^ rhs;
	/// assert_eq!("[0110]", &format!("{}", xor));
	/// ```
	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

/** Performs the Boolean `XOR` operation in place on a `BitVec`, using a stream
of `bool` values as the other bit for each operation. If the other stream is
shorter than `self`, `self` will be truncated when the other stream expires.
**/
impl<C, T, I> BitXorAssign<I> for BitVec<C, T>
where C: Cursor, T: BitStore, I: IntoIterator<Item=bool> {
	/// `XOR`s another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src  = bitvec![0, 1, 0, 1];
	///         src ^= bitvec![0, 0, 1, 1];
	/// assert_eq!("[0110]", &format!("{}", src));
	/// ```
	fn bitxor_assign(&mut self, rhs: I) {
		// let mut len = 0;
		// for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
		// 	let val = self[idx] ^ other;
		// 	self.set(idx, val);
		// 	len += 1;
		// }
		let len = rhs.into_iter()
			.take(self.len())
			.enumerate()
			.map(|(i, r)| {
				let l = unsafe { *self.get_unchecked(i) };
				unsafe { self.set_unchecked(i, l ^ r); }
			})
			.count();
		self.truncate(len);
	}
}

/** Reborrows the `BitVec` as a `BitSlice`.

This mimics the separation between `Vec<T>` and `[T]`.
**/
impl<C, T> Deref for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Target = BitSlice<C, T>;

	/// Dereferences `&BitVec` down to `&BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec = bitvec![1; 4];
	/// let bref: &BitSlice = &bv;
	/// assert!(bref[2]);
	/// ```
	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

/** Mutably reborrows the `BitVec` as a `BitSlice`.

This mimics the separation between `Vec<T>` and `[T]`.
**/
impl<C, T> DerefMut for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Dereferences `&mut BitVec` down to `&mut BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = bitvec![0; 6];
	/// let bref: &mut BitSlice = &mut bv;
	/// assert!(!bref[5]);
	/// bref.set(5, true);
	/// assert!(bref[5]);
	/// ```
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

/// Readies the underlying storage for Drop.
impl<C, T> Drop for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Rebuild the interior `Vec` and let it run the deallocator.
	fn drop(&mut self) {
		let bp = mem::replace(&mut self.pointer, BitPtr::empty());
		//  Build a Vec<T> out of the elements, and run its destructor.
		let (ptr, cap) = (bp.pointer(), self.capacity);
		drop(unsafe { Vec::from_raw_parts(ptr.w(), 0, cap) });
	}
}

/// Gets the bit at a specific index. The index must be less than the length of
/// the `BitVec`.
impl<C, T> Index<usize> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = bool;

	/// Looks up a single bit by semantic count.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
	/// assert!(!bv[7]); // ---------------------------------^  |  |
	/// assert!( bv[8]); // ------------------------------------^  |
	/// assert!(!bv[9]); // ---------------------------------------^
	/// ```
	///
	/// If the index is greater than or equal to the length, indexing will
	/// panic.
	///
	/// The below test will panic when accessing index 1, as only index 0 is
	/// valid.
	///
	/// ```rust,should_panic
	/// use bitvec::prelude::*;
	///
	/// let mut bv: BitVec = BitVec::new();
	/// bv.push(true);
	/// bv[1];
	/// ```
	fn index(&self, cursor: usize) -> &Self::Output {
		&self.as_bitslice()[cursor]
	}
}

impl<C, T> Index<Range<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: Range<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<Range<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeFrom<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeFrom<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeFull> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self.as_bitslice()
	}
}

impl<C, T> IndexMut<RangeFull> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self.as_mut_bitslice()
	}
}

impl<C, T> Index<RangeInclusive<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeInclusive<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeTo<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeTo<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeTo<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<C, T> Index<RangeToInclusive<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = BitSlice<C, T>;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<C, T> IndexMut<RangeToInclusive<usize>> for BitVec<C, T>
where C: Cursor, T: BitStore {
	fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

/** 2’s-complement negation of a `BitVec`.

In 2’s-complement, negation is defined as bit-inversion followed by adding one.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<C, T> Neg for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Numerically negates a `BitVec` using 2’s-complement arithmetic.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![0, 1, 1];
	/// let ne = -bv;
	/// assert_eq!(ne, bitvec![1, 0, 1]);
	/// ```
	fn neg(mut self) -> Self::Output {
		//  An empty vector does nothing.
		//  Negative zero is zero. Without this check, -[0+] becomes[10+1].
		if self.is_empty() || self.not_any() {
			return self;
		}
		self = !self;
		self += BitVec::<C, T>::from_iter(iter::once(true));
		self
	}
}

/// Flips all bits in the vector.
impl<C, T> Not for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Inverts all bits in the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv: BitVec<BigEndian, u32> = BitVec::from(&[0u32] as &[u32]);
	/// let flip = !bv;
	/// assert_eq!(!0u32, flip.as_slice()[0]);
	/// ```
	fn not(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().not();
		self
	}
}

__bitvec_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/** Shifts all bits in the vector to the left – **DOWN AND TOWARDS THE FRONT**.

On fundamentals, the left-shift operator `<<` moves bits away from origin and
towards the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, left-shifting moves bits towards the **minimum**.

In BigEndian order, the effect in memory will be what you expect the `<<`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `>>` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than
left to their old value.

The length of the vector is decreased by the shift amount.

If the shift amount is greater than the length, the vector calls `clear()` and
zeroes its memory. This is *not* an error.
**/
impl<C, T> Shl<usize> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Shifts a `BitVec` to the left, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let ls = bv << 2usize;
	/// assert_eq!("[0111]", &format!("{}", ls));
	/// assert_eq!(0b0111_0000, ls.as_slice()[0]);
	/// assert_eq!(ls.len(), 4);
	/// ```
	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

/** Shifts all bits in the vector to the left – **DOWN AND TOWARDS THE FRONT**.

On fundamentals, the left-shift operator `<<` moves bits away from origin and
towards the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This increases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, left-shifting moves bits towards the **minimum**.

In BigEndian order, the effect in memory will be what you expect the `<<`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `>>` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is decreased by the shift amount.

If the shift amount is greater than the length, the vector calls `clear()` and
zeroes its memory. This is *not* an error.
**/
impl<C, T> ShlAssign<usize> for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Shifts a `BitVec` to the left in place, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![LittleEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv <<= 2;
	/// assert_eq!("[0111]", &format!("{}", bv));
	/// assert_eq!(0b0000_1110, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 4);
	/// ```
	fn shl_assign(&mut self, shamt: usize) {
		let len = self.len();
		if shamt >= len {
			self.set_all(false);
			self.clear();
			return;
		}
		for idx in shamt .. len {
			let val = self[idx];
			self.set(idx.saturating_sub(shamt), val);
		}
		let trunc = len.saturating_sub(shamt);
		for idx in trunc .. len {
			self.set(idx, false);
		}
		self.truncate(trunc);
	}
}

/** Shifts all bits in the vector to the right – **UP AND TOWARDS THE BACK**.

On fundamentals, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, right-shifting moves bits towards the **maximum**.

In BigEndian order, the effect in memory will be what you expect the `>>`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `<<` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is increased by the shift amount.

If the new length of the vector would overflow, a panic occurs. This *is* an
error.
**/
impl<C, T> Shr<usize> for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Shifts a `BitVec` to the right, lengthening it and filling the front
	/// with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let rs = bv >> 2usize;
	/// assert_eq!("[00000111]", &format!("{}", rs));
	/// assert_eq!(0b0000_0111, rs.as_slice()[0]);
	/// assert_eq!(rs.len(), 8);
	/// ```
	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

/** Shifts all bits in the vector to the right – **UP AND TOWARDS THE BACK**.

On fundamentals, the right-shift operator `>>` moves bits towards the origin and
away from the ceiling. This is because we label the bits in a primitive with the
minimum on the right and the maximum on the left, which is big-endian bit order.
This decreases the value of the primitive being shifted.

**THAT IS NOT HOW `BITVEC` WORKS!**

`BitVec` defines its layout with the minimum on the left and the maximum on the
right! Thus, right-shifting moves bits towards the **maximum**.

In BigEndian order, the effect in memory will be what you expect the `>>`
operator to do.

**In LittleEndian order, the effect will be equivalent to using `<<` on the**
**fundamentals in memory!**

# Notes

In order to preserve the effects in memory that this operator traditionally
expects, the bits that are emptied by this operation are zeroed rather than left
to their old value.

The length of the vector is increased by the shift amount.

If the new length of the vector would overflow, a panic occurs. This *is* an
error.
**/
impl<C, T> ShrAssign<usize> for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Shifts a `BitVec` to the right in place, lengthening it and filling the
	/// front with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut bv = bitvec![LittleEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("[000111]", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv >>= 2;
	/// assert_eq!("[00000111]", &format!("{}", bv));
	/// assert_eq!(0b1110_0000, bv.as_slice()[0]);
	/// assert_eq!(bv.len(), 8);
	/// ```
	fn shr_assign(&mut self, shamt: usize) {
		let old_len = self.len();
		for _ in 0 .. shamt {
			self.push(false);
		}
		for idx in (0 .. old_len).rev() {
			let val = self[idx];
			self.set(idx.saturating_add(shamt), val);
		}
		for idx in 0 .. shamt {
			self.set(idx, false);
		}
	}
}

/** Subtracts one `BitVec` from another assuming 2’s-complement encoding.

Subtraction is a more complex operation than addition. The bit-level work is
largely the same, but semantic distinctions must be made. Unlike addition, which
is commutative and tolerant of switching the order of the addends, subtraction
cannot swap the minuend (LHS) and subtrahend (RHS).

Because of the properties of 2’s-complement arithmetic, M - S is equivalent to M
+ (!S + 1). Subtraction therefore bitflips the subtrahend and adds one. This
may, in a degenerate case, cause the subtrahend to increase in length.

Once the subtrahend is stable, the minuend zero-extends its left side in order
to match the length of the subtrahend if needed (this is provided by the `>>`
operator).

When the minuend is stable, the minuend and subtrahend are added together by the
`<BitVec as Add>` implementation. The output will be encoded in 2’s-complement,
so a leading one means that the output is considered negative.

Interpreting the contents of a `BitVec` as an integer is beyond the scope of
this crate.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<C, T> Sub for BitVec<C, T>
where C: Cursor, T: BitStore {
	type Output = Self;

	/// Subtracts one `BitVec` from another.
	///
	/// # Examples
	///
	/// Minuend larger than subtrahend, positive difference.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![1, 0];
	/// let b = bitvec![   1];
	/// let c = a - b;
	/// assert_eq!(bitvec![0, 1], c);
	/// ```
	///
	/// Minuend smaller than subtrahend, negative difference.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![   1];
	/// let b = bitvec![1, 0];
	/// let c = a - b;
	/// assert_eq!(bitvec![1, 1], c);
	/// ```
	///
	/// Subtraction from self is correctly handled.
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 1, 1, 0];
	/// let b = a.clone();
	/// let c = a - b;
	/// assert!(c.not_any(), "{:?}", c);
	/// ```
	fn sub(mut self, subtrahend: Self) -> Self::Output {
		self -= subtrahend;
		self
	}
}

/** Subtracts another `BitVec` from `self`, assuming 2’s-complement encoding.

The minuend is zero-extended, or the subtrahend sign-extended, as needed to
ensure that the vectors are the same width before subtraction occurs.

The `Sub` trait has more documentation on the subtraction process.

Numeric arithmetic is provided on `BitVec` as a convenience. Serious numeric
computation on variable-length integers should use the `num_bigint` crate
instead, which is written specifically for that use case. `BitVec`s are not
intended for arithmetic, and `bitvec` makes no guarantees about sustained
correctness in arithmetic at this time.
**/
impl<C, T> SubAssign for BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Subtracts another `BitVec` from `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let a = bitvec![0, 0, 0, 1];
	/// let b = bitvec![0, 0, 0, 0];
	/// let c = a - b;
	/// assert_eq!(c, bitvec![0, 0, 0, 1]);
	/// ```
	//  Note: in `a - b`, `a` is `self` and the minuend, `b` is the subtrahend
	fn sub_assign(&mut self, mut subtrahend: Self) {
		//  Test for a zero subtrahend. Subtraction of zero is the identity
		//  function, and can exit immediately.
		if subtrahend.not_any() {
			return;
		}
		//  Invert the subtrahend in preparation for addition
		subtrahend = -subtrahend;
		let (llen, rlen) = (self.len(), subtrahend.len());
		//  If the subtrahend is longer than the minuend, 0-extend the minuend.
		if rlen > llen {
			let diff = rlen - llen;
			*self >>= diff;
		}
		else {
			//  If the minuend is longer than the subtrahend, sign-extend the
			//  subtrahend.
			if llen > rlen {
				let diff = llen - rlen;
				let sign = subtrahend[0];
				subtrahend >>= diff;
				subtrahend[.. diff].set_all(sign);
			}
		}
		let old = self.len();
		*self += subtrahend;
		//  If the subtraction emitted a carry, remove it.
		if self.len() > old {
			*self <<= 1;
		}
	}
}

/** State keeper for draining iteration.

# Type Parameters

- `C: Cursor`: The cursor type of the underlying vector.
- `T: 'a + BitStore`: The storage type of the underlying vector.

# Lifetimes

- `'a`: The lifetime of the underlying vector.
**/
pub struct Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Pointer to the `BitVec` being drained.
	bitvec: NonNull<BitVec<C, T>>,
	/// Current remaining range to remove.
	iter: crate::slice::iter::Iter<'a, C, T>,
	/// Index of the original vector tail to preserve.
	tail_start: usize,
	/// Length of the tail.
	tail_len: usize,
}

impl<'a, C, T> Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	/// Fills the drain span with another iterator.
	///
	/// If the stream exhausts before the drain is filled, then the tail
	/// elements move downwards; otherwise, the tail stays put and the drain is
	/// filled.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `stream`: The source of bits to fill into the drain.
	///
	/// # Returns
	///
	/// - `true` if the drain was filled before the `stream` exhausted.
	/// - `false` if the `stream` exhausted early, and the tail was moved down.
	///
	/// # Type Parameters
	///
	/// - `I: Iterator<Item=bool>`: A provider of bits.
	unsafe fn fill<I: Iterator<Item=bool>>(&mut self, stream: &mut I) -> bool {
		let bv = self.bitvec.as_mut();
		let drain_from = bv.len();
		let drain_upto = self.tail_start;

		for n in drain_from .. drain_upto {
			if let Some(bit) = stream.next() {
				bv.push(bit);
			}
			else {
				for (to, from) in (n .. n + self.tail_len).zip(drain_upto ..) {
					bv.swap(from, to);
				}
				self.tail_start = n;
				return false;
			}
		}
		true
	}

	/// Moves the tail span farther back in the vector.
	///
	/// # Parameters
	///
	/// - `&mut self`
	/// - `by`: The amount by which to move the tail span.
	unsafe fn move_tail(&mut self, by: usize) {
		let bv = self.bitvec.as_mut();
		bv.reserve(by);
		let new_tail = self.tail_start + by;
		let old_len = bv.len();
		let new_len = self.tail_start + self.tail_len + by;

		bv.set_len(new_len);
		for n in (0 .. self.tail_len).rev() {
			bv.swap(self.tail_start + n, new_tail + n);
		}
		bv.set_len(old_len);

		self.tail_start = new_tail;
	}
}

impl<'a, C, T> DoubleEndedIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.iter.next_back().copied()
	}
}

impl<'a, C, T> ExactSizeIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> FusedIterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {}

impl<'a, C, T> Iterator for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next().copied()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	fn count(self) -> usize {
		self.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.iter.nth(n).copied()
	}

	fn last(mut self) -> Option<Self::Item> {
		self.iter.next_back().copied()
	}
}

impl<'a, C, T> Drop for Drain<'a, C, T>
where C: Cursor, T: 'a + BitStore {
	fn drop(&mut self) { unsafe {
		let bv: &mut BitVec<C, T> = self.bitvec.as_mut();
		//  Get the start of the drained span.
		let start = bv.len();
		//  Get the start of the remnant span.
		let tail = self.tail_start;
		let tail_len = self.tail_len;
		//  Get the full length of the vector,
		let full_len = tail + tail_len;
		//  And the length of the vector after the drain.
		let end_len = start + tail_len;
		//  Inflate the vector to include the remnant span,
		bv.set_len(full_len);
		//  Swap the remnant span down into the drained span,
		for (from, to) in (tail .. full_len).zip(start .. end_len) {
			bv.swap(from, to);
		}
		//  And deflate the vector to fit.
		bv.set_len(end_len);
	} }
}

/// A consuming iterator for `BitVec`.
#[repr(C)]
pub struct IntoIter<C, T>
where C: Cursor, T: BitStore {
	/// Owning descriptor for the allocation. This is not modified by iteration.
	bitvec: BitVec<C, T>,
	/// Descriptor for the live portion of the vector as iteration proceeds.
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
	/// let bv = bitvec![1, 0];
	/// let mut iter = bv.iter();
	/// assert!(iter.next().unwrap());
	/// assert!(!iter.next().unwrap());
	/// assert!(iter.next().is_none());
	/// ```
	fn next(&mut self) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.next().copied();
		self.region = slice_iter.bitptr();
		out
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
	/// let bv = bitvec![0, 1];
	/// let mut iter = bv.iter();
	/// assert_eq!(iter.size_hint(), (2, Some(2)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (1, Some(1)));
	/// iter.next();
	/// assert_eq!(iter.size_hint(), (0, Some(0)));
	/// ```
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iterator().size_hint()
	}

	/// Counts how many bits are live in the iterator, consuming it.
	///
	/// You are probably looking to use this on a borrowed iterator rather than
	/// an owning iterator. See [`BitSlice`].
	///
	/// # Parameters
	///
	/// - `self`
	///
	/// # Returns
	///
	/// The number of bits in the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bv = bitvec![BigEndian, u8; 0, 1, 0, 1, 0];
	/// assert_eq!(bv.into_iter().count(), 5);
	/// ```
	///
	/// [`BitSlice`]: ../struct.BitSlice.html#method.iter
	fn count(self) -> usize {
		self.bitvec.len()
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
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// let mut iter = bv.into_iter();
	/// assert_eq!(iter.len(), 4);
	/// assert!(iter.nth(3).unwrap());
	/// assert!(iter.nth(0).is_none());
	/// ```
	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let mut slice_iter = self.iterator();
		let out = slice_iter.nth(n).copied();
		self.region = slice_iter.bitptr();
		out
	}

	/// Consumes the iterator, returning only the last bit.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// assert!(bv.into_iter().last().unwrap());
	/// ```
	///
	/// Empty iterators return `None`
	///
	/// ```rust
	/// use bitvec::prelude::*;
	/// assert!(bitvec![].into_iter().last().is_none());
	/// ```
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

/** A splicing iterator for `BitVec`.

This removes a segment from the vector and inserts another bitstream into its
spot. Any bits from the original `BitVec` after the removed segment are kept,
after the inserted bitstream.

Only the removed segment is available for iteration.

# Type Parameters

- `I: Iterator<Item=bool>`: Any bitstream. This will be used to fill the
  removed span.
**/
pub struct Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	drain: Drain<'a, C, T>,
	splice: I,
}

impl<'a, C, T, I> DoubleEndedIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn next_back(&mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, C, T, I> ExactSizeIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {}

impl<'a, C, T, I> FusedIterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {}

//  Forward iteration to the interior drain
impl<'a, C, T, I> Iterator for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	type Item = bool;

	fn next(&mut self) -> Option<Self::Item> {
		//  If the drain produced a bit, then try to pull a bit from the
		//  replacement. If the replacement produced a bit, push it into the
		//  `BitVec` that the drain is managing. This works because the `Drain`
		//  type truncates the `BitVec` to the front of the region being
		//  drained, then tracks the remainder of the memory.
		self.drain.next().map(|bit| {
			if let Some(new_bit) = self.splice.next() {
				unsafe { self.drain.bitvec.as_mut() }.push(new_bit);
			}
			bit
		})
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.drain.size_hint()
	}

	fn count(self) -> usize {
		self.drain.len()
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		self.drain.nth(n)
	}

	fn last(mut self) -> Option<Self::Item> {
		self.drain.next_back()
	}
}

impl<'a, C, T, I> Drop for Splice<'a, C, T, I>
where C: Cursor, T: 'a + BitStore, I: Iterator<Item=bool> {
	fn drop(&mut self) { unsafe {
		if self.drain.tail_len == 0 {
			self.drain.bitvec.as_mut().extend(self.splice.by_ref());
			return;
		}

		//  Fill the drained span from the splice. If this exhausts the splice,
		//  exit. Note that `Drain::fill` runs from the current `BitVec.len`
		//  value, so the fact that `Splice::next` attempts to push onto the
		//  vector is not a problem here.
		if !self.drain.fill(&mut self.splice) {
			return;
		}

		let (lower, _) = self.splice.size_hint();

		//  If the splice still has data, move the tail to make room for it and
		//  fill.
		if lower > 0 {
			self.drain.move_tail(lower);
			if !self.drain.fill(&mut self.splice) {
				return;
			}
		}

		let mut remnant = self.splice.by_ref().collect::<Vec<_>>().into_iter();
		if remnant.len() > 0 {
			self.drain.move_tail(remnant.len());
			self.drain.fill(&mut remnant);
		}
		//  Drain::drop does the rest
	} }
}

mod api;

pub use api::*;
