//! Iterators over `[T]`.

use crate::{
	index::BitIdx,
	mem::BitMemory,
	order::BitOrder,
	ptr::BitPtr,
	slice::{
		proxy::BitMut,
		BitSlice,
		BitSliceIndex,
	},
	store::BitStore,
};

use core::{
	cmp,
	fmt::{
		self,
		Debug,
		Formatter,
	},
	iter::FusedIterator,
	marker::PhantomData,
	mem,
	ptr::NonNull,
};

/** Immutable [`BitSlice`] iterator.

This struct is created by the [`.iter()`] method on [`BitSlice`]s.

# Original

[`slice::Iter`](core::slice::Iter)

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let bits = bits![0, 1];
for bit in bits.iter() {
  # #[cfg(feature = "std")]
  println!("{}", bit);
}
```

[`BitSlice`]: crate::slice::BitSlice
[`.iter()`]: crate::slice::BitSlice::iter
**/
#[repr(C)]
pub struct Iter<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Address of the element with the first live bit.
	base: NonNull<T>,
	/// Address of the element containing the first dead bit.
	///
	/// This address may or may not be dereferencable, but thanks to a rule in
	/// the C++ and LLVM memory models emplaced specifically to allow
	/// double-pointer iteration, the creation of an address one element after
	/// the end of a live region is required to be legial. It is not required to
	/// be equal to a numerically-identical pointer that is the base address of
	/// a separate adjoining region, but the distinction is not important here.
	last: NonNull<T>,
	/// Semantic index of the first live bit.
	head: BitIdx<T::Mem>,
	/// Semantic index of the first dead bit after the last live bit. This may
	/// be in an element beyond the dereferencable region.
	///
	/// This is not a [`BitTail`] because reverse iteration requires a valid
	/// index, and the use of a pointer that may point outside the element
	/// region has a smoother codepath than the use of an index that may be
	/// outside the element.
	///
	/// [`BitTail`]: crate::index::BitTail
	tail: BitIdx<T::Mem>,
	/// `Iter` is semantically equivalent to a [`&BitSlice`].
	///
	/// [`&BitSlice`]: crate::slice::BitSlice
	_ref: PhantomData<&'a BitSlice<O, T>>,
}

/** Mutable [`BitSlice`] iterator.

This struct is created by the [`.iter_mut()`] method on [`BitSlice`]s.

# Original

[`slice::IterMut`](crate::slice::IterMut)

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let bits = bits![mut 0; 2];
for mut bit in bits.iter_mut() {
  *bit = true;
}
assert_eq!(bits, bits![1; 2]);
```

[`BitSlice`]: crate::slice::BitSlice
[`.iter_mut()`]: crate::slice::BitSlice::iter_mut
**/
#[repr(C)]
pub struct IterMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// Address of the element with the first live bit.
	base: NonNull<<T::Alias as BitStore>::Access>,
	/// Address of the element with the first dead bit. See `Iter.last`.
	last: NonNull<<T::Alias as BitStore>::Access>,
	/// Index of the first live bit in `*base`.
	head: BitIdx<<T::Alias as BitStore>::Mem>,
	/// Index of the first dead bit in `*last`. See `Iter.tail`.
	tail: BitIdx<<T::Alias as BitStore>::Mem>,
	/// `IterMut` is semantically an aliasing `&mut BitSlice`.
	_ref: PhantomData<&'a mut BitSlice<O, T::Alias>>,
}

impl<'a, O, T> Iter<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The canonical empty iterator.
	const EMPTY: Self = Self {
		base: NonNull::dangling(),
		last: NonNull::dangling(),
		head: BitIdx::ZERO,
		tail: BitIdx::ZERO,
		_ref: PhantomData,
	};

	/// Views the underlying data as a subslice of the original data.
	///
	/// This has the same lifetime as the original [`BitSlice`], and so the
	/// iterator can continue to be used while this exists.
	///
	/// # Original
	///
	/// [`Iter::as_slice`](core::slice::Iter::as_slice)
	///
	/// # API Differences
	///
	/// As this views a [`BitSlice`], rather than a `[T]` or `[bool]` slice, it
	/// has been renamed.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// # #[cfg(feature = "std")] {
	/// use bitvec::prelude::*;
	///
	/// let bits = bits![0, 0, 1, 1];
	///
	/// // Get the iterator:
	/// let mut iter = bits.iter();
	/// // So if we print what `as_bitslice` returns
	/// // here, we have "[0011]":
	/// println!("{:b}", iter.as_bitslice());
	///
	/// // Next, we move to the second element of the slice:
	/// iter.next();
	/// // Now `as_bitslice` returns "[011]":
	/// println!("{:b}", iter.as_bitslice());
	/// # }
	/// ```
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn as_bitslice(&self) -> &'a BitSlice<O, T> {
		unsafe {
			BitPtr::new_unchecked(self.base.as_ptr(), self.head, self.len())
		}
		.to_bitslice_ref()
	}

	/* Allow the standard-library name to resolve, but instruct the user to
	rename.

	It is important not to use the name `slice` to refer to any `BitSlice`
	regions, and to keep distinct the views of a `BitSlice` from the views of
	the underlying `[T]` storage slice.
	*/
	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `.as_bitslice()` to view the underlying slice"]
	pub fn as_slice(&self) -> &'a BitSlice<O, T> {
		self.as_bitslice()
	}

	/// Removes the bit at the front of the iterator.
	fn pop_front(&mut self) -> <Self as Iterator>::Item {
		let base_raw = self.base.as_ptr() as *const T;
		let out = unsafe { &*base_raw }.get_bit::<O>(self.head);
		let (head, incr) = self.head.next();
		self.set_base(unsafe { base_raw.add(incr as usize) as *mut T });
		self.head = head;

		if out { &true } else { &false }
	}

	/// Removes the bit at the back of the iterator.
	fn pop_back(&mut self) -> <Self as Iterator>::Item {
		let (tail, offset) = self.tail.prev();
		self.set_last(unsafe { self.last.as_ptr().offset(-(offset as isize)) });
		self.tail = tail;
		if unsafe { &*self.last.as_ptr() }.get_bit::<O>(self.tail) {
			&true
		}
		else {
			&false
		}
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn get_base(&self) -> *const T {
		self.base.as_ptr() as *const T
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn get_last(&self) -> *const T {
		self.last.as_ptr() as *const T
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn set_base(&mut self, base: *const T) {
		self.base = unsafe { NonNull::new_unchecked(base as *mut T) }
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn set_last(&mut self, last: *const T) {
		self.last = unsafe { NonNull::new_unchecked(last as *mut T) }
	}
}

impl<'a, O, T> IterMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The canonical empty iterator.
	const EMPTY: Self = Self {
		base: NonNull::dangling(),
		last: NonNull::dangling(),
		head: BitIdx::ZERO,
		tail: BitIdx::ZERO,
		_ref: PhantomData,
	};

	/// Views the underlying data as a subslice of the original data.
	///
	/// To avoid creating `&mut` references that alias, this is forced to
	/// consume the iterator.
	///
	/// # Original
	///
	/// [`IterMut::into_slice`](core::slice::IterMut::into_slice)
	///
	/// # API Differences
	///
	/// As this views a [`BitSlice`], rather than a `[T]` or `[bool]` slice, it
	/// has been renamed.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```rust
	/// # #[cfg(feature = "std")] {
	/// use bitvec::prelude::*;
	///
	/// let bits = bits![mut 0, 1, 0];
	///
	/// {
	///   // Get the iterator:
	///   let mut iter = bits.iter_mut();
	///   // We move to the next element:
	///   iter.next();
	///   // So if we print what `into_bitslice`
	///   // returns here, we have "[10]":
	///   println!("{:b}", iter.into_slice());
	/// }
	///
	/// // Now let’s modify a value of the slice:
	/// {
	///   // First we get back the iterator:
	///   let mut iter = bits.iter_mut();
	///   // We change the value of the first bit of
	///   // the slice returned by the `next` method:
	///   *iter.next().unwrap() = true;
	/// }
	/// // Now bits is "[110]":
	/// println!("{:b}", bits);
	/// # }
	/// ```
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn into_bitslice(self) -> &'a mut BitSlice<O, T::Alias> {
		unsafe {
			BitPtr::new_unchecked(
				self.base.as_ptr()
					as *const <<T as BitStore>::Alias as BitStore>::Access
					as *const <T as BitStore>::Alias,
				self.head,
				self.len(),
			)
		}
		.to_bitslice_mut()
	}

	/* Allow the standard-library name to resolve, but instruct the user to
	rename.

	It is important not to use the name `slice` to refer to any `BitSlice`
	regions, and to keep distinct the views of a `BitSlice` from the views of
	the underlying `[T]` storage slice.
	*/
	#[doc(hidden)]
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Use `.into_bitslice()` to view the underlying slice"]
	pub fn into_slice(self) -> &'a mut BitSlice<O, T::Alias> {
		self.into_bitslice()
	}

	/// Used only for `Debug` printing.
	#[cfg(not(tarpaulin_include))]
	fn as_bitslice(&self) -> &BitSlice<O, T::Alias> {
		unsafe { core::ptr::read(self) }.into_bitslice()
	}

	/// Removes the bit at the front of the iterator.
	fn pop_front(&mut self) -> <Self as Iterator>::Item {
		let out =
			unsafe { BitMut::new_unchecked(self.base.as_ptr(), self.head) };

		let (head, incr) = self.head.next();
		self.set_base(unsafe { self.base.as_ptr().add(incr as usize) });
		self.head = head;

		out
	}

	/// Removes the bit at the back of the iterator.
	fn pop_back(&mut self) -> <Self as Iterator>::Item {
		let (tail, decr) = self.tail.prev();
		self.set_last(unsafe { self.last.as_ptr().sub(decr as usize) });
		self.tail = tail;

		unsafe { BitMut::new_unchecked(self.last.as_ptr(), self.tail) }
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn get_base(&self) -> *mut <T::Alias as BitStore>::Access {
		self.base.as_ptr()
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn get_last(&self) -> *mut <T::Alias as BitStore>::Access {
		self.last.as_ptr()
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn set_base(&mut self, base: *mut <T::Alias as BitStore>::Access) {
		self.base = unsafe { NonNull::new_unchecked(base) }
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn set_last(&mut self, last: *mut <T::Alias as BitStore>::Access) {
		self.last = unsafe { NonNull::new_unchecked(last) }
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Clone for Iter<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn clone(&self) -> Self {
		*self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> AsRef<BitSlice<O, T>> for Iter<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Debug for Iter<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("Iter").field(&self.as_bitslice()).finish()
	}
}

impl<O, T> Copy for Iter<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Debug for IterMut<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_tuple("IterMut")
			.field(&self.as_bitslice())
			.finish()
	}
}

impl<'a, O, T> IntoIterator for &'a BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = Iter<'a, O, T>;
	type Item = <Self::IntoIter as Iterator>::Item;

	fn into_iter(self) -> Self::IntoIter {
		let (addr, head, bits) = self.bitptr().raw_parts();
		let addr = addr.to_mut();
		let base = unsafe { NonNull::new_unchecked(addr) };

		let (elts, tail) = head.offset(bits as isize);
		let last = unsafe { NonNull::new_unchecked(addr.offset(elts)) };

		Self::IntoIter {
			base,
			last,
			head,
			tail,
			_ref: PhantomData,
		}
	}
}

impl<'a, O, T> IntoIterator for &'a mut BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = IterMut<'a, O, T>;
	type Item = <Self::IntoIter as Iterator>::Item;

	fn into_iter(self) -> Self::IntoIter {
		let (addr, head, bits) = self.alias().bitptr().raw_parts();

		let addr = addr.to_access()
			as *mut <<T as BitStore>::Alias as BitStore>::Access;
		let base = unsafe { NonNull::new_unchecked(addr) };

		let (elts, tail) = head.offset(bits as isize);
		let last = unsafe { NonNull::new_unchecked(addr.offset(elts)) };

		Self::IntoIter {
			base,
			last,
			head,
			tail,
			_ref: PhantomData,
		}
	}
}

/// `Iter` and `IterMut` have very nearly the same implementation text.
macro_rules! iter {
	($($t:ident => $i:ty),+ $(,)?) => { $(
		impl<'a, O, T> $t<'a, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			/// Tests whether the iterator is *any* empty iterator.
			fn inherent_is_empty(&self) -> bool {
				self.base == self.last && self.head == self.tail
			}
		}

		impl<'a, O, T> Iterator for $t<'a, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			type Item = $i;

			#[inline]
			fn next(&mut self) -> Option<Self::Item> {
				if self.inherent_is_empty() {
					return None;
				}
				Some(self.pop_front())
			}

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				let len = self.len();
				(len, Some(len))
			}

			#[inline]
			fn count(self) -> usize {
				self.len()
			}

			#[inline]
			fn nth(&mut self, n: usize) -> Option<Self::Item> {
				if n >= self.len() {
					*self = Self::EMPTY;
					return None;
				}

				//  Move the head cursors up by `n` bits before producing a bit.
				let (elts, head) = self.head.offset(n as isize);
				self.set_base(unsafe{self.get_base().offset(elts)});
				self.head = head;
				Some(self.pop_front())
			}

			#[inline]
			fn last(mut self) -> Option<Self::Item> {
				self.next_back()
			}
		}

		impl<'a, O, T> DoubleEndedIterator for $t <'a, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			#[inline]
			fn next_back(&mut self) -> Option<Self::Item> {
				if self.inherent_is_empty() {
					return None;
				}
				Some(self.pop_back())
			}

			#[inline]
			fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
				if n >= self.len() {
					*self = Self::EMPTY;
					return None;
				}

				//  Move the tail cursors down by `n` bits before producing a
				//  bit.
				let (elts, tail) = self.tail.offset(-(n as isize));
				self.set_last(unsafe{self.get_last().offset(elts)});
				self.tail = tail;
				Some(self.pop_back())
			}
		}

		impl<O, T> ExactSizeIterator for $t <'_, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			fn len(&self) -> usize {
				let (base, last) =
					(self.get_base() as usize, self.get_last() as usize);
				/* Get the total number of bits in the element range
				`self.base .. self.last`. Wrapping arithmetic is used because
				`last` is known to never be less than base, so we always want a
				bare `sub` instruction without any checks. We also know that the
				difference between the two addresses can support a `shl`
				instruction without overflow.
				*/
				last.wrapping_sub(base)
					//  Pointers are always byte-stepped, not element-stepped.
					.wrapping_shl(<u8 as BitMemory>::INDX as u32)
					//  Now, add the live bits before `self.tail` in `*last`,
					.wrapping_add(self.tail.value() as usize)
					//  And remove the dead bits before `self.head` in `*base`.
					.wrapping_sub(self.head.value() as usize)
			}
		}

		impl<O, T> FusedIterator for $t <'_, O, T>
		where
			O: BitOrder,
			T: BitStore
		{
		}

		unsafe impl<O, T> Send for $t <'_, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
		}

		unsafe impl<O, T> Sync for $t <'_, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
		}
	)+ };
}

iter!(
	Iter => <usize as BitSliceIndex<'a, O, T>>::Immut,
	IterMut => <usize as BitSliceIndex<'a, O, T::Alias>>::Mut,
);

/// Creates a full iterator set from only the base functions needed to build it.
macro_rules! group {
	(
		//  The type for the iteration set. This must be an immutable group.
		$iter:ident => $item:ty $( where $alias:ident )? {
			//  The eponymous functions from the iterator traits.
			$next:item
			$nth:item
			$next_back:item
			$nth_back:item
			$len:item
		}
	) => {
		//  Immutable iterator implementation
		impl<'a, O, T> Iterator for $iter <'a, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			type Item = $item;

			#[inline]
			$next

			#[inline]
			$nth

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				let len = self.len();
				(len, Some(len))
			}

			#[inline]
			fn count(self) -> usize {
				self.len()
			}

			#[inline]
			fn last(mut self) -> Option<Self::Item> {
				self.next_back()
			}
		}

		impl<'a, O, T> DoubleEndedIterator for $iter <'a, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			#[inline]
			$next_back

			#[inline]
			$nth_back
		}

		impl<O, T> ExactSizeIterator for $iter <'_, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			#[inline]
			$len
		}

		impl<O, T> FusedIterator for $iter <'_, O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
		}
	}
}

/** An iterator over overlapping subslices of length `size`.

This struct is created by the [`.windows()`] method on [`BitSlice`]s.

# Original

[`slice::Windows`](core::slice::Windows)

[`BitSlice`]: crate::slice::BitSlice
[`.windows()`]: crate::slice::BitSlice::windows
**/
#[derive(Clone, Debug)]
pub struct Windows<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being windowed.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// The width of the produced windows.
	width: usize,
}

group!(Windows => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		if self.width > self.slice.len() {
			self.slice = Default::default();
			return None;
		}
		unsafe {
			let out = self.slice.get_unchecked(.. self.width);
			self.slice = self.slice.get_unchecked(1 ..);
			Some(out)
		}
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = self.width.overflowing_add(n);
		if end > self.slice.len() || ovf {
			self.slice = Default::default();
			return None;
		}
		unsafe {
			let out = self.slice.get_unchecked(n .. end);
			self.slice = self.slice.get_unchecked(n + 1 ..);
			Some(out)
		}
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.slice.len();
		if self.width > len {
			self.slice = Default::default();
			return None;
		}
		unsafe {
			let out = self.slice.get_unchecked(len - self.width ..);
			self.slice = self.slice.get_unchecked(.. len - 1);
			Some(out)
		}
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let (end, ovf) = self.slice.len().overflowing_sub(n);
		if end < self.width || ovf {
			self.slice = Default::default();
			return None;
		}
		unsafe {
			let out = self.slice.get_unchecked(end - self.width .. end);
			self.slice = self.slice.get_unchecked(.. end - 1);
			Some(out)
		}
	}

	fn len(&self) -> usize {
		let len = self.slice.len();
		if self.width > len {
			return 0;
		}
		len - self.width + 1
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) chunks (`chunk_size`
bits at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`.chunks()`] method on [`BitSlice`]s.

# Original

[`slice::Chunks`](core::slice::Chunks)

[`BitSlice`]: crate::slice::BitSlice
[`.chunks()`]: crate::slice::BitSlice::chunks
**/
#[derive(Clone, Debug)]
pub struct Chunks<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	width: usize,
}

group!(Chunks => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		let len = self.slice.len();
		if len == 0 {
			return None;
		}
		let mid = cmp::min(len, self.width);
		let (out, rest) = unsafe { self.slice.split_at_unchecked(mid) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.slice.len();
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= len || ovf {
			self.slice = Default::default();
			return None;
		}
		let (out, rest) = unsafe {
			self.slice
				//  Discard the skipped front chunks,
				.get_unchecked(start ..)
				//  then split at the chunk width, or remnant length.
				.split_at_unchecked(cmp::min(len, self.width))
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		match self.slice.len() {
			0 => None,
			len => {
				//  Determine if the back chunk is a remnant or a whole chunk.
				let rem = len % self.width;
				let size = if rem == 0 { self.width } else { rem };
				let (rest, out) =
					unsafe { self.slice.split_at_unchecked(len - size) };
				self.slice = rest;
				Some(out)
			},
		}
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		if n >= len {
			self.slice = Default::default();
			return None;
		}
		let start = (len - 1 - n) * self.width;
		let width = cmp::min(start + self.width, self.slice.len());
		let (rest, out) = unsafe {
			self.slice
				//  Truncate to the end of the returned chunk,
				.get_unchecked(.. start + width)
				//  then split at the start of the returned chunk.
				.split_at_unchecked(start)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		match self.slice.len() {
			0 => 0,
			len => {
				//  an explicit `div_mod` would be nice here
				let (n, r) = (len / self.width, len % self.width);
				n + (r > 0) as usize
			},
		}
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) mutable chunks
(`chunk_size` bits at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`.chunks_mut()`] method on [`BitSlice`]s.

# Original

[`slice::ChunksMut`](core::slice::ChunksMut)

# API Differences

All slices yielded from this iterator are marked as aliased.

[`BitSlice`]: crate::slice::BitSlice
[`.chunks_mut()`]: crate::slice::BitSlice::chunks_mut
**/
#[derive(Debug)]
pub struct ChunksMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a mut BitSlice<O, T::Alias>,
	/// The width of the produced chunks.
	width: usize,
}

group!(ChunksMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		if len == 0 {
			return None;
		}
		let mid = cmp::min(len, self.width);
		let (out, rest) = unsafe { slice.split_at_unchecked_mut_noalias(mid) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= len || ovf {
			return None;
		}
		let (out, rest) = unsafe {
			slice
				//  Discard the skipped front chunks,
				.get_unchecked_mut(start ..)
				//  then split at the chunk width, or remnant length.
				.split_at_unchecked_mut_noalias(cmp::min(len, self.width))
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		match slice.len() {
			0 => None,
			len => {
				//  Determine if the back chunk is a remnant or a whole chunk.
				let rem = len % self.width;
				let size = if rem == 0 { self.width } else { rem };
				let (rest, out) =
					unsafe { slice.split_at_unchecked_mut_noalias(len - size) };
				self.slice = rest;
				Some(out)
			},
		}
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		let slice = mem::take(&mut self.slice);
		if n >= len {
			return None;
		}
		let start = (len - 1 - n) * self.width;
		let width = cmp::min(start + self.width, slice.len());
		let (rest, out) = unsafe {
			slice
				//  Truncate to the end of the returned chunk,
				.get_unchecked_mut(.. start + width)
				//  then split at the start of the returned chunk.
				.split_at_unchecked_mut_noalias(start)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		match self.slice.len() {
			0 => 0,
			len => {
				//  an explicit `div_mod` would be nice here
				let (n, r) = (len / self.width, len % self.width);
				n + (r > 0) as usize
			},
		}
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) chunks (`chunk_size`
bits at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`chunk_size-1` bits will be ommitted but can be retrieved from the
[`.remainder()`] function from the iterator.

This struct is created by the [`.chunks_exact()`] method on [`BitSlice`]s.

# Original

[`slice::ChunksExact`](core::slice::ChunksExact)

[`BitSlice`]: crate::slice::BitSlice
[`.chunks_exact()`]: crate::slice::BitSlice::chunks_exact
[`.remainder()`]: Self::remainder
**/
#[derive(Clone, Debug)]
pub struct ChunksExact<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// Any remnant of the chunked [`BitSlice`] not divisible by `width`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	extra: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	width: usize,
}

impl<'a, O, T> ChunksExact<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	pub(super) fn new(slice: &'a BitSlice<O, T>, width: usize) -> Self {
		let len = slice.len();
		let rem = len % width;
		let (slice, extra) = unsafe { slice.split_at_unchecked(len - rem) };
		Self {
			slice,
			extra,
			width,
		}
	}

	/// Returns the remainder of the original [`BitSlice`] that is not going to
	/// be returned by the iterator. The returned `BitSlice` has at most
	/// `chunk_size-1` bits.
	///
	/// # Original
	///
	/// [`slice::ChunksExact::remainder`](core::slice::ChunksExact::remainder)
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	pub fn remainder(&self) -> &'a BitSlice<O, T> {
		self.extra
	}
}

group!(ChunksExact => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		if self.slice.len() < self.width {
			return None;
		}
		let (out, rest) = unsafe { self.slice.split_at_unchecked(self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let (start, ovf) = n.overflowing_mul(self.width);
		if start + self.width >= self.slice.len() || ovf {
			self.slice = Default::default();
			return None;
		}
		let (out, rest) = unsafe {
			self.slice
				.get_unchecked(start ..)
				.split_at_unchecked(self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let len = self.slice.len();
		if len < self.width {
			return None;
		}
		let (rest, out) =
			unsafe { self.slice.split_at_unchecked(len - self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		if n >= len {
			self.slice = Default::default();
			return None;
		}
		let end = (len - n) * self.width;
		let (rest, out) = unsafe {
			self.slice
				.get_unchecked(.. end)
				.split_at_unchecked(end - self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		self.slice.len() / self.width
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) mutable chunks
(`chunk_size` bits at a time), starting at the beginning of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`chunk_size-1` bits will be omitted but can be retrieved from the
[`.into_remainder()`] function from the iterator.

This struct is created by the [`.chunks_exact_mut()`] method on [`BitSlice`]s.

# Original

[`slice::ChunksExactMut`](core::slice::ChunksExactMut)

# API Differences

All slices yielded from this iterator are marked as aliased.

[`BitSlice`]: crate::slice::BitSlice
[`.chunks_exact_mut()`]: crate::slice::BitSlice::chunks_exact_mut
[`.into_remainder()`]: Self::into_remainder
**/
#[derive(Debug)]
pub struct ChunksExactMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a mut BitSlice<O, T::Alias>,
	/// Any remnant of the chunked [`BitSlice`] not divisible by `width`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	extra: &'a mut BitSlice<O, T::Alias>,
	/// The width of the produced chunks.
	width: usize,
}

impl<'a, O, T> ChunksExactMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	pub(super) fn new(slice: &'a mut BitSlice<O, T>, width: usize) -> Self {
		let len = slice.len();
		let rem = len % width;
		let (slice, extra) = unsafe { slice.split_at_unchecked_mut(len - rem) };
		Self {
			slice,
			extra,
			width,
		}
	}

	/// Returns the remainder of the original [`BitSlice`] that is not going to
	/// be returned by the iterator. The returned `BitSlice` has at most
	/// `chunk_size-1` bits.
	///
	/// # Original
	///
	/// [`slice::ChunksExactMut::into_remainder`][orig]
	///
	/// # API Differences
	///
	/// The remainder slice, as with all slices yielded from this iterator, is
	/// marked as aliased.
	///
	/// [orig]: core::slice::ChunksExactMut::into_remainder
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn into_remainder(self) -> &'a mut BitSlice<O, T::Alias> {
		self.extra
	}
}

group!(ChunksExactMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		if slice.len() < self.width {
			return None;
		}
		let (out, rest) =
			unsafe { slice.split_at_unchecked_mut_noalias(self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let (start, ovf) = n.overflowing_mul(self.width);
		if start + self.width >= slice.len() || ovf {
			return None;
		}
		let (out, rest) = unsafe {
			slice.get_unchecked_mut(start ..)
				.split_at_unchecked_mut_noalias(self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		if len < self.width {
			return None;
		}
		let (rest, out) =
			unsafe { slice.split_at_unchecked_mut_noalias(len - self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		let slice = mem::take(&mut self.slice);
		if n >= len {
			return None;
		}
		let end = (len - n) * self.width;
		let (rest, out) = unsafe {
			slice.get_unchecked_mut(.. end)
				.split_at_unchecked_mut_noalias(end - self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		self.slice.len() / self.width
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) chunks (`chunk_size`
bits at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last
slice of the iteration will be the remainder.

This struct is created by the [`.rchunks()`] method on [`BitSlice`]s.

# Original

[`slice::RChunks`](core::slice::RChunks)

[`BitSlice`]: crate::slice::BitSlice
[`.rchunks()`]: crate::slice::BitSlice::rchunks
**/
#[derive(Clone, Debug)]
pub struct RChunks<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	width: usize,
}

group!(RChunks => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		let len = self.slice.len();
		if len == 0 {
			return None;
		}
		let mid = len - cmp::min(len, self.width);
		let (rest, out) = unsafe { self.slice.split_at_unchecked(mid) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.slice.len();
		let (num, ovf) = n.overflowing_mul(self.width);
		if num >= len || ovf {
			self.slice = Default::default();
			return None;
		}
		let end = len - num;
		//  Find the partition between `[.. retain]` and `[return ..][..w]`
		let mid = end.saturating_sub(self.width);
		let (rest, out) = unsafe {
			self.slice
				.get_unchecked(.. end)
				.split_at_unchecked(mid)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		match self.slice.len() {
			0 => None,
			n => {
				let rem = n % self.width;
				let len = if rem == 0 { self.width } else { rem };
				let (out, rest) = unsafe { self.slice.split_at_unchecked(len) };
				self.slice = rest;
				Some(out)
			},
		}
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		if n >= len {
			self.slice = Default::default();
			return None;
		}
		/* Taking from the back of a reverse iterator means taking from the
		front of the slice.

		`len` gives us the total number of subslices remaining. In order to find
		the partition point, we need to subtract `n - 1` full subslices from
		that count (because the back slice of the iteration might not be full),
		compute their bit width, and offset *that* from the end of the memory
		region. This gives us the zero-based index of the partition point
		between what is returned and what is retained.

		The `part ..` section of the slice is retained, and the very end of the
		`.. part` section is returned. The head section is split at no less than
		`self.width` bits below the end marker (this could be the partial
		section, so a wrapping subtraction cannot be used), and `.. start` is
		discarded.

		Source:
		https://doc.rust-lang.org/1.43.0/src/core/slice/mod.rs.html#5141-5156
		*/
		let from_end = (len - 1 - n) * self.width;
		let end = self.slice.len() - from_end;
		let start = end.saturating_sub(self.width);
		let (out, rest) = unsafe { self.slice.split_at_unchecked(end) };
		self.slice = rest;
		Some(unsafe { out.get_unchecked(start ..) })
	}

	fn len(&self) -> usize {
		match self.slice.len() {
			0 => 0,
			len => {
				let (n, r) = (len / self.width, len % self.width);
				n + (r > 0) as usize
			},
		}
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) mutable chunks
(`chunk_size` bits at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last slice of
the iteration will be the remainder.

This struct is created by the [`.rchunks_mut()`] method on [`BitSlice`]s.

# Original

[`slice::RChunksMut`](core::slice::RChunksMut)

# API Differences

All slices yielded from this iterator are marked as aliased.

[`BitSlice`]: crate::slice::BitSlice
[`.rchunks_mut()`]: crate::slice::BitSlice::rchunks_mut
**/
#[derive(Debug)]
pub struct RChunksMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a mut BitSlice<O, T::Alias>,
	/// The width of the produced chunks.
	width: usize,
}

group!(RChunksMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		if len == 0 {
			return None;
		}
		let mid = len - cmp::min(len, self.width);
		let (rest, out) = unsafe { slice.split_at_unchecked_mut_noalias(mid) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		let (num, ovf) = n.overflowing_mul(self.width);
		if num >= len || ovf {
			return None;
		}
		let end = len - num;
		//  Find the partition between `[.. retain]` and `[return ..][..w]`
		let mid = end.saturating_sub(self.width);
		let (rest, out) = unsafe {
			slice.get_unchecked_mut(.. end)
				.split_at_unchecked_mut_noalias(mid)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		match slice.len() {
			0 => None,
			n => {
				let rem = n % self.width;
				let len = if rem == 0 { self.width } else { rem };
				let (out, rest) =
					unsafe { slice.split_at_unchecked_mut_noalias(len) };
				self.slice = rest;
				Some(out)
			},
		}
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.len();
		let slice = mem::take(&mut self.slice);
		if n >= len {
			return None;
		}
		let from_end = (len - 1 - n) * self.width;
		let end = slice.len() - from_end;
		let start = end.saturating_sub(self.width);
		let (out, rest) = unsafe { slice.split_at_unchecked_mut_noalias(end) };
		self.slice = rest;
		Some(unsafe { out.get_unchecked_mut(start ..) })
	}

	fn len(&self) -> usize {
		match self.slice.len() {
			0 => 0,
			len => {
				let (n, r) = (len / self.width, len % self.width);
				n + (r > 0) as usize
			},
		}
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) chunks (`chunk_size`
bits at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`chunk_size-1` bits will be omitted but can be retrieved from the
[`.remainder()`] function from the iterator.

This struct is created by the [`.rchunks_exact()`] method on [`BitSlice`]s.

# Original

[`slice::RChunksExact`](core::slice::RChunksExact)

[`BitSlice`]: crate::slice::BitSlice
[`.rchunks_exact()`]: crate::slice::BitSlice::rchunks_exact
[`.remainder()`]: Self::remainder
**/
#[derive(Clone, Debug)]
pub struct RChunksExact<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// Any remnant of the chunked [`BitSlice`] not divisible by `width`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	extra: &'a BitSlice<O, T>,
	/// The width of the produced chunks.
	width: usize,
}

impl<'a, O, T> RChunksExact<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	pub(super) fn new(slice: &'a BitSlice<O, T>, width: usize) -> Self {
		let (extra, slice) =
			unsafe { slice.split_at_unchecked(slice.len() % width) };
		Self {
			slice,
			extra,
			width,
		}
	}

	/// Returns the remainder of the original [`BitSlice`] that is not going to
	/// be returned by the iterator. The returned `BitSlice` has at most
	/// `chunk_size-1` bits.
	///
	/// # Original
	///
	/// [`slice::RChunksExact::remainder`](core::slice::RChunksExact::remainder)
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn remainder(&self) -> &'a BitSlice<O, T> {
		self.extra
	}
}

group!(RChunksExact => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		let len = self.slice.len();
		if len < self.width {
			return None;
		}
		let (rest, out) =
			unsafe { self.slice.split_at_unchecked(len - self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.slice.len();
		let (split, ovf) = n.overflowing_mul(self.width);
		if split >= len || ovf {
			self.slice = Default::default();
			return None;
		}
		let end = len - split;
		let (rest, out) = unsafe {
			self.slice
				.get_unchecked(.. end)
				.split_at_unchecked(end - self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		if self.slice.len() < self.width {
			return None;
		}
		let (out, rest) = unsafe { self.slice.split_at_unchecked(self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let len = self.slice.len();
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= len || ovf {
			self.slice = Default::default();
			return None;
		}
		//  At this point, `start` is at least `self.width` less than `len`.
		let (out, rest) = unsafe {
			self.slice.get_unchecked(start ..).split_at_unchecked(self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		self.slice.len() / self.width
	}
});

/** An iterator over a [`BitSlice`] in (non-overlapping) mutable chunks
(`chunk_size` bits at a time), starting at the end of the slice.

When the slice length is not evenly divided by the chunk size, the last up to
`chunk_size-1` bits will be omitted but can be retrieved from the
[`.into_remainder()`] function from the iterator.

This struct is created by the [`.rchunks_exact_mut()`] method on [`BitSlice`]s.

# Original

[`slice::RChunksExactMut`](core::slice::RChunksExactMut)

# API Differences

All slices yielded from this iterator are marked as aliased.

[`BitSlice`]: crate::slice::BitSlice
[`.into_remainder()`]: Self::into_remainder
[`.rchunks_exact_mut()`]: crate::slice::BitSlice::rchunks_exact_mut
**/
#[derive(Debug)]
pub struct RChunksExactMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The [`BitSlice`] being chunked.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a mut BitSlice<O, T::Alias>,
	/// Any remnant of the chunked [`BitSlice`] not divisible by `width`.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	extra: &'a mut BitSlice<O, T::Alias>,
	/// The width of the produced chunks.
	width: usize,
}

impl<'a, O, T> RChunksExactMut<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	pub(super) fn new(slice: &'a mut BitSlice<O, T>, width: usize) -> Self {
		let (extra, slice) =
			unsafe { slice.split_at_unchecked_mut(slice.len() % width) };
		Self {
			slice,
			extra,
			width,
		}
	}

	/// Returns the remainder of the original [`BitSlice`] that is not going to
	/// be returned by the iterator. The returned `BitSlice` has at most
	/// `chunk_size-1` bits.
	///
	/// # Original
	///
	/// [`slice::RChunksExactMut::into_remainder`][orig]
	///
	/// # API Differences
	///
	/// The remainder slice, as with all slices yielded from this iterator, is
	/// marked as aliased.
	///
	/// [orig]: core::slice::RChunksExactMut::into_remainder
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline]
	pub fn into_remainder(self) -> &'a mut BitSlice<O, T::Alias> {
		self.extra
	}
}

group!(RChunksExactMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		if len < self.width {
			return None;
		}
		let (rest, out) =
			unsafe { slice.split_at_unchecked_mut_noalias(len - self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		let (split, ovf) = n.overflowing_mul(self.width);
		if split >= len || ovf {
			return None;
		}
		let end = len - split;
		let (rest, out) = unsafe {
			slice.get_unchecked_mut(.. end)
				.split_at_unchecked_mut_noalias(end - self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		if slice.len() < self.width {
			return None;
		}
		let (out, rest) =
			unsafe { slice.split_at_unchecked_mut_noalias(self.width) };
		self.slice = rest;
		Some(out)
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		let slice = mem::take(&mut self.slice);
		let len = slice.len();
		let (start, ovf) = n.overflowing_mul(self.width);
		if start >= len || ovf {
			return None;
		}
		//  At this point, `start` is at least `self.width` less than `len`.
		let (out, rest) = unsafe {
			slice.get_unchecked_mut(start ..)
				.split_at_unchecked_mut_noalias(self.width)
		};
		self.slice = rest;
		Some(out)
	}

	fn len(&self) -> usize {
		self.slice.len() / self.width
	}
});

macro_rules! new_group {
	($($t:ident $($m:ident)? $( . $a:ident ())?),+ $(,)?) => { $(
		impl<'a, O, T> $t <'a, O, T>
		where
			O: BitOrder,
			T: BitStore
		{
			#[inline(always)]
			#[allow(clippy::redundant_field_names)]
			pub(super) fn new(
				slice: &'a $($m)? BitSlice<O, T>,
				width: usize,
			) -> Self {
				Self { slice: slice $( . $a () )?, width }
			}
		}
	)+ };
}

new_group!(
	Windows,
	Chunks,
	ChunksMut mut .alias_mut(),
	RChunks,
	RChunksMut mut .alias_mut(),
);

macro_rules! split {
	($iter:ident => $item:ty $( where $alias:ident )? {
		$next:item
		$next_back:item
	}) => {
		impl<'a, O, T, P> $iter <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			#[inline]
			pub(super) fn new(slice: $item, pred: P) -> Self {
				Self {
					slice,
					pred,
					done: false,
				}
			}
		}

		impl<O, T, P> Debug for $iter <'_, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				fmt.debug_struct(stringify!($iter))
					.field("slice", &self.slice)
					.field("done", &self.done)
					.finish()
			}
		}

		impl<'a, O, T, P> Iterator for $iter <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			type Item = $item;

			#[inline]
			$next

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				if self.done {
					(0, Some(0))
				}
				else {
					(1, Some(self.slice.len() + 1))
				}
			}
		}

		impl<'a, O, T, P> DoubleEndedIterator for $iter <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			#[inline]
			$next_back
		}

		impl<'a, O, T, P> core::iter::FusedIterator for $iter <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
		}

		impl<'a, O, T, P> SplitIter for $iter <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			#[inline]
			fn finish(&mut self) -> Option<Self::Item> {
				if self.done {
					None
				}
				else {
					self.done = true;
					Some(mem::take(&mut self.slice))
				}
			}
		}
	};
}

/** An iterator over subslices separated by bits that match a predicate
function.

This struct is created by the [`.split()`] method on [`BitSlice`]s.

# Original

[`slice::Split`](core::slice::Split)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`.split()`]: crate::slice::BitSlice::split
**/
#[derive(Clone)]
pub struct Split<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// The function used to test whether a split should occur.
	pred: P,
	/// Whether the split is finished.
	done: bool,
}

split!(Split => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		if self.done {
			return None;
		}
		match self.slice
			.iter()
			.enumerate()
			.position(|(idx, bit)| (self.pred)(idx, bit))
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let out = self.slice.get_unchecked(.. idx);
				self.slice = self.slice.get_unchecked(idx + 1 ..);
				Some(out)
			},
		}
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		if self.done {
			return None;
		}
		match self.slice
			.iter()
			.enumerate()
			.rposition(|(idx, bit)| (self.pred)(idx, bit))
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let out = self.slice.get_unchecked(idx + 1 ..);
				self.slice = self.slice.get_unchecked(.. idx);
				Some(out)
			},
		}
	}
});

/** An iterator over the mutable subslices which are separated by bits that
match `pred`.

This struct is created by the [`.split_mut()`] method on [`BitSlice`]s.

# Original

[`slice::SplitMut`](core::slice::SplitMut)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`.split_mut()`]: crate::slice::BitSlice::split_mut
**/
pub struct SplitMut<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	slice: &'a mut BitSlice<O, T::Alias>,
	pred: P,
	done: bool,
}

split!(SplitMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		if self.done {
			return None;
		}
		let idx_opt = {
			let pred = &mut self.pred;
			self.slice
				.iter()
				.enumerate()
				.position(|(idx, bit)| (pred)(idx, bit))
		};
		match idx_opt
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let slice = mem::take(&mut self.slice);
				let (out, rest) = slice.split_at_unchecked_mut_noalias(idx);
				self.slice = rest.get_unchecked_mut(1 ..);
				Some(out)
			},
		}
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		if self.done {
			return None;
		}
		let idx_opt = {
			let pred = &mut self.pred;
			self.slice
				.iter()
				.enumerate()
				.rposition(|(idx, bit)| (pred)(idx, bit))
		};
		match idx_opt
		{
			None => self.finish(),
			Some(idx) => unsafe {
				let slice = mem::take(&mut self.slice);
				let (rest, out) = slice.split_at_unchecked_mut_noalias(idx);
				self.slice = rest;
				Some(out.get_unchecked_mut(1 ..))
			},
		}
	}
});

/** An iterator over subslices separated by bits that match a predicate
function, starting from the end of the [`BitSlice`].

This struct is created by the [`.rsplit()`] method on [`BitSlice`]s.

# Original

[`slice::RSplit`](core::slice::RSplit)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`.rsplit()`]: crate::slice::BitSlice::rsplit
**/
#[derive(Clone)]
pub struct RSplit<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a BitSlice<O, T>,
	/// The function used to test whether a split should occur.
	pred: P,
	/// Whether the split is finished.
	done: bool,
}

split!(RSplit => &'a BitSlice<O, T> {
	fn next(&mut self) -> Option<Self::Item> {
		let mut split = Split::<'a, O, T, &mut P> {
			slice: mem::take(&mut self.slice),
			pred: &mut self.pred,
			done: self.done,
		};
		let out = split.next_back();
		self.slice = mem::take(&mut split.slice);
		self.done = split.done;
		out
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let mut split = Split::<'a, O, T, &mut P> {
			slice: mem::take(&mut self.slice),
			pred: &mut self.pred,
			done: self.done,
		};
		let out = split.next();
		self.slice = mem::take(&mut split.slice);
		self.done = split.done;
		out
	}
});

/** An iterator over subslices separated by bits that match a predicate
function, starting from the end of the [`BitSlice`].

This struct is created by the [`.rsplit_mut()`] method on [`BitSlice`]s.

# Original

[`slice::RSplitMut`](core::slice::RSplitMut)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`.rsplit_mut()`]: crate::slice::BitSlice::rsplit_mut
**/
pub struct RSplitMut<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	slice: &'a mut BitSlice<O, T::Alias>,
	/// The function used to test whether a split should occur.
	pred: P,
	/// Whether the split is finished.
	done: bool,
}

split!(RSplitMut => &'a mut BitSlice<O, T::Alias> {
	fn next(&mut self) -> Option<Self::Item> {
		let mut split = SplitMut::<'a, O, T, &mut P> {
			slice: mem::take(&mut self.slice),
			pred: &mut self.pred,
			done: self.done,
		};
		let out = split.next_back();
		self.slice = mem::take(&mut split.slice);
		self.done = split.done;
		out
	}

	fn next_back(&mut self) -> Option<Self::Item> {
		let mut split = SplitMut::<'a, O, T, &mut P> {
			slice: mem::take(&mut self.slice),
			pred: &mut self.pred,
			done: self.done,
		};
		let out = split.next();
		self.slice = mem::take(&mut split.slice);
		self.done = split.done;
		out
	}
});

/// An internal abstraction over the splitting iterators, so that `splitn`,
/// `splitn_mut`, etc, can be implemented once.
#[doc(hidden)]
trait SplitIter: DoubleEndedIterator {
	/// Marks the underlying iterator as complete, extracting the remaining
	/// portion of the slice.
	fn finish(&mut self) -> Option<Self::Item>;
}

/** An iterator over subslices separated by bits that match a predicate
function, limited to a given number of splits.

This struct is created by the [`.splitn()`] method on [`BitSlice`]s.

# Original

[`slice::SplitN`](core::slice::SplitN)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`.splitn()`]: crate::slice::BitSlice::splitn
**/
pub struct SplitN<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	inner: Split<'a, O, T, P>,
	/// The number of splits remaining.
	count: usize,
}

/** An iterator over subslices separated by bits that match a predicate
function, limited to a given number of splits.

This struct is created by the [`splitn_mut`] method on [`BitSlice`]s.

# Original

[`slice::SplitNMut`](core::slice::SplitNMut)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`splitn_mut`]: crate::slice::BitSlice::splitn_mut
**/
pub struct SplitNMut<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	inner: SplitMut<'a, O, T, P>,
	/// The number of splits remaining.
	count: usize,
}

/** An iterator over subslices separated by bits that match a predicate
function, limited to a given number of splits, starting from the end of the
[`BitSlice`].

This struct is created by the [`rsplitn`] method on [`BitSlice`]s.

# Original

[`slice::RSplitN`](core::slice::RSplitN)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`rsplitn`]: crate::slice::BitSlice::rsplitn
**/
pub struct RSplitN<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	inner: RSplit<'a, O, T, P>,
	/// The number of splits remaining.
	count: usize,
}

/** An iterator over subslices separated by bits that match a predicate
function, limited to a given number of splits, starting from the end of the
[`BitSlice`].

This struct is created by the [`rsplitn_mut`] method on [`BitSlice`]s.

# Original

[`slice::RSplitNMut`](core::slice::RSplitNMut)

# API Differences

In order to allow more than one bit of information for the split decision, the
predicate receives the index of each bit, as well as its value.

[`BitSlice`]: crate::slice::BitSlice
[`rsplitn_mut`]: crate::slice::BitSlice::rsplitn_mut
**/
pub struct RSplitNMut<'a, O, T, P>
where
	O: BitOrder,
	T: BitStore,
	P: FnMut(usize, &bool) -> bool,
{
	/// The [`BitSlice`] being split.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	inner: RSplitMut<'a, O, T, P>,
	/// The number of splits remaining.
	count: usize,
}

macro_rules! split_n {
	($outer:ident => $inner:ident => $item:ty $( where $alias:ident )?) => {
		impl<'a, O, T, P> $outer <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
		{
			pub(super) fn new(
				slice: $item,
				pred: P,
				count: usize,
			) -> Self
			{Self{
				inner: <$inner<'a, O, T, P>>::new(slice, pred),
				count,
			}}
		}

		impl<O, T, P> Debug for $outer <'_, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool
		{
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				fmt.debug_struct(stringify!($outer))
					.field("slice", &self.inner.slice)
					.field("count", &self.count)
					.finish()
			}
		}

		impl<'a, O, T, P> Iterator for $outer <'a, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
			$( T::$alias: radium::Radium<<<T as BitStore>::Alias as BitStore>::Mem>, )?
		{
			type Item = <$inner <'a, O, T, P> as Iterator>::Item;

			#[inline]
			fn next(&mut self) -> Option<Self::Item> {
				match self.count {
					0 => None,
					1 => {
						self.count -= 1;
						self.inner.finish()
					},
					_ => {
						self.count -= 1;
						self.inner.next()
					},
				}
			}

			#[inline]
			fn size_hint(&self) -> (usize, Option<usize>) {
				let (low, hi) = self.inner.size_hint();
				(low, hi.map(|h| cmp::min(self.count, h)))
			}
		}

		impl<O, T, P> core::iter::FusedIterator for $outer <'_, O, T, P>
		where
			O: BitOrder,
			T: BitStore,
			P: FnMut(usize, &bool) -> bool,
			$( T::$alias: radium::Radium<<<T as BitStore>::Alias as BitStore>::Mem>, )?
		{
		}
	};
}

split_n!(SplitN => Split => &'a BitSlice<O, T>);
split_n!(SplitNMut => SplitMut => &'a mut BitSlice<O, T::Alias> );
split_n!(RSplitN => RSplit => &'a BitSlice<O, T>);
split_n!(RSplitNMut => RSplitMut => &'a mut BitSlice<O, T::Alias> );

/** Enumerates bits in a [`BitSlice`] that are set to `1`.

This struct is created by the [`.iter_ones()`] method on [`BitSlice`]s.

[`BitSlice`]: crate::slice::BitSlice
[`.iter_ones()`]: crate::slice::BitSlice::iter_ones
**/
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct IterOnes<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The remaining slice whose `1` bits are to be found.
	inner: &'a BitSlice<O, T>,
	/// The number of `1` bits remaining in `inner`.
	count: usize,
	/// The offset from the front of the original slice to current `inner`.
	front: usize,
}

impl<'a, O, T> IterOnes<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	#[cfg(not(tarpaulin_include))]
	fn empty() -> Self {
		Self {
			inner: BitSlice::empty(),
			count: 0,
			front: 0,
		}
	}

	#[inline]
	pub(crate) fn new(slice: &'a BitSlice<O, T>) -> Self {
		let count = slice.count_ones();
		Self {
			inner: slice,
			count,
			front: 0,
		}
	}
}

impl<O, T> Iterator for IterOnes<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Item = usize;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		if self.count == 0 {
			return None;
		}
		match self.inner.iter().copied().position(|b| b) {
			Some(n) => {
				//  Split on the far side of the found index. This is always
				//  safe, as split(len) yields (self, empty).
				let (_, rest) = unsafe { self.inner.split_at_unchecked(n + 1) };
				self.inner = rest;
				self.count -= 1;
				let out = self.front + n;
				//  Search resumes from the next index after the found.
				self.front = out + 1;
				Some(out)
			},
			None => {
				*self = Self::empty();
				None
			},
		}
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn size_hint(&self) -> (usize, Option<usize>) {
		(self.count, Some(self.count))
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn count(self) -> usize {
		self.count
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T> DoubleEndedIterator for IterOnes<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.count == 0 {
			return None;
		}
		match self.inner.iter().copied().rposition(|b| b) {
			Some(n) => {
				let (rest, _) = unsafe { self.inner.split_at_unchecked(n) };
				self.inner = rest;
				self.count -= 1;
				Some(self.front + n)
			},
			None => {
				*self = Self::empty();
				None
			},
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> ExactSizeIterator for IterOnes<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn len(&self) -> usize {
		self.count
	}
}

impl<O, T> FusedIterator for IterOnes<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

/** Enumerates bits in a [`BitSlice`] that are cleared to `0`.

This struct is created by the [`.iter_zeros()`] method on [`BitSlice`]s.

[`BitSlice`]: crate::slice::BitSlice
[`.iter_zeros()`]: crate::slice::BitSlice::iter_zeros
**/
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct IterZeros<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	/// The remaining slice whose `0` bits are to be found.
	inner: &'a BitSlice<O, T>,
	/// The number of `0` bits remaining in `inner`.
	count: usize,
	/// The offset from the front of the original slice to current `inner`.
	front: usize,
}

impl<'a, O, T> IterZeros<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	#[cfg(not(tarpaulin_include))]
	fn empty() -> Self {
		Self {
			inner: BitSlice::empty(),
			count: 0,
			front: 0,
		}
	}

	#[inline]
	pub(crate) fn new(slice: &'a BitSlice<O, T>) -> Self {
		let count = slice.count_zeros();
		Self {
			inner: slice,
			count,
			front: 0,
		}
	}
}

impl<O, T> Iterator for IterZeros<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Item = usize;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		if self.count == 0 {
			return None;
		}
		match self.inner.iter().copied().position(|b| !b) {
			Some(n) => {
				let (_, rest) = unsafe { self.inner.split_at_unchecked(n + 1) };
				self.inner = rest;
				self.count -= 1;
				let out = self.front + n;
				self.front = out + 1;
				Some(out)
			},
			None => {
				*self = Self::empty();
				None
			},
		}
	}

	#[inline(always)]
	fn size_hint(&self) -> (usize, Option<usize>) {
		(self.count, Some(self.count))
	}

	#[inline(always)]
	fn count(self) -> usize {
		self.count
	}

	#[inline(always)]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<O, T> DoubleEndedIterator for IterZeros<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.count == 0 {
			return None;
		}
		match self.inner.iter().copied().rposition(|b| !b) {
			Some(n) => {
				let (rest, _) = unsafe { self.inner.split_at_unchecked(n) };
				self.inner = rest;
				self.count -= 1;
				Some(self.front + n)
			},
			None => {
				self.inner = BitSlice::empty();
				self.count = 0;
				None
			},
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> ExactSizeIterator for IterZeros<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn len(&self) -> usize {
		self.count
	}
}

impl<O, T> FusedIterator for IterZeros<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

/* This macro has some very obnoxious call syntax that is necessary to handle
the different iteration protocols used above.

The `Split` iterators are not `DoubleEndedIterator` or `ExactSizeIterator`, and
must be excluded from those implementations. However, bounding on `DEI` causes
`.next_back()` and `.nth_back()` to return opaque associated types, rather than
the return type from the directly-resolved signatures. As such, the item type of
the source iterator must also be provided so that methods on it can be named.
*/
macro_rules! noalias {
	( $(
		$from:ident $( ( $p:ident ) )?
		=> $alias:ty
		=> $to:ident
		=> $item:ty
		=> $map:path
		;
	)+ ) => { $(
		/// An iterator variant that does not apply a [`T::Alias`] marker to its
		/// yielded items.
		///
		/// This iterator can be safely used in `for … in` loop headers, but
		/// cannot be used anywhere that its surrounding code may pull multiple
		/// yielded items into the same scope. This includes any iterator
		/// adapters that pull multiple yielded items into the same collection!
		/// Each yielded item **must** not have any sibling items in its scope.
		///
		/// This iterator does not yield [`T::Mem`] raw-typed references, as it
		/// may be produced from an already-aliased iterator and must retain its
		/// initial aliasing properties. It merely asserts that it will not be
		/// used in contexts that produce multiple yielded items in the same
		/// scope.
		///
		/// [`T::Alias`]: crate::store::BitStore::Alias
		/// [`T::Mem`]: crate::store::BitStore::Mem
		pub struct $to <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			/// The actual iterator that this modifies.
			inner: $from <'a, O, T $( , $p )? >,
		}

		impl<'a, O, T $( , $p )? > $from <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			/// Adapts the iterator to no longer mark its yielded items as
			/// aliased.
			///
			/// # Safety
			///
			/// This adapter can only be used in contexts where only one yielded
			/// item will be alive at any time. This is most commonly true in
			/// `for … in` loops, so long as no subsequent adapter collects
			/// multiple yielded items into a collection where they are live
			/// simultaneously.
			///
			/// The items yielded by this iterator will not have an additional
			/// alias marker applied to them, so their use in an iteration
			/// sequence will not be penalized when the surrounding code
			/// guarantees that each item yielded by the iterator is destroyed
			/// before the next is produced.
			///
			/// This adapter does **not** convert the iterator to use [`T::Mem`]
			/// raw types, as it can be applied to an iterator over an
			/// already-aliased slice and must preserve its condition. Its only
			/// effect is to prevent the addition of a new [`T::Alias`] marker.
			///
			/// [`T::Alias`]: crate::store::BitStore::Alias
			/// [`T::Mem`]: crate::store::BitStore::Mem
			#[inline(always)]
			pub fn remove_alias(self) -> $to <'a, O, T $( , $p )? > {
				$to ::new(self)
			}
		}

		impl<'a, O, T $( , $p )? > $to <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			#[inline(always)]
			fn new(inner: $from<'a, O, T $( , $p )? >) -> Self {
				Self { inner }
			}
		}

		impl<'a, O, T $( , $p )? > Iterator for $to <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			type Item = $item;

			#[inline(always)]
			fn next(&mut self) -> Option<Self::Item> {
				self.inner.next().map(|item| unsafe { $map(item) })
			}

			#[inline(always)]
			fn size_hint(&self) -> (usize, Option<usize>) {
				self.inner.size_hint()
			}

			#[inline(always)]
			fn count(self) -> usize {
				self.inner.count()
			}

			#[inline(always)]
			fn nth(&mut self, n: usize) -> Option<Self::Item> {
				self.inner.nth(n).map(|item| unsafe { $map(item) })
			}

			#[inline(always)]
			fn last(self) -> Option<Self::Item> {
				self.inner.last().map(|item| unsafe { $map(item) })
			}
		}

		impl<'a, O, T $( , $p )? > DoubleEndedIterator for $to <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$from <'a, O, T $( , $p )? >: DoubleEndedIterator<Item = $alias >,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			#[inline(always)]
			fn next_back(&mut self) -> Option<Self::Item> {
				self.inner
					.next_back()
					.map(|item| unsafe { $map(item) })
				}

				#[inline(always)]
				fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
					self.inner
					.nth_back(n)
					.map(|item| unsafe { $map(item) })
			}
		}

		impl<'a, O, T $( , $p )? > ExactSizeIterator for $to <'a, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$from <'a, O, T $( , $p )? >: ExactSizeIterator,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
			#[inline(always)]
			fn len(&self) -> usize {
				self.inner.len()
			}
		}

		impl<O, T $( , $p )? > FusedIterator for $to <'_, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
		}

		unsafe impl<O, T $( , $p )? > Send for $to <'_, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
		}

		unsafe impl<O, T $( , $p )? > Sync for $to <'_, O, T $( , $p )? >
		where
			O: BitOrder,
			T: BitStore,
			$( $p : FnMut(usize, &bool) -> bool, )?
		{
		}
	)+ };
}

noalias! {
	IterMut => <usize as BitSliceIndex<'a, O, T::Alias>>::Mut
	=> IterMutNoAlias => <usize as BitSliceIndex<'a, O, T>>::Mut
	=> BitMut::remove_alias;

	ChunksMut => &'a mut BitSlice<O, T::Alias>
	=> ChunksMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	ChunksExactMut => &'a mut BitSlice<O, T::Alias>
	=> ChunksExactMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	RChunksMut => &'a mut BitSlice<O, T::Alias>
	=> RChunksMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	RChunksExactMut => &'a mut BitSlice<O, T::Alias>
	=> RChunksExactMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	SplitMut (P) => &'a mut BitSlice<O, T::Alias>
	=> SplitMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	RSplitMut (P) => &'a mut BitSlice<O, T::Alias>
	=> RSplitMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	SplitNMut (P) => &'a mut BitSlice<O, T::Alias>
	=> SplitNMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;

	RSplitNMut (P) => &'a mut BitSlice<O, T::Alias>
	=> RSplitNMutNoAlias => &'a mut BitSlice<O, T>
	=> BitSlice::unalias_mut;
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	#[test]
	fn iter() {
		let bits = bits![Lsb0, u8; 0, 1, 1, 0, 1, 0, 0, 1];
		let mut iter = bits.iter();

		assert_eq!(iter.as_bitslice(), bits);
		assert_eq!(iter.next(), Some(&false));
		assert_eq!(iter.as_bitslice(), &bits[1 ..]);
		assert_eq!(iter.next(), Some(&true));

		assert_eq!(iter.as_bitslice(), &bits[2 ..]);
		assert_eq!(iter.next_back(), Some(&true));
		assert_eq!(iter.as_bitslice(), &bits[2 .. 7]);
		assert_eq!(iter.next_back(), Some(&false));

		assert_eq!(iter.as_bitslice(), &bits[2 .. 6]);
		assert_eq!(iter.next(), Some(&true));
		assert_eq!(iter.as_bitslice(), &bits[3 .. 6]);
		assert_eq!(iter.next(), Some(&false));

		assert_eq!(iter.as_bitslice(), &bits[4 .. 6]);
		assert_eq!(iter.next_back(), Some(&false));
		assert_eq!(iter.as_bitslice(), &bits[4 .. 5]);

		assert_eq!(iter.next_back(), Some(&true));
		assert!(iter.as_bitslice().is_empty());
		assert!(iter.next().is_none());
		assert!(iter.next_back().is_none());
	}

	#[test]
	fn iter_mut() {
		let bits = bits![mut Msb0, u8; 0, 1, 1, 0, 1, 0, 0, 1];
		let mut iter = bits.iter_mut();

		*iter.next().unwrap() = true;
		*iter.nth_back(1).unwrap() = true;
		*iter.nth(2).unwrap() = true;
		*iter.next_back().unwrap() = true;

		assert_eq!(iter.into_bitslice().bitptr(), bits[4 .. 5].bitptr());
	}

	#[test]
	fn windows() {
		let bits = bits![LocalBits, u8; 0; 8];

		let mut windows = bits.windows(5);
		assert_eq!(windows.next().unwrap().bitptr(), bits[.. 5].bitptr());
		assert_eq!(windows.next_back().unwrap().bitptr(), bits[3 ..].bitptr());

		let mut windows = bits.windows(3);
		assert_eq!(windows.nth(2).unwrap().bitptr(), bits[2 .. 5].bitptr());
		assert_eq!(windows.nth_back(2).unwrap().bitptr(), bits[3 .. 6].bitptr());
		assert!(windows.next().is_none());
		assert!(windows.next_back().is_none());
		assert!(windows.nth(1).is_none());
		assert!(windows.nth_back(1).is_none());
	}

	#[test]
	fn chunks() {
		let bits = bits![Lsb0, u16; 0; 16];

		let mut chunks = bits.chunks(5);
		assert_eq!(chunks.next().unwrap().bitptr(), bits[.. 5].bitptr());
		assert_eq!(chunks.next_back().unwrap().bitptr(), bits[15 ..].bitptr());

		let mut chunks = bits.chunks(3);
		assert_eq!(chunks.nth(2).unwrap().bitptr(), bits[6 .. 9].bitptr());
		assert_eq!(chunks.nth_back(2).unwrap().bitptr(), bits[9 .. 12].bitptr());
	}

	#[test]
	fn chunks_mut() {
		let bits = bits![mut Msb0, u16; 0; 16];

		let (one, two, three, four) = (
			bits[.. 5].bitptr(),
			bits[15 ..].bitptr(),
			bits[6 .. 9].bitptr(),
			bits[9 .. 12].bitptr(),
		);

		let mut chunks = bits.chunks_mut(5);
		assert_eq!(chunks.next().unwrap().bitptr(), one);
		assert_eq!(chunks.next_back().unwrap().bitptr(), two);

		let mut chunks = bits.chunks_mut(3);
		assert_eq!(chunks.nth(2).unwrap().bitptr(), three);
		assert_eq!(chunks.nth_back(2).unwrap().bitptr(), four);
	}

	#[test]
	fn chunks_exact() {
		let bits = bits![Lsb0, u32; 0; 32];

		let mut chunks = bits.chunks_exact(5);
		assert_eq!(chunks.remainder().bitptr(), bits[30 ..].bitptr());
		assert_eq!(chunks.next().unwrap().bitptr(), bits[.. 5].bitptr());
		assert_eq!(
			chunks.next_back().unwrap().bitptr(),
			bits[25 .. 30].bitptr(),
		);
		assert_eq!(chunks.nth(1).unwrap().bitptr(), bits[10 .. 15].bitptr());
		assert_eq!(
			chunks.nth_back(1).unwrap().bitptr(),
			bits[15 .. 20].bitptr(),
		);

		assert!(chunks.next().is_none());
		assert!(chunks.next_back().is_none());
		assert!(chunks.nth(1).is_none());
		assert!(chunks.nth_back(1).is_none());
	}

	#[test]
	fn chunks_exact_mut() {
		let bits = bits![mut Msb0, u32; 0; 32];

		let (one, two, three, four, rest) = (
			bits[.. 5].bitptr(),
			bits[10 .. 15].bitptr(),
			bits[15 .. 20].bitptr(),
			bits[25 .. 30].bitptr(),
			bits[30 ..].bitptr(),
		);

		let mut chunks = bits.chunks_exact_mut(5);
		assert_eq!(chunks.next().unwrap().bitptr(), one);
		assert_eq!(chunks.next_back().unwrap().bitptr(), four);
		assert_eq!(chunks.nth(1).unwrap().bitptr(), two);
		assert_eq!(chunks.nth_back(1).unwrap().bitptr(), three);

		assert!(chunks.next().is_none());
		assert!(chunks.next_back().is_none());
		assert!(chunks.nth(1).is_none());
		assert!(chunks.nth_back(1).is_none());

		assert_eq!(chunks.into_remainder().bitptr(), rest);
	}

	#[test]
	fn rchunks() {
		let bits = bits![Lsb0, u16; 0; 16];

		let mut rchunks = bits.rchunks(5);
		assert_eq!(rchunks.next().unwrap().bitptr(), bits[11 ..].bitptr());
		assert_eq!(rchunks.next_back().unwrap().bitptr(), bits[.. 1].bitptr());

		let mut rchunks = bits.rchunks(3);
		assert_eq!(rchunks.nth(2).unwrap().bitptr(), bits[7 .. 10].bitptr());
		assert_eq!(rchunks.nth_back(2).unwrap().bitptr(), bits[4 .. 7].bitptr());
	}

	#[test]
	fn rchunks_mut() {
		let bits = bits![mut Msb0, u16; 0; 16];

		let (one, two, three, four) = (
			bits[11 ..].bitptr(),
			bits[.. 1].bitptr(),
			bits[7 .. 10].bitptr(),
			bits[4 .. 7].bitptr(),
		);

		let mut rchunks = bits.rchunks_mut(5);
		assert_eq!(rchunks.next().unwrap().bitptr(), one);
		assert_eq!(rchunks.next_back().unwrap().bitptr(), two);

		let mut rchunks = bits.rchunks_mut(3);
		assert_eq!(rchunks.nth(2).unwrap().bitptr(), three);
		assert_eq!(rchunks.nth_back(2).unwrap().bitptr(), four);
	}

	#[test]
	fn rchunks_exact() {
		let bits = bits![Lsb0, u32; 0; 32];

		let mut rchunks = bits.rchunks_exact(5);
		assert_eq!(rchunks.remainder().bitptr(), bits[.. 2].bitptr());
		assert_eq!(rchunks.next().unwrap().bitptr(), bits[27 ..].bitptr());
		assert_eq!(rchunks.next_back().unwrap().bitptr(), bits[2 .. 7].bitptr(),);
		assert_eq!(rchunks.nth(1).unwrap().bitptr(), bits[17 .. 22].bitptr());
		assert_eq!(
			rchunks.nth_back(1).unwrap().bitptr(),
			bits[12 .. 17].bitptr(),
		);

		assert!(rchunks.next().is_none());
		assert!(rchunks.next_back().is_none());
		assert!(rchunks.nth(1).is_none());
		assert!(rchunks.nth_back(1).is_none());
	}

	#[test]
	fn rchunks_exact_mut() {
		let bits = bits![mut Msb0, u32; 0; 32];

		let (rest, one, two, three, four) = (
			bits[.. 2].bitptr(),
			bits[2 .. 7].bitptr(),
			bits[12 .. 17].bitptr(),
			bits[17 .. 22].bitptr(),
			bits[27 ..].bitptr(),
		);

		let mut rchunks = bits.rchunks_exact_mut(5);
		assert_eq!(rchunks.next().unwrap().bitptr(), four);
		assert_eq!(rchunks.next_back().unwrap().bitptr(), one);
		assert_eq!(rchunks.nth(1).unwrap().bitptr(), three);
		assert_eq!(rchunks.nth_back(1).unwrap().bitptr(), two);

		assert!(rchunks.next().is_none());
		assert!(rchunks.next_back().is_none());
		assert!(rchunks.nth(1).is_none());
		assert!(rchunks.nth_back(1).is_none());

		assert_eq!(rchunks.into_remainder().bitptr(), rest);
	}

	#[test]
	fn iter_ones_zeros() {
		//                          0  1  2  3  4  5  6  7
		let bits = bits![0, 0, 1, 1, 0, 1, 0, 1];
		let mut ones = bits.iter_ones();
		let mut zeros = bits.iter_zeros();

		assert_eq!(ones.next(), Some(2));
		assert_eq!(zeros.next(), Some(0));

		assert_eq!(ones.next_back(), Some(7));
		assert_eq!(zeros.next_back(), Some(6));
	}
}
