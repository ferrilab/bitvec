//! Implementation of `Range<BitPtr>`.

use crate::{
	index::BitIdx,
	mem::BitMemory,
	mutability::Mutability,
	order::BitOrder,
	ptr::{
		Address,
		BitPtr,
		BitSpan,
	},
	store::BitStore,
};

use core::{
	fmt::{
		self,
		Debug,
		Formatter,
		Pointer,
	},
	iter::FusedIterator,
	marker::PhantomData,
	ops::Range,
};

/** Corresponds to `Range<*bool>`, as `Range<BitPtr>` is not representable.

`Range` depends on a number of unstable associated traits, and as a container
defined in `core`, cannot be extended here.

This is strictly an exclusive range: the end pointer is not included in the span
that the range describes.

# Original

[`Range<*bool>`](core::ops::Range)

# API Differences

This cannot be constructed directly from the `..` syntax, though a `From`
implementation is provided.

# Type Parameters

- `M`: The write permissions of the pointers this range produces.
- `O`: The bit-ordering within a storage element used to access bits.
- `T`: The storage element type containing the referent bits.
**/
#[repr(C)]
pub struct BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	//  Semantically, this is two `BitPtr<O, T>`, but structurally, the `BitPtr`
	//  members need to be kept unpacked so that this compacts to three words
	//  rather than four.
	base: Address<M, T>,
	last: Address<M, T>,
	head: BitIdx<T::Mem>,
	tail: BitIdx<T::Mem>,
	_ord: PhantomData<O>,
}

impl<M, O, T> BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	/// An empty range.
	pub const EMPTY: Self = Self {
		base: Address::DANGLING,
		last: Address::DANGLING,
		head: BitIdx::ZERO,
		tail: BitIdx::ZERO,
		_ord: PhantomData,
	};

	/// Produces the inclusive start and exclusive end pointers of the range.
	///
	/// # Parameters
	///
	/// - `self`: A clone of the range to destructure.
	///
	/// # Returns
	///
	/// - `.0`: The inclusive start pointer of the range.
	/// - `.1`: The exclusive end pointer of the range.
	pub fn pointers(self) -> (BitPtr<M, O, T>, BitPtr<M, O, T>) {
		unsafe {
			(
				BitPtr::new_unchecked(self.base, self.head),
				BitPtr::new_unchecked(self.last, self.tail),
			)
		}
	}

	/// Returns `true` if the range contains no referent bits.
	///
	/// # Original
	///
	/// [`Range::is_empty`](core::ops::Range::is_empty)
	pub fn is_empty(&self) -> bool {
		let (start, end) = self.pointers();
		start == end
	}

	/// Returns `true` if the `pointer` is contained in the range.
	///
	/// # Original
	///
	/// [`Range::contains`](core::ops::Range::contains)
	///
	/// # API Differences
	///
	/// This permits pointers of similar memory element type, and any mutability
	/// permission, rather than being constrained to exactly the same type as
	/// the range.
	pub fn contains<M2, T2>(&self, pointer: &BitPtr<M2, O, T2>) -> bool
	where
		M2: Mutability,
		T2: BitStore,
	{
		let (start, end) = self.pointers();
		start.le(&pointer) && pointer.lt(&end)
	}

	/// Converts the pair into a single span descriptor over all included bits.
	///
	/// The produce span does *not* include the bit addressed by the end
	/// pointer, as this is an exclusive range.
	pub(crate) fn into_bit_span(self) -> BitSpan<M, O, T> {
		unsafe { BitSpan::new_unchecked(self.base, self.head, self.len()) }
	}

	/// Takes a pointer from the front of the range.
	///
	/// # Preconditions
	///
	/// `self` must not be empty.
	///
	/// # Behavior
	///
	/// The front pointer is returned, then incremented.
	fn take_front(&mut self) -> BitPtr<M, O, T> {
		let out = unsafe { BitPtr::new_unchecked(self.base, self.head) };
		let (head, incr) = self.head.next();
		self.head = head;
		self.base = unsafe {
			Address::new_unchecked(
				self.base.to_const().add(incr as usize) as usize
			)
		};
		out
	}

	/// Takes a pointer from the back of the range.
	///
	/// # Preconditions
	///
	/// `self` must not be empty
	///
	/// # Behavior
	///
	/// The back pointer is decremented, then returned.
	fn take_back(&mut self) -> BitPtr<M, O, T> {
		let (tail, decr) = self.tail.prev();
		self.tail = tail;
		unsafe {
			self.last = Address::new_unchecked(
				self.last.to_const().sub(decr as usize) as usize,
			);
			BitPtr::new_unchecked(self.last, self.tail)
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> Clone for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		*self
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> From<BitSpan<M, O, T>> for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn from(span: BitSpan<M, O, T>) -> Self {
		let (base, head, bits) = span.raw_parts();
		let (elts, tail) = head.offset(bits as isize);
		let last = unsafe {
			Address::new_unchecked(base.to_const().offset(elts) as usize)
		};
		Self {
			base,
			last,
			head,
			tail,
			_ord: PhantomData,
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> From<Range<BitPtr<M, O, T>>> for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn from(Range { start, end }: Range<BitPtr<M, O, T>>) -> Self {
		let (base, head) = start.raw_parts();
		let (last, tail) = end.raw_parts();
		Self {
			base,
			last,
			head,
			tail,
			_ord: PhantomData,
		}
	}
}

#[cfg(not(tarpaulin_include))]
impl<M, O, T> Debug for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let (from, upto) = self.pointers();
		Pointer::fmt(&from, fmt)?;
		fmt.write_str("..")?;
		Pointer::fmt(&upto, fmt)
	}
}

impl<M, O, T> Iterator for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	type Item = BitPtr<M, O, T>;

	fn next(&mut self) -> Option<Self::Item> {
		if Self::is_empty(&*self) {
			return None;
		}
		Some(self.take_front())
	}

	fn nth(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.base = self.last;
			self.head = self.tail;
			return None;
		}
		let (elts, head) = self.head.offset(n as isize);
		self.head = head;
		self.base = unsafe {
			Address::new_unchecked(self.base.to_const().offset(elts) as usize)
		};
		Some(self.take_front())
	}

	#[cfg(not(tarpaulin_include))]
	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn count(self) -> usize {
		self.len()
	}

	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	fn last(mut self) -> Option<Self::Item> {
		self.next_back()
	}
}

impl<M, O, T> DoubleEndedIterator for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		if Self::is_empty(&*self) {
			return None;
		}
		Some(self.take_back())
	}

	fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
		if n >= self.len() {
			self.last = self.base;
			self.tail = self.head;
			return None;
		}
		let (elts, tail) = self.tail.offset(-(n as isize));
		self.tail = tail;
		self.last = unsafe {
			Address::new_unchecked(self.last.to_const().offset(elts) as usize)
		};
		Some(self.take_back())
	}
}

impl<M, O, T> ExactSizeIterator for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
	fn len(&self) -> usize {
		//  Get the byte distance between the start and end pointers,
		self.last
			.value()
			.wrapping_sub(self.base.value())
			//  Multiply it by the bit-width of a byte,
			.wrapping_mul(<u8 as BitMemory>::BITS as usize)
			//  Add any excess bits in the tail element,
			.wrapping_add(self.tail.value() as usize)
			//  And subtract any excess bits in the head element.
			.wrapping_sub(self.head.value() as usize)
	}
}

impl<M, O, T> FusedIterator for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}

impl<M, O, T> Copy for BitPtrRange<M, O, T>
where
	M: Mutability,
	O: BitOrder,
	T: BitStore,
{
}
