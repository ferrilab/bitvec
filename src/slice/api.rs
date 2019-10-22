/*! Reimplementation of the slice fundamental’s inherent method API.
!*/

use super::*;

use core::{
	ops::{
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
	},
};

/// Reimplementation of the `[T]` inherent-method API.
impl<C, T> BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Returns the number of bits in the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 0u8.bits::<Local>();
	/// assert_eq!(bits.len(), 8);
	/// ```
	pub fn len(&self) -> usize {
		self.bitptr().len()
	}

	/// Returns `true` if the slice has a length of 0.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 0u8.bits::<Local>();
	/// assert!(!bits.is_empty());
	///
	/// assert!(BitSlice::<Local, Word>::empty().is_empty())
	/// ```
	pub fn is_empty(&self) -> bool {
		self.bitptr().len() == 0
	}

	/// Returns the first bit of the slice, or `None` if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<LittleEndian>();
	/// assert_eq!(bits.first(), Some(&true));
	///
	/// assert!(BitSlice::<Local, Word>::empty().first().is_none());
	/// ```
	pub fn first(&self) -> Option<&bool> {
		if self.is_empty() {
			None
		}
		else {
			Some(&self[0])
		}
	}

	/// Returns a mutable pointer to the first bit of the slice, or `None` if it
	/// is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// if let Some(mut first) = bits.first_mut() {
	///     *first = true;
	/// }
	/// assert_eq!(data, 1u8);
	/// ```
	pub fn first_mut(&mut self) -> Option<BitGuard<C, T>> {
		if self.is_empty() {
			None
		}
		else {
			Some(self.at(0))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<LittleEndian>();
	/// if let Some((first, rest)) = bits.split_first() {
	///     assert_eq!(first, &true);
	///     assert_eq!(rest, &bits[1 ..]);
	/// }
	/// ```
	pub fn split_first(&self) -> Option<(&bool, &Self)> {
		if self.is_empty() {
			None
		}
		else {
			Some((&self[0], &self[1 ..]))
		}
	}

	/// Returns the first and all the rest of the bits of the slice, or `None`
	/// if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<LittleEndian>();
	/// if let Some((mut first, rest)) = bits.split_first_mut() {
	///     *first = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 7);
	/// ```
	pub fn split_first_mut(&mut self) -> Option<(BitGuard<C, T>, &mut Self)> {
		if self.is_empty() {
			None
		}
		else {
			let (head, rest) = self.split_at_mut(1);
			Some((head.at(0), rest))
		}
	}

	/// Returns the last and all the rest of the bits of the slice, or `None` if
	/// it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<BigEndian>();
	/// if let Some((last, rest)) = bits.split_last() {
	///     assert_eq!(last, &true);
	///     assert_eq!(rest, &bits[.. 7]);
	/// }
	/// ```
	pub fn split_last(&self) -> Option<(&bool, &Self)> {
		match self.len() {
			0 => None,
			len => Some((&self[len - 1], &self[.. len - 1])),
		}
	}

	/// Returns the last and all the rest of the bits of the slice, or `None` if
	/// it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// if let Some((mut last, rest)) = bits.split_last_mut() {
	///     *last = true;
	///     *rest.at(0) = true;
	///     *rest.at(1) = true;
	/// }
	/// assert_eq!(data, 128 | 64 | 1);
	/// ```
	pub fn split_last_mut(&mut self) -> Option<(BitGuard<C, T>, &mut Self)> {
		match self.len() {
			0 => None,
			len => {
				let (rest, tail) = self.split_at_mut(len - 1);
				Some((tail.at(0), rest))
			},
		}
	}

	/// Returns the last bit of the slice, or `None` if it is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let bits = 1u8.bits::<BigEndian>();
	/// assert_eq!(Some(&true), bits.last());
	/// assert!(BitSlice::<Local, Word>::empty().last().is_none());
	/// ```
	pub fn last(&self) -> Option<&bool> {
		match self.len() {
			0 => None,
			len => Some(&self[len - 1]),
		}
	}

	/// Returns a mutable pointer to the last bit in the slice.
	///
	/// # Examples
	///
	/// ```rust
	/// # use bitvec::prelude::*;
	/// let mut data = 0u8;
	/// let bits = data.bits_mut::<BigEndian>();
	/// if let Some(mut last) = bits.last_mut() {
	///     *last = true;
	/// }
	/// assert!(bits[7]);
	pub fn last_mut(&mut self) -> Option<BitGuard<C, T>> {
		match self.len() {
			0 => None,
			len => Some(self.at(len - 1)),
		}
	}

	pub fn get<'a, I>(&'a self, index: I) -> Option<<I as BitSliceIndex<'a, C, T>>::ImmutOutput>
	where I: BitSliceIndex<'a, C, T> {
		index.get(self)
	}
}

/** Replacement for [`core::slice::SliceIndex`].

This trait is stabilized in definition and `type Output` only, but all methods
are unstable. This makes it unusable in non-`libstd` slice libraries, and so it
must be duplicated here.

There is no tracking issue for `feature(slice_index_methods)`.

[`core::slice::SliceIndex`]: https://doc.rust-lang.org/stable/core/slice/trait.SliceIndex.html
**/
pub trait BitSliceIndex<'a, C, T>
where C: 'static + Cursor, T: 'a + BitStore {
	/// Immutable output type.
	type ImmutOutput;

	/// Mutable output type. This is necessary because `&mut BitSlice` is
	/// producible for range indices, but `&mut bool` is not producable for
	/// `usize` indices.
	type MutOutput;

	/// Returns a shared reference to the output at this location, if in bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output, if `self` is in bounds; otherwise `None`.
	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput>;

	/// Returns a mutable reference to the output at this location, if in
	/// bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output, if `self` is in bounds; otherwise `None`.
	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput>;

	/// Returns a shared reference to the output at this location, without
	/// performing any bounds checking.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output.
	unsafe fn get_unchecked(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput;

	/// Returns a mutable reference to the output at this location, without
	/// performing any bounds checking.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output.
	unsafe fn get_unchecked_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput;

	/// Returns a shared reference to the output at this location, panicking if
	/// out of bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// An immutable output.
	///
	/// # Panics
	///
	/// This panics if `self` is out of bounds of `slice`.
	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput;

	/// Returns a mutable reference to the output at this location, panicking if
	/// out of bounds.
	///
	/// # Parameters
	///
	/// - `self`: The index value.
	/// - `slice`: The slice under index.
	///
	/// # Returns
	///
	/// A mutable output.
	///
	/// # Panics
	///
	/// This panics if `self` is out of bounds of `slice`.
	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput;
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for usize
where C: 'static + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a bool;
	type MutOutput = BitGuard<'a, C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		if self >= slice.len() {
			None
		}
		else {
			Some(unsafe { self.get_unchecked(slice) })
		}
	}

	fn get_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Option<Self::MutOutput> {
		if self < slice.len() {
			Some(slice.at(self))
		}
		else {
			None
		}
	}

	unsafe fn get_unchecked(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		let bitptr = slice.bitptr();
		let (elt, bit) = bitptr.head().offset(self as isize);
		let data_ptr = bitptr.pointer().a();

		if (&*data_ptr.offset(elt)).get::<C>(bit) {
			&true
		}
		else {
			&false
		}
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		slice.at_unchecked(self)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		match self.get(slice) {
			None => panic!("Index {} out of bounds: {}", self, slice.len()),
			Some(out) => out,
		}
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		slice.at(self)
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for Range<usize>
where C: 'static + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		let Range { start, end } = self;
		let bits = slice.len();
		if start > bits || end > bits || start > end {
			return None;
		}

		Some(unsafe { self.get_unchecked(slice) })
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		self.get(slice).map(|s| s.bitptr().into_bitslice_mut::<C>())
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		let Range { start, end } = self;
		let (data, head, _) = slice.bitptr().raw_parts();

		let (skip, new_head) = head.offset(start as isize);
		let new_bits = end - start;

		BitPtr::new_unchecked(
			data.r().offset(skip),
			new_head,
			new_bits,
		).into_bitslice::<C>()
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		self.get_unchecked(slice).bitptr().into_bitslice_mut::<C>()
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		match self.clone().get(slice) {
			None => panic!("Range {:?} exceeds length {}", self, slice.len()),
			Some(out) => out,
		}
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		self.index(slice).bitptr().into_bitslice_mut::<C>()
	}
}

impl<'a, C, T> BitSliceIndex<'a, C, T> for RangeInclusive<usize>
where C: 'static + Cursor, T: 'a + BitStore {
	type ImmutOutput = &'a BitSlice<C, T>;
	type MutOutput = &'a mut BitSlice<C, T>;

	fn get(self, slice: &'a BitSlice<C, T>) -> Option<Self::ImmutOutput> {
		(*self.start() .. *self.end() + 1).get(slice)
	}

	fn get_mut(self, slice: &'a mut BitSlice<C, T>) -> Option<Self::MutOutput> {
		(*self.start() .. *self.end() + 1).get_mut(slice)
	}

	unsafe fn get_unchecked(
		self,
		slice: &'a BitSlice<C, T>,
	) -> Self::ImmutOutput {
		(*self.start() .. *self.end() + 1).get_unchecked(slice)
	}

	unsafe fn get_unchecked_mut(
		self,
		slice: &'a mut BitSlice<C, T>,
	) -> Self::MutOutput {
		(*self.start() .. *self.end() + 1).get_unchecked_mut(slice)
	}

	fn index(self, slice: &'a BitSlice<C, T>) -> Self::ImmutOutput {
		(*self.start() .. *self.end() + 1).index(slice)
	}

	fn index_mut(self, slice: &'a mut BitSlice<C, T>) -> Self::MutOutput {
		(*self.start() .. *self.end() + 1).index_mut(slice)
	}
}
