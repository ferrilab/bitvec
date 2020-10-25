//! Non-operator trait implementations.

use crate::{
	boxed::BitBox,
	order::BitOrder,
	ptr::BitPtr,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

use alloc::boxed::Box;

use core::{
	borrow::{
		Borrow,
		BorrowMut,
	},
	cmp,
	convert::TryFrom,
	fmt::{
		self,
		Binary,
		Debug,
		Display,
		Formatter,
		LowerHex,
		Octal,
		Pointer,
		UpperHex,
	},
	hash::{
		Hash,
		Hasher,
	},
};

use tap::pipe::Pipe;

impl<O, T> Borrow<BitSlice<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn borrow(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

impl<O, T> BorrowMut<BitSlice<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn borrow_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<O, T> Clone for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		self.as_bitslice().pipe(Self::from_bitslice)
	}
}

impl<O, T> Eq for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

impl<O, T> Ord for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.as_bitslice().cmp(other.as_bitslice())
	}
}

impl<O1, O2, T1, T2> PartialEq<BitBox<O2, T2>> for BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn eq(&self, other: &BitBox<O2, T2>) -> bool {
		self == other.as_bitslice()
	}
}

impl<O1, O2, T1, T2> PartialEq<BitBox<O2, T2>> for &BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn eq(&self, other: &BitBox<O2, T2>) -> bool {
		*self == other.as_bitslice()
	}
}

impl<O1, O2, T1, T2> PartialEq<BitBox<O2, T2>> for &mut BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn eq(&self, other: &BitBox<O2, T2>) -> bool {
		**self == other.as_bitslice()
	}
}

impl<O, T, Rhs> PartialEq<Rhs> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialEq<BitSlice<O, T>>,
{
	fn eq(&self, other: &Rhs) -> bool {
		other == self.as_bitslice()
	}
}

impl<O1, O2, T1, T2> PartialOrd<BitBox<O2, T2>> for BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn partial_cmp(&self, other: &BitBox<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

impl<O, T, Rhs> PartialOrd<Rhs> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialOrd<BitSlice<O, T>>,
{
	fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
		other.partial_cmp(self.as_bitslice())
	}
}

impl<'a, O1, O2, T1, T2> PartialOrd<BitBox<O2, T2>> for &'a BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn partial_cmp(&self, other: &BitBox<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

impl<'a, O1, O2, T1, T2> PartialOrd<BitBox<O2, T2>> for &'a mut BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	fn partial_cmp(&self, other: &BitBox<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

impl<O, T> AsRef<BitSlice<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

impl<O, T> AsMut<BitSlice<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn as_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<'a, O, T> From<&'a BitSlice<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(slice: &'a BitSlice<O, T>) -> Self {
		Self::from_bitslice(slice)
	}
}

impl<O, T> From<BitVec<O, T>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn from(bv: BitVec<O, T>) -> Self {
		bv.into_boxed_bitslice()
	}
}

impl<O, T> Into<Box<[T]>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<O, T> TryFrom<Box<[T]>> for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = Box<[T]>;

	fn try_from(boxed: Box<[T]>) -> Result<Self, Self::Error> {
		Self::try_from_boxed_slice(boxed)
	}
}

impl<O, T> Default for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn default() -> Self {
		Self {
			pointer: BitPtr::EMPTY.to_nonnull(),
		}
	}
}

impl<O, T> Debug for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(self, fmt)?;
		fmt.write_str(" ")?;
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Display for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Binary for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> LowerHex for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Octal for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Pointer for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.bitptr().render(fmt, "Box", None)
	}
}

impl<O, T> UpperHex for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Hash for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn hash<H>(&self, state: &mut H)
	where H: Hasher {
		self.as_bitslice().hash(state)
	}
}

/// This is not present on `Box<[T]>`, but is needed to fit into the general
/// operator implementations.
impl<O, T> IntoIterator for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type IntoIter = <crate::vec::BitVec<O, T> as IntoIterator>::IntoIter;
	type Item = <Self::IntoIter as Iterator>::Item;

	fn into_iter(self) -> Self::IntoIter {
		self.into_bitvec().into_iter()
	}
}

unsafe impl<O, T> Send for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

unsafe impl<O, T> Sync for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

impl<O, T> Unpin for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}
