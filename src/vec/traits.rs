//! Non-operator trait implementations.

use alloc::vec::Vec;
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
		UpperHex,
	},
	hash::{
		Hash,
		Hasher,
	},
};

use tap::Tap;

use super::BitVec;
use crate::{
	boxed::BitBox,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

#[cfg(not(tarpaulin_include))]
impl<O, T> Borrow<BitSlice<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn borrow(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> BorrowMut<BitSlice<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn borrow_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<O, T> Clone for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		Self::new().tap_mut(|bv| bv.clone_from(self))
	}

	fn clone_from(&mut self, source: &Self) {
		self.clear();
		self.resize(source.len(), false);
		self.copy_from_bitslice(source.as_bitslice());
	}
}

impl<O, T> Eq for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Ord for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.as_bitslice().cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<O1, O2, T1, T2> PartialEq<BitVec<O2, T2>> for BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitVec<O2, T2>) -> bool {
		self == other.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O1, O2, T1, T2> PartialEq<BitVec<O2, T2>> for &BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitVec<O2, T2>) -> bool {
		*self == other.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O1, O2, T1, T2> PartialEq<BitVec<O2, T2>> for &mut BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitVec<O2, T2>) -> bool {
		**self == other.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> PartialEq<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialEq<BitSlice<O, T>>,
{
	#[inline]
	fn eq(&self, other: &Rhs) -> bool {
		other == self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O1, O2, T1, T2> PartialOrd<BitVec<O2, T2>> for BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(&self, other: &BitVec<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O1, O2, T1, T2> PartialOrd<BitVec<O2, T2>> for &'a BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(&self, other: &BitVec<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O1, O2, T1, T2> PartialOrd<BitVec<O2, T2>> for &'a mut BitSlice<O1, T1>
where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(&self, other: &BitVec<O2, T2>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> PartialOrd<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialOrd<BitSlice<O, T>>,
{
	#[inline]
	fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
		other.partial_cmp(self.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> AsRef<BitSlice<O, T>> for BitVec<O, T>
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
impl<O, T> AsMut<BitSlice<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn as_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> From<&'a BitSlice<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn from(slice: &'a BitSlice<O, T>) -> Self {
		Self::from_bitslice(slice)
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, T> From<&'a mut BitSlice<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn from(slice: &'a mut BitSlice<O, T>) -> Self {
		Self::from_bitslice(slice)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> From<BitBox<O, T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn from(boxed: BitBox<O, T>) -> Self {
		boxed.into_bitvec()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> From<BitVec<O, T>> for Vec<T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn from(bv: BitVec<O, T>) -> Self {
		bv.into_vec()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> TryFrom<Vec<T>> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Error = Vec<T>;

	#[inline(always)]
	fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
		Self::try_from_vec(vec)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Default for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn default() -> Self {
		Self::new()
	}
}

impl<O, T> Debug for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.as_bitspan().render(fmt, "Vec", &[(
			"capacity",
			&self.capacity() as &dyn Debug,
		)])?;
		fmt.write_str(" ")?;
		Display::fmt(self, fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Display for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Binary for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> LowerHex for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Octal for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> UpperHex for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Hash for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn hash<H>(&self, state: &mut H)
	where H: Hasher {
		self.as_bitslice().hash(state)
	}
}

unsafe impl<O, T> Send for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

unsafe impl<O, T> Sync for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

impl<O, T> Unpin for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
}
