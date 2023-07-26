//! General trait implementations for bit-sets.

use core::{
	cmp,
	fmt::{
		self,
		Debug,
		Formatter,
	},
	hash::Hasher,
	marker::Unpin,
};

use super::BitSet;
use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

#[cfg(not(tarpaulin_include))]
impl<T, O> Clone for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.clone(),
		}
	}
}

impl<T, O> Eq for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
}

#[cfg(not(tarpaulin_include))]
impl<T, O> Ord for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.iter().cmp(other.iter())
	}
}

#[cfg(not(tarpaulin_include))]
impl<T1, T2, O1, O2> PartialEq<BitSet<T2, O2>> for BitSet<T1, O1>
where
	T1: BitStore,
	T2: BitStore,
	O1: BitOrder,
	O2: BitOrder,
{
	#[inline]
	fn eq(&self, other: &BitSet<T2, O2>) -> bool {
		self.shrunken() == other.shrunken()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T1, T2, O1, O2> PartialOrd<BitSet<T2, O2>> for BitSet<T1, O1>
where
	T1: BitStore,
	T2: BitStore,
	O1: BitOrder,
	O2: BitOrder,
{
	#[inline]
	fn partial_cmp(&self, other: &BitSet<T2, O2>) -> Option<cmp::Ordering> {
		Some(self.iter().cmp(other.iter()))
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsRef<BitSlice<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_ref(&self) -> &BitSlice<T, O> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsMut<BitSlice<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_mut(&mut self) -> &mut BitSlice<T, O> {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsRef<BitVec<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_ref(&self) -> &BitVec<T, O> {
		self.as_bitvec()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsMut<BitVec<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_mut(&mut self) -> &mut BitVec<T, O> {
		self.as_mut_bitvec()
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsRef<BitSet<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_ref(&self) -> &Self {
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> AsMut<BitSet<T, O>> for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn as_mut(&mut self) -> &mut Self {
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<T, O> Default for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn default() -> Self {
		Self::new()
	}
}

impl<T, O> Debug for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_set().entries(self.iter()).finish()
	}
}

unsafe impl<T, O> Send for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
}

unsafe impl<T, O> Sync for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
}

impl<T, O> Unpin for BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
}

/*
impl<T, O> BitAnd<&BitSet<T, O>> for &BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	type Output = BitSet<T, O>;

	#[inline]
	fn bitand(self, rhs: &BitSet<T, O>) -> BitSet<T, O> {
		BitSet::from_iter(self.intersection(rhs))
	}
}

impl<T, O> BitOr<&BitSet<T, O>> for &BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	type Output = BitSet<T, O>;

	#[inline]
	fn bitor(self, rhs: &BitSet<T, O>) -> BitSet<T, O> {
		BitSet::from_iter(self.union(rhs))
	}
}
impl<T, O> BitXor<&BitSet<T, O>> for &BitSet<T, O>
where
	T: BitStore,
	O: BitOrder,
{
	type Output = BitSet<T, O>;

	#[inline]
	fn bitxor(self, rhs: &BitSet<T, O>) -> BitSet<T, O> {
		BitSet::from_iter(self.symmetric_difference(rhs))
	}
}
*/
