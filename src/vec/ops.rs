//! Port of the `Vec<T>` operator implementations.

use core::{
	mem::ManuallyDrop,
	ops::{
		BitAnd,
		BitAndAssign,
		BitOr,
		BitOrAssign,
		BitXor,
		BitXorAssign,
		Deref,
		DerefMut,
		Index,
		IndexMut,
		Not,
	},
};

use super::BitVec;
use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitAnd<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitAndAssign<Rhs>,
{
	type Output = Self;

	#[inline(always)]
	fn bitand(mut self, rhs: Rhs) -> Self::Output {
		self &= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitAndAssign<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitAndAssign<Rhs>,
{
	#[inline(always)]
	fn bitand_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() &= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitOr<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitOrAssign<Rhs>,
{
	type Output = Self;

	#[inline(always)]
	fn bitor(mut self, rhs: Rhs) -> Self::Output {
		self |= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitOrAssign<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitOrAssign<Rhs>,
{
	#[inline(always)]
	fn bitor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() |= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitXor<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitXorAssign<Rhs>,
{
	type Output = Self;

	#[inline(always)]
	fn bitxor(mut self, rhs: Rhs) -> Self::Output {
		self ^= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Rhs> BitXorAssign<Rhs> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: BitXorAssign<Rhs>,
{
	#[inline(always)]
	fn bitxor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() ^= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Deref for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Target = BitSlice<O, T>;

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> DerefMut for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Drop for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn drop(&mut self) {
		//  Run the `Vec` destructor to deällocate the buffer.
		self.with_vec(|slot| unsafe { ManuallyDrop::drop(slot) });
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Idx> Index<Idx> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: Index<Idx>,
{
	type Output = <BitSlice<O, T> as Index<Idx>>::Output;

	#[inline(always)]
	fn index(&self, index: Idx) -> &Self::Output {
		self.as_bitslice().index(index)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T, Idx> IndexMut<Idx> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: IndexMut<Idx>,
{
	#[inline(always)]
	fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
		self.as_mut_bitslice().index_mut(index)
	}
}

/** This implementation inverts all elements in the live buffer. You cannot rely
on the value of bits in the buffer that are outside the domain of
[`BitVec::as_mut_bitslice`].
**/
#[cfg(not(tarpaulin_include))]
impl<O, T> Not for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Output = Self;

	#[inline]
	fn not(mut self) -> Self::Output {
		for elem in self.as_mut_raw_slice() {
			elem.store_value(!elem.load_value())
		}
		self
	}
}
