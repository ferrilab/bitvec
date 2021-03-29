//! Port of the `[T; N]` operator implementations.

use core::ops::{
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
};

use super::BitArray;
use crate::{
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	view::BitViewSized,
};

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitAnd<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitAndAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitand(mut self, rhs: Rhs) -> Self::Output {
		self &= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitAndAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitAndAssign<Rhs>,
{
	#[inline]
	fn bitand_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() &= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitOr<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitOrAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitor(mut self, rhs: Rhs) -> Self::Output {
		self |= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitOrAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitOrAssign<Rhs>,
{
	#[inline]
	fn bitor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() |= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitXor<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitXorAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitxor(mut self, rhs: Rhs) -> Self::Output {
		self ^= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitXorAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: BitXorAssign<Rhs>,
{
	#[inline]
	fn bitxor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() ^= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Deref for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	type Target = BitSlice<O, V::Store>;

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> DerefMut for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	#[inline(always)]
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Idx> Index<Idx> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: Index<Idx>,
{
	type Output = <BitSlice<O, V::Store> as Index<Idx>>::Output;

	#[inline]
	fn index(&self, index: Idx) -> &Self::Output {
		self.as_bitslice().index(index)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Idx> IndexMut<Idx> for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
	BitSlice<O, V::Store>: IndexMut<Idx>,
{
	#[inline]
	fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
		self.as_mut_bitslice().index_mut(index)
	}
}

impl<O, V> Not for BitArray<O, V>
where
	O: BitOrder,
	V: BitViewSized,
{
	type Output = Self;

	#[inline]
	fn not(mut self) -> Self::Output {
		for elem in self.as_mut_raw_slice() {
			elem.store_value(!elem.load_value());
		}
		self
	}
}
