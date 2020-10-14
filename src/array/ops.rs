//! Port of the `[T; N]` operator implementations.

use crate::{
	array::BitArray,
	order::BitOrder,
	slice::BitSlice,
	view::BitView,
};

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

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitAnd<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Mem>: BitAndAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitand(mut self, rhs: Rhs) -> Self::Output {
		*self.as_mut_bitslice() &= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitAndAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Mem>: BitAndAssign<Rhs>,
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
	V: BitView,
	BitSlice<O, V::Mem>: BitOrAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitor(mut self, rhs: Rhs) -> Self::Output {
		*self.as_mut_bitslice() |= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitOrAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Mem>: BitOrAssign<Rhs>,
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
	V: BitView,
	BitSlice<O, V::Mem>: BitXorAssign<Rhs>,
{
	type Output = Self;

	#[inline]
	fn bitxor(mut self, rhs: Rhs) -> Self::Output {
		*self.as_mut_bitslice() ^= rhs;
		self
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> BitXorAssign<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Mem>: BitXorAssign<Rhs>,
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
	V: BitView,
{
	type Target = BitSlice<O, V::Mem>;

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> DerefMut for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
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
	V: BitView,
	BitSlice<O, V::Mem>: Index<Idx>,
{
	type Output = <BitSlice<O, V::Mem> as Index<Idx>>::Output;

	#[inline]
	fn index(&self, index: Idx) -> &Self::Output {
		self.as_bitslice().index(index)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Idx> IndexMut<Idx> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Mem>: IndexMut<Idx>,
{
	#[inline]
	fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
		self.as_mut_bitslice().index_mut(index)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Not for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type Output = Self;

	#[inline]
	fn not(mut self) -> Self::Output {
		for elem in self.as_mut_slice() {
			*elem = !*elem;
		}
		self
	}
}
