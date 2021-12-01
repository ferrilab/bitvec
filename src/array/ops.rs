//! Operator trait implementations for bit-arrays.

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
impl<A, O> BitAndAssign<BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitand_assign(&mut self, rhs: BitArray<A, O>) {
		*self &= rhs.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, O> BitAndAssign<&BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitand_assign(&mut self, rhs: &BitArray<A, O>) {
		*self &= rhs.as_bitslice()
	}
}

impl<A, O, Rhs> BitAnd<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitAndAssign<Rhs>,
{
	type Output = Self;

	fn bitand(mut self, rhs: Rhs) -> Self::Output {
		self &= rhs;
		self
	}
}

impl<A, O, Rhs> BitAndAssign<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitAndAssign<Rhs>,
{
	fn bitand_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() &= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, O> BitOrAssign<BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitor_assign(&mut self, rhs: BitArray<A, O>) {
		*self |= rhs.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, O> BitOrAssign<&BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitor_assign(&mut self, rhs: &BitArray<A, O>) {
		*self |= rhs.as_bitslice()
	}
}

impl<A, O, Rhs> BitOr<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitOrAssign<Rhs>,
{
	type Output = Self;

	fn bitor(mut self, rhs: Rhs) -> Self::Output {
		self |= rhs;
		self
	}
}

impl<A, O, Rhs> BitOrAssign<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitOrAssign<Rhs>,
{
	fn bitor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() |= rhs;
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, O> BitXorAssign<BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitxor_assign(&mut self, rhs: BitArray<A, O>) {
		*self ^= rhs.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<A, O> BitXorAssign<&BitArray<A, O>> for BitSlice<A::Store, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn bitxor_assign(&mut self, rhs: &BitArray<A, O>) {
		*self ^= rhs.as_bitslice()
	}
}

impl<A, O, Rhs> BitXor<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitXorAssign<Rhs>,
{
	type Output = Self;

	fn bitxor(mut self, rhs: Rhs) -> Self::Output {
		self ^= rhs;
		self
	}
}

impl<A, O, Rhs> BitXorAssign<Rhs> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: BitXorAssign<Rhs>,
{
	fn bitxor_assign(&mut self, rhs: Rhs) {
		*self.as_mut_bitslice() ^= rhs;
	}
}

impl<A, O> Deref for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	type Target = BitSlice<A::Store, O>;

	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

impl<A, O> DerefMut for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

impl<A, O, Idx> Index<Idx> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: Index<Idx>,
{
	type Output = <BitSlice<A::Store, O> as Index<Idx>>::Output;

	fn index(&self, index: Idx) -> &Self::Output {
		&self.as_bitslice()[index]
	}
}

impl<A, O, Idx> IndexMut<Idx> for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
	BitSlice<A::Store, O>: IndexMut<Idx>,
{
	fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[index]
	}
}

impl<A, O> Not for BitArray<A, O>
where
	A: BitViewSized,
	O: BitOrder,
{
	type Output = Self;

	fn not(mut self) -> Self::Output {
		for elem in self.as_raw_mut_slice() {
			elem.store_value(!elem.load_value());
		}
		self
	}
}
