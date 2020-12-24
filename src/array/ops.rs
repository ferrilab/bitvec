//! Port of the `[T; N]` operator implementations.

use crate::{
	array::BitArray,
	iter::BitIter,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
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

macro_rules! bitop {
	( $(
		$trait_assign:ident :: $func_assign:ident, $trait:ident :: $func:ident;
	)+ ) => { $(
		impl<O1, O2, V1, V2> $trait <BitArray<O2, V2>> for BitArray<O1, V1>
		where
			O1: BitOrder,
			O2: BitOrder,
			V1: BitView,
			V2: BitView,
		{
			type Output = Self;

			#[inline(always)]
			fn $func (mut self, rhs: BitArray<O2, V2>) -> Self::Output {
				$trait_assign :: $func_assign (
					self.as_mut_bitslice(),
					rhs.as_bitslice(),
				);
				self
			}
		}

		impl<O1, O2, V1, V2> $trait_assign <BitArray<O2, V2>>
		for BitArray<O1, V1>
		where
			O1: BitOrder,
			O2: BitOrder,
			V1: BitView,
			V2: BitView,
		{
			#[inline(always)]
			fn $func_assign(&mut self, rhs: BitArray<O2, V2>) {
				$trait_assign :: $func_assign (
					self.as_mut_bitslice(),
					rhs.as_bitslice(),
				);
			}
		}

		impl<'a, O1, O2, V, T> $trait <&'a BitSlice<O2, T>> for BitArray<O1, V>
		where
			O1: BitOrder,
			O2: BitOrder,
			V: BitView,
			T: BitStore,
		{
			type Output = Self;

			#[inline(always)]
			fn $func (mut self, rhs: &'a BitSlice<O2, T>) -> Self::Output {
				$trait_assign :: $func_assign (self.as_mut_bitslice(), rhs);
				self
			}
		}

		impl<'a, O1, O2, V, T> $trait_assign <&'a BitSlice<O2, T>>
		for BitArray<O1, V>
		where
			O1: BitOrder,
			O2: BitOrder,
			V: BitView,
			T: BitStore,
		{
			#[inline(always)]
			fn $func_assign (&mut self, rhs: &'a BitSlice<O2, T>) {
				$trait_assign :: $func_assign (self.as_mut_bitslice(), rhs);
			}
		}

		impl<O1, O2, T, V> $trait_assign <BitArray<O2, V>> for BitSlice<O1, T>
		where
			O1: BitOrder,
			O2: BitOrder,
			T: BitStore,
			V: BitView,
		{
			#[inline(always)]
			fn $func_assign (&mut self, rhs: BitArray<O2, V>) {
				$trait_assign :: $func_assign (self, rhs.as_bitslice())
			}
		}

		impl<O, V, I> $trait <BitIter<I>> for BitArray<O, V>
		where
			O: BitOrder,
			V: BitView,
			I: Iterator<Item = bool>,
		{
			type Output = Self;

			#[inline]
			fn $func (mut self, rhs: BitIter<I>) -> Self::Output {
				$trait_assign :: $func_assign(&mut self, rhs);
				self
			}
		}

		impl<O, V, I> $trait <BitArray<O, V>> for BitIter<I>
		where
			O: BitOrder,
			V: BitView,
			I: Iterator<Item = bool>,
		{
			type Output = BitArray<O, V>;

			#[inline(always)]
			fn $func (self, rhs: BitArray<O, V>) -> Self::Output {
				$trait :: $func (rhs, self)
			}
		}

		impl<O, V, I> $trait_assign <BitIter<I>> for BitArray<O, V>
		where
			O: BitOrder,
			V: BitView,
			I: Iterator<Item = bool>,
		{
			#[inline]
			fn $func_assign (&mut self, rhs: BitIter<I>) {
				$trait_assign :: $func_assign (self.as_mut_bitslice(), rhs)
			}
		}
	)+ };
}

bitop! {
	BitAndAssign::bitand_assign, BitAnd::bitand;
	BitOrAssign::bitor_assign, BitOr::bitor;
	BitXorAssign::bitxor_assign, BitXor::bitxor;
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Deref for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
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
	V: BitView,
{
	#[inline(always)]
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

impl<O, V, Idx> Index<Idx> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	BitSlice<O, V::Store>: Index<Idx>,
{
	type Output = <BitSlice<O, V::Store> as Index<Idx>>::Output;

	#[inline]
	fn index(&self, index: Idx) -> &Self::Output {
		self.as_bitslice().index(index)
	}
}

impl<O, V, Idx> IndexMut<Idx> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
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
	V: BitView,
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
