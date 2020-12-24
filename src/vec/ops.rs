//! Port of the `Vec<T>` operator implementations.

use crate::{
	iter::BitIter,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

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

macro_rules! bitop {
	( $(
		$trait_assign:ident :: $func_assign:ident, $trait:ident :: $func:ident;
	)+ ) => { $(
		impl<O1, O2, T1, T2> $trait <BitVec<O2, T2>> for BitVec<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			type Output = Self;

			#[inline(always)]
			fn $func (mut self, rhs: BitVec<O2, T2>) -> Self::Output {
				$trait_assign :: $func_assign (
					self.as_mut_bitslice(),
					rhs.as_bitslice(),
				);
				self
			}
		}

		impl<O1, O2, T1, T2> $trait_assign <BitVec<O2, T2>>
		for BitVec<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			#[inline(always)]
			fn $func_assign(&mut self, rhs: BitVec<O2, T2>) {
				$trait_assign :: $func_assign (
					self.as_mut_bitslice(),
					rhs.as_bitslice(),
				);
			}
		}

		impl<'a, O1, O2, T1, T2> $trait <&'a BitSlice<O2, T2>> for BitVec<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			type Output = Self;

			#[inline(always)]
			fn $func (mut self, rhs: &'a BitSlice<O2, T2>) -> Self::Output {
				$trait_assign :: $func_assign (self.as_mut_bitslice(), rhs);
				self
			}
		}

		impl<'a, O1, O2, T1, T2> $trait_assign <&'a BitSlice<O2, T2>>
		for BitVec<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			#[inline(always)]
			fn $func_assign (&mut self, rhs: &'a BitSlice<O2, T2>) {
				$trait_assign :: $func_assign (self.as_mut_bitslice(), rhs);
			}
		}

		impl<O1, O2, T1, T2> $trait_assign <BitVec<O2, T2>> for BitSlice<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			#[inline(always)]
			fn $func_assign (&mut self, rhs: BitVec<O2, T2>) {
				$trait_assign :: $func_assign (self, rhs.as_bitslice())
			}
		}

		impl<O, T, I> $trait <BitIter<I>> for BitVec<O, T>
		where
			O: BitOrder,
			T: BitStore,
			I: Iterator<Item = bool>,
		{
			type Output = Self;

			#[inline(always)]
			fn $func (mut self, rhs: BitIter<I>) -> Self::Output {
				$trait_assign :: $func_assign(&mut self, rhs);
				self
			}
		}

		impl<O, T, I> $trait <BitVec<O, T>> for BitIter<I>
		where
			O: BitOrder,
			T: BitStore,
			I: Iterator<Item = bool>,
		{
			type Output = BitVec<O, T>;

			#[inline(always)]
			fn $func (self, rhs: BitVec<O, T>) -> Self::Output {
				$trait :: $func (rhs, self)
			}
		}

		impl<O, T, I> $trait_assign <BitIter<I>> for BitVec<O, T>
		where
			O: BitOrder,
			T: BitStore,
			I: Iterator<Item = bool>,
		{
			#[inline(always)]
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

impl<O, T> Deref for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Target = BitSlice<O, T>;

	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

impl<O, T> DerefMut for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

impl<O, T> Drop for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn drop(&mut self) {
		//  Run the `Vec` destructor to deällocate the buffer.
		self.with_vec(|slot| unsafe { ManuallyDrop::drop(slot) });
	}
}

impl<O, T, Idx> Index<Idx> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: Index<Idx>,
{
	type Output = <BitSlice<O, T> as Index<Idx>>::Output;

	fn index(&self, index: Idx) -> &Self::Output {
		self.as_bitslice().index(index)
	}
}

impl<O, T, Idx> IndexMut<Idx> for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T>: IndexMut<Idx>,
{
	fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
		self.as_mut_bitslice().index_mut(index)
	}
}

/** This implementation inverts all elements in the live buffer. You cannot rely
on the value of bits in the buffer that are outside the domain of
`BitVec::as_mit_bitslice`.
**/
impl<O, T> Not for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Output = Self;

	fn not(mut self) -> Self::Output {
		for elem in self.as_mut_raw_slice() {
			elem.store_value(!elem.load_value())
		}
		self
	}
}
