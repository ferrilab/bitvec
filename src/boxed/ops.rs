//! Operator trait implementations.

use crate::{
	boxed::BitBox,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use alloc::boxed::Box;

use core::{
	ops::{
		Add,
		AddAssign,
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
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
		Neg,
		Not,
		Shl,
		ShlAssign,
		Shr,
		ShrAssign,
	},
	slice,
};

impl<O, T> Add<Self> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

impl<O, T> AddAssign for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn add_assign(&mut self, addend: Self) {
		self.as_mut_bitslice().add_assign(addend.as_bitslice().iter().copied())
	}
}

impl<O, T, I> BitAnd<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

impl<O, T, I> BitAndAssign<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitand_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitand_assign(rhs);
	}
}

impl<O, T, I> BitOr<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

impl<O, T, I> BitOrAssign<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitor_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitor_assign(rhs);
	}
}

impl<O, T, I> BitXor<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	type Output = Self;

	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

impl<O, T, I> BitXorAssign<I> for BitBox<O, T>
where O: BitOrder, T: BitStore, I: IntoIterator<Item=bool> {
	fn bitxor_assign(&mut self, rhs: I) {
		self.as_mut_bitslice().bitxor_assign(rhs);
	}
}

impl<O, T> Deref for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Target = BitSlice<O, T>;

	fn deref(&self) -> &Self::Target {
		self.as_bitslice()
	}
}

impl<O, T> DerefMut for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.as_mut_bitslice()
	}
}

impl<O, T> Drop for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn drop(&mut self) {
		let bp = self.bitptr();
		let ptr = bp.pointer().w();
		let len = bp.elements();
		let slice = unsafe { slice::from_raw_parts_mut(ptr, len) };
		drop(unsafe { Box::from_raw(slice as *mut [_]) })
	}
}

impl<O, T> Index<usize> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = bool;

	fn index(&self, index: usize) -> &Self::Output {
		&self.as_bitslice()[index]
	}
}

impl<O, T> Index<Range<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: Range<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<Range<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeFrom<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeFrom<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeFull> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, _: RangeFull) -> &Self::Output {
		self.as_bitslice()
	}
}

impl<O, T> IndexMut<RangeFull> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
		self.as_mut_bitslice()
	}
}

impl<O, T> Index<RangeInclusive<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeInclusive<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeTo<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeTo<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeTo<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Index<RangeToInclusive<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = BitSlice<O, T>;

	fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
		&self.as_bitslice()[range]
	}
}

impl<O, T> IndexMut<RangeToInclusive<usize>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn index_mut(
		&mut self,
		range: RangeToInclusive<usize>,
	) -> &mut Self::Output {
		&mut self.as_mut_bitslice()[range]
	}
}

impl<O, T> Neg for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().neg();
		self
	}
}

impl<O, T> Not for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn not(mut self) -> Self::Output {
		let _ = self.as_mut_bitslice().not();
		self
	}
}

impl<O, T> Shl<usize> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

impl<O, T> ShlAssign<usize> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn shl_assign(&mut self, shamt: usize) {
		self.as_mut_bitslice().shl_assign(shamt);
	}
}

impl<O, T> Shr<usize> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	type Output = Self;

	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

impl<O, T> ShrAssign<usize> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn shr_assign(&mut self, shamt: usize) {
		self.as_mut_bitslice().shr_assign(shamt);
	}
}
