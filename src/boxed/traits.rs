/*! General trait implementations for `BitBox`

The operator traits are defined in the `ops` module.
!*/

use crate::{
	boxed::BitBox,
	order::BitOrder,
	pointer::BitPtr,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
	},
	boxed::Box,
};

use core::{
	cmp::Ordering,
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
	marker::PhantomData,
	mem,
};

impl<O, T> Borrow<BitSlice<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn borrow(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

impl<O, T> BorrowMut<BitSlice<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn borrow_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<O, T> Clone for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn clone(&self) -> Self {
		let new_box = self.do_with_box(Clone::clone);
		let mut pointer = self.pointer;
		unsafe { pointer.set_pointer(new_box.as_ptr()); }
		mem::forget(new_box);
		Self {
			_order: PhantomData,
			pointer,
		}
	}
}

impl<O, T> Eq for BitBox<O, T>
where O: BitOrder, T: BitStore {}

impl<O, T> Ord for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bitslice().cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitBox<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.as_bitslice().eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitBox<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitBox<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitBox<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitSlice<A, B>
where A: BitOrder, B: BitStore, C: BitOrder, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

impl<O, T> AsMut<BitSlice<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<O, T> {
		self.as_mut_bitslice()
	}
}

impl<O, T> AsMut<[T]> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_bitslice().as_mut()
	}
}

impl<O, T> AsRef<BitSlice<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn as_ref(&self) -> &BitSlice<O, T> {
		self.as_bitslice()
	}
}

impl<O, T> AsRef<[T]> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_bitslice().as_ref()
	}
}

impl<O, T> From<&BitSlice<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: &BitSlice<O, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<O, T> From<&[T]> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<O, T> From<BitVec<O, T>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: BitVec<O, T>) -> Self {
		src.into_boxed_bitslice()
	}
}

impl<O, T> From<Box<[T]>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_slice(src)
	}
}

impl<O, T> Into<Box<[T]>> for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<O, T> Default for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn default() -> Self {
		Self {
			_order: PhantomData,
			pointer: BitPtr::default(),
		}
	}
}

impl<O, T> Binary for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Debug for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("BitBox<")?;
		fmt.write_str(O::TYPENAME)?;
		fmt.write_str(", ")?;
		fmt.write_str(T::TYPENAME)?;
		fmt.write_str("> ")?;
		Display::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Display for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> LowerHex for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Octal for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> UpperHex for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, T> Hash for BitBox<O, T>
where O: BitOrder, T: BitStore {
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		self.as_bitslice().hash(hasher)
	}
}

/// `BitBox` is safe to move across thread boundaries, as is `&mut BitBox`.
unsafe impl<O, T> Send for BitBox<O, T>
where O: BitOrder, T: BitStore {}

/// `&BitBox` is safe to move across thread boundaries.
unsafe impl<O, T> Sync for BitBox<O, T>
where O: BitOrder, T: BitStore {}
