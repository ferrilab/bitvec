/*! General trait implementations for `BitBox`

The operator traits are defined in the `ops` module.
!*/

use super::*;

use alloc::{
	borrow::{
		Borrow,
		BorrowMut,
	},
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
};

impl<C, T> Borrow<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow(&self) -> &BitSlice<C, T> {
		self.as_bitslice()
	}
}

impl<C, T> BorrowMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn borrow_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_mut_bitslice()
	}
}

impl<C, T> Clone for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn clone(&self) -> Self {
		let new_box = self.do_with_box(Clone::clone);
		let mut pointer = self.pointer;
		unsafe { pointer.set_pointer(new_box.as_ptr()); }
		mem::forget(new_box);
		Self {
			_cursor: PhantomData,
			pointer,
		}
	}
}

impl<C, T> Eq for BitBox<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.as_bitslice().cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.as_bitslice().eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		self.as_bitslice().eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitBox<C, D>) -> bool {
		self.eq(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs.as_bitslice())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitBox<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		self.as_bitslice().partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<BitBox<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitBox<C, D>) -> Option<Ordering> {
		self.partial_cmp(rhs.as_bitslice())
	}
}

impl<C, T> AsMut<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut BitSlice<C, T> {
		self.as_mut_bitslice()
	}
}

impl<C, T> AsMut<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_bitslice().as_mut()
	}
}

impl<C, T> AsRef<BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &BitSlice<C, T> {
		self.as_bitslice()
	}
}

impl<C, T> AsRef<[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn as_ref(&self) -> &[T] {
		self.as_bitslice().as_ref()
	}
}

impl<C, T> From<&BitSlice<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &BitSlice<C, T>) -> Self {
		Self::from_bitslice(src)
	}
}

impl<C, T> From<&[T]> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: &[T]) -> Self {
		Self::from_slice(src)
	}
}

impl<C, T> From<BitVec<C, T>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: BitVec<C, T>) -> Self {
		src.into_boxed_bitslice()
	}
}

impl<C, T> From<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn from(src: Box<[T]>) -> Self {
		Self::from_boxed_slice(src)
	}
}

impl<C, T> Into<Box<[T]>> for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn into(self) -> Box<[T]> {
		self.into_boxed_slice()
	}
}

impl<C, T> Default for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn default() -> Self {
		Self {
			_cursor: PhantomData,
			pointer: BitPtr::default(),
		}
	}
}

impl<C, T> Binary for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> Debug for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("BitBox<")?;
		fmt.write_str(C::TYPENAME)?;
		fmt.write_str(", ")?;
		fmt.write_str(T::TYPENAME)?;
		fmt.write_str("> ")?;
		Display::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> Display for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> LowerHex for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> Octal for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> UpperHex for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

impl<C, T> Hash for BitBox<C, T>
where C: Cursor, T: BitStore {
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		self.as_bitslice().hash(hasher)
	}
}

/// `BitBox` is safe to move across thread boundaries, as is `&mut BitBox`.
unsafe impl<C, T> Send for BitBox<C, T>
where C: Cursor, T: BitStore {}

/// `&BitBox` is safe to move across thread boundaries.
unsafe impl<C, T> Sync for BitBox<C, T>
where C: Cursor, T: BitStore {}
