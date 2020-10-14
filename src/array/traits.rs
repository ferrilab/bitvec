//! Non-operator trait implementations.

use crate::{
	array::BitArray,
	index::BitIdx,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	view::BitView,
};

use core::{
	borrow::{
		Borrow,
		BorrowMut,
	},
	cmp,
	convert::TryFrom,
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
};

#[cfg(not(tarpaulin_include))]
impl<O, V> Borrow<BitSlice<O, V::Mem>> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn borrow(&self) -> &BitSlice<O, V::Mem> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> BorrowMut<BitSlice<O, V::Mem>> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn borrow_mut(&mut self) -> &mut BitSlice<O, V::Mem> {
		self.as_mut_bitslice()
	}
}

impl<O, V> Eq for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Ord for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.as_bitslice().cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, T> PartialEq<BitArray<O, V>> for BitSlice<O, T>
where
	O: BitOrder,
	V: BitView,
	T: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitArray<O, V>) -> bool {
		self == other.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> PartialEq<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	Rhs: ?Sized,
	BitSlice<O, V::Mem>: PartialEq<Rhs>,
{
	#[inline]
	fn eq(&self, other: &Rhs) -> bool {
		self.as_bitslice() == other
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, T> PartialOrd<BitArray<O, V>> for BitSlice<O, T>
where
	O: BitOrder,
	V: BitView,
	T: BitStore,
{
	#[inline]
	fn partial_cmp(&self, other: &BitArray<O, V>) -> Option<cmp::Ordering> {
		self.partial_cmp(other.as_bitslice())
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V, Rhs> PartialOrd<Rhs> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
	Rhs: ?Sized,
	BitSlice<O, V::Mem>: PartialOrd<Rhs>,
{
	#[inline]
	fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
		self.as_bitslice().partial_cmp(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> AsRef<BitSlice<O, V::Mem>> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn as_ref(&self) -> &BitSlice<O, V::Mem> {
		self.as_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> AsMut<BitSlice<O, V::Mem>> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn as_mut(&mut self) -> &mut BitSlice<O, V::Mem> {
		self.as_mut_bitslice()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> From<V> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn from(data: V) -> Self {
		Self::new(data)
	}
}

impl<'a, O, V> TryFrom<&'a BitSlice<O, V::Mem>> for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type Error = TryFromBitSliceError<'a, O, V::Mem>;

	#[inline]
	fn try_from(src: &'a BitSlice<O, V::Mem>) -> Result<Self, Self::Error> {
		if src.len() != V::const_bits() {
			return Self::Error::err(src);
		}
		let mut out = Self::zeroed();
		out.copy_from_bitslice(src);
		Ok(out)
	}
}

impl<'a, O, V> TryFrom<&'a BitSlice<O, V::Mem>> for &'a BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type Error = TryFromBitSliceError<'a, O, V::Mem>;

	#[inline]
	fn try_from(src: &'a BitSlice<O, V::Mem>) -> Result<Self, Self::Error> {
		let bitptr = src.bitptr();
		//  This pointer cast can only happen if the slice is exactly as long as
		//  the array, and is aligned to the front of the element.
		if src.len() != V::const_bits() || bitptr.head() != BitIdx::ZERO {
			return Self::Error::err(src);
		}
		Ok(unsafe { &*(bitptr.pointer().to_const() as *const BitArray<O, V>) })
	}
}

impl<'a, O, V> TryFrom<&'a mut BitSlice<O, V::Mem>> for &'a mut BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type Error = TryFromBitSliceError<'a, O, V::Mem>;

	#[inline]
	fn try_from(src: &'a mut BitSlice<O, V::Mem>) -> Result<Self, Self::Error> {
		let bitptr = src.bitptr();
		if src.len() != V::const_bits() || bitptr.head() != BitIdx::ZERO {
			return Self::Error::err(&*src);
		}
		Ok(unsafe { &mut *(bitptr.pointer().to_mut() as *mut BitArray<O, V>) })
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Default for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline(always)]
	fn default() -> Self {
		Self::zeroed()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Binary for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

impl<O, V> Debug for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.bitptr().render(fmt, "Array", None)?;
		fmt.write_str(" ")?;
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Display for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> LowerHex for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Octal for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> UpperHex for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(self.as_bitslice(), fmt)
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, V> Hash for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	#[inline]
	fn hash<H>(&self, hasher: &mut H)
	where H: Hasher {
		self.as_bitslice().hash(hasher)
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, V> IntoIterator for &'a BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type IntoIter = <&'a BitSlice<O, V::Mem> as IntoIterator>::IntoIter;
	type Item = <&'a BitSlice<O, V::Mem> as IntoIterator>::Item;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.as_bitslice().into_iter()
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, O, V> IntoIterator for &'a mut BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
	type IntoIter = <&'a mut BitSlice<O, V::Mem> as IntoIterator>::IntoIter;
	type Item = <&'a mut BitSlice<O, V::Mem> as IntoIterator>::Item;

	#[inline]
	fn into_iter(self) -> Self::IntoIter {
		self.as_mut_bitslice().into_iter()
	}
}

impl<O, V> Unpin for BitArray<O, V>
where
	O: BitOrder,
	V: BitView,
{
}

/** The error type returned when a conversion from a [`BitSlice`] to a
[`BitArray`] fails.

[`BitArray`]: crate::array::BitArray
[`BitSlice`]: crate::slice::BitSlice
**/
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct TryFromBitSliceError<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	inner: &'a BitSlice<O, T>,
}

impl<'a, O, T> TryFromBitSliceError<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn err<A>(inner: &'a BitSlice<O, T>) -> Result<A, Self> {
		Err(Self { inner })
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Debug for TryFromBitSliceError<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_struct("TryFromBitSliceError")
			.field("inner", &self.inner)
			.finish()
	}
}

#[cfg(not(tarpaulin_include))]
impl<O, T> Display for TryFromBitSliceError<'_, O, T>
where
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_fmt(format_args!(
			"could not convert bitslice to bitarray: {:?}",
			self.inner
		))
	}
}

#[cfg(feature = "std")]
impl<'a, O, T> std::error::Error for TryFromBitSliceError<'a, O, T>
where
	O: BitOrder,
	T: BitStore,
{
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;
	use core::convert::TryInto;

	#[test]
	fn convert() {
		let arr: BitArray<Lsb0, _> = 2u8.into();
		assert!(arr.any());

		let bits = bits![Msb0, u8; 1; 128];
		let arr: BitArray<Msb0, [u8; 16]> = bits.try_into().unwrap();
		assert!(arr.all());

		let bits = bits![Lsb0, u32; 0; 64];
		let arr: &BitArray<Lsb0, [u32; 2]> = bits.try_into().unwrap();
		assert!(arr.not_any());

		let bits = bits![mut Msb0, u16; 0; 64];
		let arr: &mut BitArray<Msb0, [u16; 4]> = bits.try_into().unwrap();
		assert!(arr.not_any());

		let bits = bits![mut LocalBits, usize; 0; 4];
		let bit_arr: Result<&BitArray<LocalBits, usize>, _> =
			(&*bits).try_into();
		assert!(bit_arr.is_err());
		let bit_arr: Result<&mut BitArray<LocalBits, usize>, _> =
			bits.try_into();
		assert!(bit_arr.is_err());
	}

	#[test]
	#[cfg(feature = "std")]
	fn format() {
		let text = format!("{:?}", bitarr![Msb0, u8; 0, 1, 0, 0]);
		assert!(
			text.starts_with("BitArray<bitvec::order::Msb0, u8> { addr: 0x"),
			"{}",
			text
		);
		assert!(
			text.ends_with(", head: 000, bits: 8 } [01000000]"),
			"{}",
			text
		);
	}
}
