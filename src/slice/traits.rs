/*! General trait implementations for `BitSlice`.

The operator traits are defined in the `ops` module.
!*/

use super::*;

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
	hint::unreachable_unchecked,
};

#[cfg(feature = "alloc")]
use crate::{
	vec::BitVec,
};

#[cfg(feature = "alloc")]
impl<C, T> ToOwned for BitSlice<C, T>
where C: Cursor, T: BitStore {
	type Owned = BitVec<C, T>;

	fn to_owned(&self) -> Self::Owned {
		BitVec::from_bitslice(self)
	}
}

impl<C, T> Eq for BitSlice<C, T>
where C: Cursor, T: BitStore {}

impl<C, T> Ord for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn cmp(&self, rhs: &Self) -> Ordering {
		self.partial_cmp(rhs)
			//  `BitSlice` has a total ordering, and never returns `None`.
			.unwrap_or_else(|| unsafe { unreachable_unchecked() })
	}
}

/** Tests if two `BitSlice`s are semantically — not bitwise — equal.

It is valid to compare two slices of different cursor or element types.

The equality condition requires that they have the same number of total bits and
that each pair of bits in semantic order are identical.
**/
impl<A, B, C, D> PartialEq<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performas a comparison by `==`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// If the two slices are equal, by comparing the lengths and bit values at
	/// each semantic index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let lsrc = [8u8, 16, 32, 0];
	/// let rsrc = 0x10_08_04_00u32;
	/// let lbits = lsrc.bits::<LittleEndian>();
	/// let rbits = rsrc.bits::<BigEndian>();
	///
	/// assert_eq!(lbits, rbits);
	/// ```
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		if self.len() != rhs.len() {
			return false;
		}
		self.iter().zip(rhs.iter()).all(|(l, r)| l == r)
	}
}

impl<A, B, C, D> PartialEq<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &BitSlice<C, D>) -> bool {
		(*self).eq(rhs)
	}
}

impl<A, B, C, D> PartialEq<&BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn eq(&self, rhs: &&BitSlice<C, D>) -> bool {
		self.eq(*rhs)
	}
}

/** Compares two `BitSlice`s by semantic — not bitwise — ordering.

The comparison sorts by testing each index for one slice to have a set bit where
the other has an unset bit. If the slices are different, the slice with the set
bit sorts greater than the slice with the unset bit.

If one of the slices is exhausted before they differ, the longer slice is
greater.
**/
impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	/// Performs a comparison by `<` or `>`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `rhs`: Another `BitSlice` against which to compare. This slice can
	///   have different cursor or storage types.
	///
	/// # Returns
	///
	/// The relative ordering of `self` against `rhs`. `self` is greater if it
	/// has a `true` bit at an index where `rhs` has a `false`; `self` is lesser
	/// if it has a `false` bit at an index where `rhs` has a `true`; if the two
	/// slices do not disagree then they are compared by length.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = 0x45u8;
	/// let bits = src.bits::<BigEndian>();
	/// let a = &bits[0 .. 3]; // 010
	/// let b = &bits[0 .. 4]; // 0100
	/// let c = &bits[0 .. 5]; // 01000
	/// let d = &bits[4 .. 8]; // 0101
	///
	/// assert!(a < b);
	/// assert!(b < c);
	/// assert!(c < d);
	/// ```
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		for (l, r) in self.iter().zip(rhs.iter()) {
			match (l, r) {
				(true, false) => return Some(Ordering::Greater),
				(false, true) => return Some(Ordering::Less),
				_ => continue,
			}
		}
		self.len().partial_cmp(&rhs.len())
	}
}

impl<A, B, C, D> PartialOrd<BitSlice<C, D>> for &BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &BitSlice<C, D>) -> Option<Ordering> {
		(*self).partial_cmp(rhs)
	}
}

impl<A, B, C, D> PartialOrd<&BitSlice<C, D>> for BitSlice<A, B>
where A: Cursor, B: BitStore, C: Cursor, D: BitStore {
	fn partial_cmp(&self, rhs: &&BitSlice<C, D>) -> Option<Ordering> {
		self.partial_cmp(*rhs)
	}
}

/// Provides write access to all fully-owned elements in the underlying memory
/// buffer. This excludes the edge elements if they are partially-owned.
impl<C, T> AsMut<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// This will not include partially-owned edge elements, as they may be
	/// contended by other slice handles.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutable slice of all uncontended storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let mut src = [0u8, 128];
	/// let bits = &mut src.bits_mut::<BigEndian>();
	///
	/// for elt in bits.as_mut() {
	///   *elt += 2;
	/// }
	///
	/// assert_eq!(&[2, 130], bits.as_ref());
	/// assert_eq!(&mut [130], bits[4 ..].as_mut());
	/// ```
	fn as_mut(&mut self) -> &mut [T] {
		self.as_mut_slice()
	}
}

/// Provides read-only access to all fully-owned elements in the underlying
/// memory buffer. This excludes the edge elements if they are partially-owned.
impl<C, T> AsRef<[T]> for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store.
	///
	/// This will not include partially-owned edge elements, as they may be
	/// contended by other slice handles.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An immutable slice of all storage elements.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let src = [0u8, 128];
	/// let bits = &src.bits::<BigEndian>();
	/// assert_eq!(&[0, 128], bits.as_ref());
	///
	/// assert_eq!(&[128], bits[4 ..].as_ref());
	/// ```
	fn as_ref(&self) -> &[T] {
		self.as_slice()
	}
}

impl<'a, C, T> From<&'a T> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a T) -> Self {
		BitSlice::<C, T>::from_element(src)
	}
}

impl<'a, C, T> From<&'a [T]> for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a [T]) -> Self {
		BitSlice::<C, T>::from_slice(src)
	}
}

impl<'a, C, T> From<&'a mut T> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut T) -> Self {
		BitSlice::<C, T>::from_element_mut(src)
	}
}

impl<'a, C, T> From<&'a mut [T]> for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn from(src: &'a mut [T]) -> Self {
		BitSlice::<C, T>::from_slice_mut(src)
	}
}

impl<'a, C, T> Default for &'a BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty()
	}
}

impl<'a, C, T> Default for &'a mut BitSlice<C, T>
where C: Cursor, T: 'a + BitStore {
	fn default() -> Self {
		BitSlice::empty_mut()
	}
}

impl<C, T> Binary for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` contents for display.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `f`: The formatter into which `self` is written.
	///
	/// # Returns
	///
	/// The result of the formatting operation.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b01001011u8, 0b0100_0000];
	/// let bits = &src.bits::<BigEndian>()[.. 10];
	/// assert_eq!("[01001011, 01]", &format!("{}", bits));
	/// # }
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let mut dbg = fmt.debug_list();
		/* Unfortunately, `T::BITS` cannot be used as the size for the
		array, due to limitations in the type system. As such, set it to the
		maximum used size.

		This allows the writes to target a static buffer, rather than a
		dynamic string, making the formatter usable in `#![no_std]`
		contexts.
		*/
		let mut w: [u8; 64] = [b'0'; 64];
		let mut writer = |elt: &T::Access, from: u8, to: u8| {
			let elt = elt.load();
			let (from, to) = (from as usize, to as usize);
			for (n, byte) in w.iter_mut().enumerate().take(to).skip(from) {
				*byte = b'0' + (elt.get::<C>((n as u8).idx()) as u8);
			}
			dbg.entry(&RenderPart(unsafe {
				str::from_utf8_unchecked(&w[from .. to])
			}));
		};
		match self.bitptr().domain().splat() {
			Err((h, e, t)) => writer(e, *h, *t),
			Ok((h, b, t)) => {
				if let Some((h, head)) = h {
					writer(head, *h, T::BITS);
				}
				if let Some(body) = b {
					for elt in body {
						writer(elt, 0, T::BITS);
					}
				}
				if let Some((tail, t)) = t {
					writer(tail, 0, *t);
				}
			},
		}
		dbg.finish()
	}
}

/** Prints the `BitSlice` for debugging.

The output is of the form `BitSlice<C, T> [ELT, *]` where `<C, T>` is the cursor
and element type, with square brackets on each end of the bits and all the
elements of the array printed in binary. The printout is always in semantic
order, and may not reflect the underlying buffer. To see the underlying buffer,
use `.as_ref()`.

The alternate character `{:#?}` prints each element on its own line, rather than
having all elements on the same line.
**/
impl<C, T> Debug for BitSlice<C, T>
where C: Cursor, T: BitStore {
	/// Renders the `BitSlice` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// # #[cfg(feature = "alloc")] {
	/// use bitvec::prelude::*;
	///
	/// let src = [0b0101_0000_1111_0101u16, 0b00000000_0000_0010];
	/// let bits = &src.bits::<LittleEndian>()[.. 18];
	/// assert_eq!(
    ///     "BitSlice<LittleEndian, u16> [1010111100001010, 01]",
	///     &format!("{:?}", bits),
	/// );
	/// # }
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("BitSlice<")?;
		fmt.write_str(C::TYPENAME)?;
		fmt.write_str(", ")?;
		fmt.write_str(T::TYPENAME)?;
		fmt.write_str("> ")?;
		Binary::fmt(self, fmt)
	}
}

/** Prints the `BitSlice` for displaying.

This prints each element in turn, formatted in binary in semantic order (so the
first bit seen is printed first and the last bit seen is printed last). Each
element of storage is separated by a space for ease of reading.

The alternate character `{:#}` prints each element on its own line.

To see the in-memory representation, use `.as_ref()` to get access to the raw
elements and print that slice instead.
**/
impl<C, T> Display for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Binary::fmt(self, fmt)
	}
}

impl<C, T> LowerHex for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let start = if fmt.alternate() { 0 } else { 2 };
		let mut dbg = fmt.debug_list();
		let mut w: [u8; 18] = [b'0'; 18];
		w[0] = b'0';
		w[1] = b'x';
		let mut writer = |bits: &Self| {
			let mut end = 2;
			for (idx, hex) in bits.chunks(4).enumerate() {
				let mut tmp = 0u8;
				for (num, bit) in hex.iter().enumerate() {
					tmp |= (*bit as u8) << num;
				}
				w[2 + idx] = match tmp {
					v @ 0 ..= 9 => b'0' + v,
					v @ 10 ..= 16 => b'a' + (v - 10),
					_ => unsafe { unreachable_unchecked() },
				};
				end += 1;
				dbg.entry(&RenderPart(unsafe {
					str::from_utf8_unchecked(&w[start .. end])
				}));
			}
		};
		match self.bitptr().domain().splat() {
			Err((head, elt, tail)) => {
				let (h, e, t) = (*head as usize, elt.load(), *tail as usize);
				let bits = Self::from_element(&e);
				writer(&bits[h .. t]);
			},
			Ok((h, b, t)) => {
				if let Some((h, head)) = h {
					writer(&Self::from_element(&head.load())[*h as usize ..]);
				}
				if let Some(body) = b {
					for elt in body.iter().map(BitAccess::load) {
						writer(Self::from_element(&elt));
					}
				}
				if let Some((tail, t)) = t {
					writer(&Self::from_element(&tail.load())[.. *t as usize]);
				}
			},
		}
		dbg.finish()
	}
}

impl<C, T> UpperHex for BitSlice<C, T>
where C: Cursor, T: BitStore {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let start = if fmt.alternate() { 0 } else { 2 };
		let mut dbg = fmt.debug_list();
		let mut w: [u8; 18] = [b'0'; 18];
		w[0] = b'0';
		w[1] = b'x';
		let mut writer = |bits: &Self| {
			let mut end = 2;
			for (idx, hex) in bits.chunks(4).enumerate() {
				let mut tmp = 0u8;
				for (num, bit) in hex.iter().enumerate() {
					tmp |= (*bit as u8) << num;
				}
				w[2 + idx] = match tmp {
					v @ 0 ..= 9 => b'0' + v,
					v @ 10 ..= 16 => b'A' + (v - 10),
					_ => unsafe { unreachable_unchecked() },
				};
				end += 1;
				dbg.entry(&RenderPart(unsafe {
					str::from_utf8_unchecked(&w[start .. end])
				}));
			}
		};
		match self.bitptr().domain().splat() {
			Err((head, elt, tail)) => {
				let (h, e, t) = (*head as usize, elt.load(), *tail as usize);
				let bits = Self::from_element(&e);
				writer(&bits[h .. t]);
			},
			Ok((h, b, t)) => {
				if let Some((h, head)) = h {
					writer(&Self::from_element(&head.load())[*h as usize ..]);
				}
				if let Some(body) = b {
					for elt in body.iter().map(BitAccess::load) {
						writer(Self::from_element(&elt));
					}
				}
				if let Some((tail, t)) = t {
					writer(&Self::from_element(&tail.load())[.. *t as usize]);
				}
			},
		}
		dbg.finish()
	}
}

/** Wrapper for inserting pre-rendered text into a formatting stream.

The numeric formatters write text into a buffer, which a formatter then reads
directly. The formatter only takes `&dyn Debug` objects, so this translates the
text buffer into a compatible trait object.
**/
struct RenderPart<'a>(&'a str);
impl Debug for RenderPart<'_> {
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str(&self.0)
	}
}
