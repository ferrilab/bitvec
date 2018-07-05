use super::{
	BitSlice,
	Bits,
	Endian,
	BigEndian,
	LittleEndian,
	TRUE,
	FALSE,
};
use std::borrow::{
	Borrow,
	BorrowMut,
};
use std::clone::Clone;
use std::cmp::{
	Eq,
	Ord,
	Ordering,
	PartialEq,
	PartialOrd,
};
use std::convert::{
	AsMut,
	AsRef,
	From,
};
use std::fmt::{
	self,
	Debug,
	Display,
	Formatter,
};
use std::iter::{
	DoubleEndedIterator,
	ExactSizeIterator,
	Extend,
	FromIterator,
	Iterator,
	IntoIterator,
};
use std::marker::PhantomData;
use std::mem;
use std::ops::{
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
	Neg,
	Not,
	Shl,
	ShlAssign,
	Shr,
	ShrAssign,
	Sub,
	SubAssign,
};
use std::ptr;

/** A compact `Vec` of bits, whose cursor and storage type can be customized.

`BitVec` is a newtype wrapper over `Vec`, and as such is exactly three words in
size on the stack.

**IMPORTANT NOTE:** It is **wildly** unsafe to use `mem::transmute` between
`Vec<T>` and `BitVec<_, T>`, because `BitVec` achieves its size by using the
length field of the underlying `Vec` to count bits, rather than elements. This
means that it has a fixed maximum bit width regardless of element type, and the
length field will always be horrifically wrong to be treated as a `Vec`. Safe
methods exist to move between `Vec` and `BitVec` – USE THEM.

`BitVec` takes two type parameters.

- `E: Endian` must be an implementor of the `Endian` trait. `BitVec` takes a
  `PhantomData` marker for access to the associated functions, and will never
  make use of an instance of the trait. The default implementations,
  `LittleEndian` and `BigEndian`, are zero-sized, and any further
  implementations should be as well, as the invoked functions will never receive
  state.
- `T: Bits` must be a primitive type. Rust decided long ago to not provide a
  unifying trait over the primitives, so `Bits` provides access to just enough
  properties of the primitives for `BitVec` to use. This trait is sealed against
  downstream implementation, and can only be implemented in this crate.
**/
pub struct BitVec<E = BigEndian, T = u8>
where E: Endian, T: Bits {
	inner: Vec<T>,
	_endian: PhantomData<E>,
}

impl<E, T> BitVec<E, T>
where E: Endian, T: Bits {
	/// Construct a new, empty, `BitVec<E, T>`.
	///
	/// The vector will not allocate until bits are pushed onto it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// assert_eq!(bv.capacity(), 0);
	/// ```
	pub fn new() -> Self {
		Self {
			inner: Vec::new(),
			_endian: PhantomData,
		}
	}

	/// Construct a new, empty `BitVec<T>` with the specified capacity.
	///
	/// The vector will be able to hold exactly `capacity` elements without
	/// reallocating. If `capacity` is 0, the vector will not allocate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec = BitVec::with_capacity(10);
	/// assert!(bv.is_empty());
	/// assert!(bv.capacity() >= 2);
	/// ```
	pub fn with_capacity(capacity: usize) -> Self {
		let (elts, bits) = T::split(capacity);
		let cap = elts + if bits > 0 { 1 } else { 0 };
		Self {
			inner: Vec::with_capacity(cap),
			_endian: PhantomData,
		}
	}

	/// Return the number of bits the vector can hold without reallocating.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec = BitVec::with_capacity(10);
	/// assert!(bv.is_empty());
	/// assert!(bv.capacity() >= 2);
	/// ```
	pub fn capacity(&self) -> usize {
		assert!(self.inner.capacity() <= T::MAX_ELT, "Capacity overflow");
		self.inner.capacity() << T::BITS
	}

	/// Append a bit to the collection.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	/// ```
	pub fn push(&mut self, value: bool) {
		assert!(self.len() < ::std::usize::MAX, "Vector will overflow!");
		let bit = self.bits();
		//  Get a cursor to the bit that matches the semantic count.
		let cursor = E::curr::<T>(bit);
		//  Insert `value` at the current cursor.
		self.do_with_tail(|elt| elt.set(cursor, value));
		//  If the cursor is at the *end* of an element, this bit will finish it
		//  and the element count needs to be incremented.
		if bit == T::MASK {
			let elts = self.elts();
			assert!(elts <= T::MAX_ELT, "Elements will overflow");
			unsafe { self.set_elts(elts + 1) };
		}
		//  Increment the bit counter, wrapping if need be.
		unsafe { self.set_bits((bit + 1) & T::MASK); }
	}

	/// Remove the last bit from the collection.
	///
	/// Returns `None` if the collection is empty.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv: BitVec = BitVec::new();
	/// assert!(bv.is_empty());
	/// bv.push(true);
	/// assert_eq!(bv.len(), 1);
	/// assert!(bv[0]);
	///
	/// assert!(bv.pop().unwrap());
	/// assert!(bv.is_empty());
	/// assert!(bv.pop().is_none());
	/// ```
	pub fn pop(&mut self) -> Option<bool> {
		if self.inner.is_empty() {
			return None;
		}
		//  Vec.pop never calls the allocator, it just decrements the length
		//  counter. Similarly, this just decrements the length counter and
		//  yields the bit underneath it.
		let cur = self.len() - 1;
		let ret = self.get(cur);
		unsafe { self.inner.set_len(cur); }
		Some(ret)
	}

	/// Empty out the `BitVec`, resetting it to length zero.
	///
	/// This does not affect the memory store! It will not zero the raw memory
	/// nor will it deallocate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![1; 30];
	/// assert_eq!(bv.len(), 30);
	/// assert!(bv.iter().all(|b| b));
	/// bv.clear();
	/// assert!(bv.is_empty());
	/// ```
	///
	/// After `clear()`, `bv` will no longer show raw memory, so the above test
	/// cannot show that the underlying memory is untouched. This is also an
	/// implementation detail on which you should not rely.
	pub fn clear(&mut self) {
		self.do_with_vec(|v| v.clear());
	}

	/// Reserve capacity for additional bits.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![1; 5];
	/// let cap = bv.capacity();
	/// bv.reserve(10);
	/// assert!(bv.capacity() >= cap + 10);
	/// ```
	pub fn reserve(&mut self, additional: usize) {
		let (cur_elts, cur_bits) = T::split(self.raw_len());
		let (new_elts, new_bits) = T::split(additional);
		let (elts, bits) = (cur_elts + new_elts, cur_bits + new_bits);
		let extra = elts + if bits > 0 { 1 } else { 0 };
		assert!(self.raw_len() + extra <= T::MAX_ELT, "Capacity would overflow");
		self.do_with_vec(|v| v.reserve(extra));
	}

	/// Shrink the capacity to fit at least as much as is needed, but with as
	/// little or as much excess as the allocator chooses.
	///
	/// This may or may not deallocate tail space, as the allocator sees fit.
	/// This does not zero the abandoned memory.
	pub fn shrink_to_fit(&mut self) {
		self.do_with_vec(|v| v.shrink_to_fit());
	}

	/// Shrink the `BitVec` to the given size, dropping all excess storage.
	///
	/// This does not affect the memory store! It will not zero the raw memory
	/// nor will it deallocate.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![1; 30];
	/// assert_eq!(bv.len(), 30);
	/// let cap = bv.capacity();
	/// bv.truncate(10);
	/// assert_eq!(bv.len(), 10);
	/// assert_eq!(bv.capacity(), cap);
	/// ```
	pub fn truncate(&mut self, len: usize) {
		let (elts, bits) = T::split(len);
		let trunc = elts + if bits > 0 { 1 } else { 0 };
		self.do_with_vec(|v| v.truncate(trunc));
		unsafe { self.set_len(len); }
	}

	/// Convert the `BitVec` into a boxed slice of storage elements. This drops
	/// all `BitVec` management semantics, including partial fill status of the
	/// trailing element or endianness, and gives ownership the raw storage.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec<BigEndian, u8> = bitvec![1; 64];
	/// let bytes: Box<[u8]> = bv.into_boxed_slice();
	/// assert_eq!(bytes.len(), 8);
	/// for byte in bytes.iter() {
	///     assert_eq!(*byte, !0);
	/// }
	/// ```
	pub fn into_boxed_slice(self) -> Box<[T]> {
		let raw = self.raw_len();
		let buf = unsafe {
			let mut buf = ptr::read(&self.inner);
			mem::forget(self);
			buf.set_len(raw);
			buf
		};
		buf.into_boxed_slice()
	}

	/// Set the bit count to a new value.
	///
	/// This utility function unconditionally sets the bottom `T::BITS` bits of
	/// `inner.len` to reflect how many bits of the tail are live. It should
	/// only be used when adjusting the liveness of the tail.
	unsafe fn set_bits(&mut self, count: u8) {
		assert!(count <= T::MASK, "Index out of range");
		let elt = self.len() & !(T::MASK as usize);
		self.inner.set_len(elt | count as usize);
	}

	/// Set the element count to a new value.
	///
	/// This utility function unconditionally sets the rest of the bits of
	/// `inner.len` to reflect how many elements in the `Vec` are fully filled.
	/// It will always be one fewer than the number of elements the `Vec` would
	/// consider live, were it consulted. It should only be used when adjusting
	/// the liveness of the underlying `Vec`.
	unsafe fn set_elts(&mut self, count: usize) {
		assert!(count <= T::MAX_ELT, "Length out of range");
		let bit = self.len() & (T::MASK as usize);
		self.inner.set_len(T::join(count, bit as u8));
	}

	/// Set the length directly.
	pub(crate) unsafe fn set_len(&mut self, len: usize) {
		self.inner.set_len(len);
	}

	/// Execute some operation with the storage `Vec` in sane condition.
	///
	/// The given function receives a sane `Vec<T>`, with the `len` attribute
	/// set to reflect the reality of elements in use. The storage `Vec` is then
	/// set back to the correct state for `BitVec` use after the given function
	/// ends.
	///
	/// The given function may not return a reference into the `Vec`. It must
	/// return a standalone value, or nothing. If access into the buffer is
	/// needed, use `AsRef` or `AsMut`.
	///
	/// NOTE: If the operation changes the length of the underlying `Vec`, this
	/// will assume that all elements are full, and the `bits()` cursor will be
	/// wiped.
	fn do_with_vec<F: Fn(&mut Vec<T>) -> R, R>(&mut self, op: F) -> R {
		//  Keep the old length in order to (maybe) restore it.
		let len = self.len();
		//  Get the number of storage elements the `Vec` considers live.
		let old = self.raw_len();
		//  `BitVec.inner.len` is used to store both element count and bit count
		//  which is a state that *cannot* be passed to operations on the `Vec`
		//  itself. Set the `Vec.len` member to be the number of live elements.
		unsafe { self.inner.set_len(old); }
		//  Do the operation.
		let ret = op(&mut self.inner);
		//  The operation may have changed how many elements are considered live
		//  so we must get the new count, manipulate it, and use that. (If the
		//  operation clears the `Vec`, then zero is a perfectly valid `len`.)
		//  There is not enough information in this call to set `bits()`
		//  correctly after a `Vec`-mutating call, so it is up to the caller to
		//  ensure that the `bits()` segment is correct after this returns.
		let new = self.inner.len();
		assert!(new <= T::MAX_ELT, "Length out of range!");
		//  If the length is unchanged before and after the call, restore the
		//  original bit length.
		if new == old {
			unsafe {
				self.inner.set_len(len);
			}
		}
		//  If the length is different, give up and assume all the elements are
		//  full. Use `push_elt()` to manipulate allocations.
		else {
			unsafe {
				self.set_bits(0);
				self.set_elts(new);
			}
		}
		ret
	}

	/// Execute some operation with the tail storage element.
	///
	/// If the bit cursor is at zero when this is called, then the current tail
	/// element is not live, and one will be pushed onto the underlying `Vec`,
	/// and this fresh element will be provided to the operation.
	fn do_with_tail<F: Fn(&mut T) -> R, R>(&mut self, op: F) -> R {
		//  If the cursor is at zero, there is not necessarily an element
		//  allocated underneath it. Have the `Vec` try to push an element,
		//  allocating if need be, for use.
		if self.bits() == 0 {
			self.push_elt();
		}
		let old_len = self.inner.len();
		let elts = self.elts();
		//  elts() counts how many elements are full. There is always one more
		//  element allocated and live than are full, so inform the `Vec` that
		//  it has `elts() + 1` elements live, act on the last one, and then
		//  restore the length to the correct value for `BitVec`'s purposes.
		unsafe {
			self.inner.set_len(elts + 1);
			let ret = op(&mut self.inner[elts]);
			self.inner.set_len(old_len);
			ret
		}
	}

	/// Push an element onto the end of the underlying store. This may or may
	/// not call the allocator. After the element ensured to be allocated, the
	/// old length is restored.
	fn push_elt(&mut self) {
		let len = self.len();
		self.do_with_vec(|v| v.push(Default::default()));
		unsafe {
			self.inner.set_len(len);
		}
	}

	/// Format the debug header for the type.
	///
	/// The body format is provided by `BitSlice`.
	fn fmt_header(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(fmt, "BitVec<{}, {}>", E::TY, T::TY)
	}
}

/// Give write access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<E, T> AsMut<[T]> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Access the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv: BitVec = bitvec![0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// for elt in bv.as_mut() {
	///   *elt += 2;
	/// }
	/// assert_eq!(&[2, 0b1000_0010], bv.as_ref());
	/// ```
	fn as_mut(&mut self) -> &mut [T] {
		BitSlice::as_mut(self)
	}
}

/// Give read access to all live elements in the underlying storage, including
/// the partially-filled tail.
impl<E, T> AsRef<[T]> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Access the underlying store.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![0, 0, 0, 0, 0, 0, 0, 0, 1];
	/// assert_eq!(&[0, 0b1000_0000], bv.as_ref());
	/// ```
	fn as_ref(&self) -> &[T] {
		BitSlice::as_ref(self)
	}
}

/// Perform the Boolean AND operation between each element of a `BitVec` and
/// anything that can provide a stream of `bool` values (such as another
/// `BitVec`, or any `bool` generator of your choice). The `BitVec` emitted will
/// have the length of the shorter sequence of bits -- if one is longer than the
/// other, the extra bits will be ignored.
impl<E, T, I> BitAnd<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// AND a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let lhs = bitvec![BigEndian, u8; 0, 1, 0, 1];
	/// let rhs = bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// let and = lhs & rhs;
	/// assert_eq!("0001", &format!("{}", and));
	/// ```
	fn bitand(mut self, rhs: I) -> Self::Output {
		self &= rhs;
		self
	}
}

/// Perform the Boolean AND operation in place on a `BitVec`, using a stream of
/// `bool` values as the other bit for each operation. If the other stream is
/// shorter than `self`, `self` will be truncated when the other stream expires.
impl<E, T, I> BitAndAssign<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	/// AND another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut src  = bitvec![BigEndian, u8; 0, 1, 0, 1];
	///         src &= bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// assert_eq!("0001", &format!("{}", src));
	/// ```
	fn bitand_assign(&mut self, rhs: I) {
		let mut len = 0;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
			let val = self.get(idx) & other;
			self.set(idx, val);
			len += 1;
		}
		self.truncate(len);
	}
}

/// Perform the Boolean OR operation between each element of a `BitVec` and
/// anything that can provide a stream of `bool` values (such as another
/// `BitVec`, or any `bool` generator of your choice). The `BitVec` emitted will
/// have the length of the shorter sequence of bits -- if one is longer than the
/// other, the extra bits will be ignored.
impl<E, T, I> BitOr<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// OR a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let lhs = bitvec![BigEndian, u8; 0, 1, 0, 1];
	/// let rhs = bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// let or  = lhs | rhs;
	/// assert_eq!("0111", &format!("{}", or));
	/// ```
	fn bitor(mut self, rhs: I) -> Self::Output {
		self |= rhs;
		self
	}
}

/// Perform the Boolean OR operation in place on a `BitVec`, using a stream of
/// `bool` values as the other bit for each operation. If the other stream is
/// shorter than `self`, `self` will be truncated when the other stream expires.
impl<E, T, I> BitOrAssign<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	/// OR another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut src  = bitvec![BigEndian, u8; 0, 1, 0, 1];
	///         src |= bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// assert_eq!("0111", &format!("{}", src));
	/// ```
	fn bitor_assign(&mut self, rhs: I) {
		let mut len = 0;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
			let val = self.get(idx) | other;
			self.set(idx, val);
			len += 1;
		}
		self.truncate(len);
	}
}

/// Perform the Boolean XOR operation between each element of a `BitVec` and
/// anything that can provide a stream of `bool` values (such as another
/// `BitVec`, or any `bool` generator of your choice). The `BitVec` emitted will
/// have the length of the shorter sequence of bits -- if one is longer than the
/// other, the extra bits will be ignored.
impl<E, T, I> BitXor<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	type Output = Self;

	/// XOR a vector and a bitstream, producing a new vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let lhs = bitvec![BigEndian, u8; 0, 1, 0, 1];
	/// let rhs = bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// let xor = lhs ^ rhs;
	/// assert_eq!("0110", &format!("{}", xor));
	/// ```
	fn bitxor(mut self, rhs: I) -> Self::Output {
		self ^= rhs;
		self
	}
}

/// Perform the Boolean XOR operation in place on a `BitVec`, using a stream of
/// `bool` values as the other bit for each operation. If the other stream is
/// shorter than `self`, `self` will be truncated when the other stream expires.
impl<E, T, I> BitXorAssign<I> for BitVec<E, T>
where E: Endian, T: Bits, I: IntoIterator<Item=bool> {
	/// XOR another bitstream into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut src  = bitvec![BigEndian, u8; 0, 1, 0, 1];
	///         src ^= bitvec![BigEndian, u8; 0, 0, 1, 1];
	/// assert_eq!("0110", &format!("{}", src));
	/// ```
	fn bitxor_assign(&mut self, rhs: I) {
		let mut len = 0;
		for (idx, other) in (0 .. self.len()).zip(rhs.into_iter()) {
			let val = self.get(idx) ^ other;
			self.set(idx, val);
			len += 1;
		}
		self.truncate(len);
	}
}

/// Signify that `BitSlice` is the borrowed form of `BitVec`.
impl<E, T> Borrow<BitSlice<E, T>> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Borrow the `BitVec` as a `BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// use std::borrow::Borrow;
	/// let bv = bitvec![0; 8];
	/// let bref: &BitSlice = bv.borrow();
	/// assert!(!bref.get(7));
	/// ```
	fn borrow(&self) -> &BitSlice<E, T> {
		&*self
	}
}

/// Signify that `BitSlice` is the borrowed form of `BitVec`.
impl<E, T> BorrowMut<BitSlice<E, T>> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Mutably borow the `BitVec` as a `BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// use std::borrow::BorrowMut;
	/// let mut bv = bitvec![0; 8];
	/// let bref: &mut BitSlice = bv.borrow_mut();
	/// assert!(!bref.get(7));
	/// bref.set(7, true);
	/// assert!(bref.get(7));
	/// ```
	fn borrow_mut(&mut self) -> &mut BitSlice<E, T> {
		&mut *self
	}
}

impl<E, T> Clone for BitVec<E, T>
where E: Endian, T: Bits {
	fn clone(&self) -> Self {
		let mut out = Self::from(self.as_ref());
		unsafe {
			out.inner.set_len(self.len());
		}
		out
	}

	fn clone_from(&mut self, other: &Self) {
		self.clear();
		self.reserve(other.len());
		unsafe {
			let src = other.as_ptr();
			let dst = self.as_mut_ptr();
			let len = other.raw_len();
			ptr::copy_nonoverlapping(src, dst, len);
		}
	}
}

/// Print the `BitVec` for debugging.
///
/// The output is of the form `BitVec<E, T> [ELT, *]`, where `<E, T>` is the
/// endianness and element type, with square brackets on each end of the bits
/// and all the live elements in the vector printed in binary. The printout is
/// always in semantic order, and may not reflect the underlying store. To see
/// the underlying store, use `format!("{:?}", self.as_ref());` instead.
///
/// The alternate character `{:#?}` prints each element on its own line, rather
/// than separated by a space.
impl<E, T> Debug for BitVec<E, T>
where E: Endian, T: Bits {
	/// Render the `BitVec` type header and contents for debug.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![LittleEndian, u16;
	///     0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1
	/// ];
	/// assert_eq!(
	///     "BitVec<LittleEndian, u16> [0101000011110101]",
	///     &format!("{:?}", bv)
	/// );
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		let alt = fmt.alternate();
		self.fmt_header(fmt)?;
		fmt.write_str(" [")?;
		if alt { writeln!(fmt)?; }
		self.fmt_body(fmt, true)?;
		if alt { writeln!(fmt)?; }
		fmt.write_str("]")
	}
}

/// Reborrow the `BitVec` as a `BitSlice`.
///
/// This mimics the separation between `Vec<T>` and `[T]`.
impl<E, T> Deref for BitVec<E, T>
where E: Endian, T: Bits {
	type Target = BitSlice<E, T>;

	/// Dereference `&BitVec` down to `&BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec = bitvec![1; 4];
	/// let bref: &BitSlice = &bv;
	/// assert!(bref.get(2));
	/// ```
	fn deref(&self) -> &Self::Target {
		//  `BitVec`'s representation of its inner `Vec` matches exactly the
		//  invariants of how `BitSlice` references must look. This is fine.
		unsafe { mem::transmute(&self.inner as &[T]) }
	}
}

/// Reborrow the `BitVec` as a `BitSlice`.
///
/// This mimics the separation between `Vec<T>` and `[T]`.
impl<E, T> DerefMut for BitVec<E, T>
where E: Endian, T: Bits {
	/// Dereference `&mut BitVec` down to `&mut BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv: BitVec = bitvec![0; 6];
	/// let bref: &mut BitSlice = &mut bv;
	/// assert!(!bref.get(5));
	/// bref.set(5, true);
	/// assert!(bref.get(5));
	/// ```
	fn deref_mut(&mut self) -> &mut Self::Target {
		unsafe { mem::transmute(&mut self.inner as &mut [T]) }
	}
}

/// Print the `BitVec` for displaying.
///
/// This prints each element in turn, formatted in binary in semantic order (so
/// the first bit seen is printed first and the last bit seen printed last).
/// Each element of storage is separated by a space for ease of reading.
///
/// The alternate character `{:#}` prints each element on its own line.
///
/// To see the in-memory representation, use `AsRef` to get access to the raw
/// elements and print that slice instead.
impl<E, T> Display for BitVec<E, T>
where E: Endian, T: Bits {
	/// Render the `BitVec` contents for display.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 1, 0, 0, 1, 0, 1, 1, 0, 1];
	/// assert_eq!("01001011 01", &format!("{}", bv));
	/// ```
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		self.fmt_body(fmt, false)
	}
}

/// Ready the underlying storage for Drop.
impl<E, T> Drop for BitVec<E, T>
where E: Endian, T: Bits {
	fn drop(&mut self) {
		//  If the `Vec` is non-empty, set the length to the number of used
		//  elements as preparation for drop. The bits do not need to be wiped.
		//
		//  If we don't do this, the `Vec` drop will treat the bit total as the
		//  number of elements and try to loop through all of them, which will
		//  not take 2 ** T::BITS times as long to run as expected, because
		//  it'll segfault.
		let raw = self.raw_len();
		unsafe { self.inner.set_len(raw); }
	}
}

/// Extend a `BitVec` with the contents of another bitstream.
///
/// At present, this just calls `.push()` in a loop. When specialization becomes
/// available, it will be able to more intelligently perform bulk moves from the
/// source into `self` when the source is `BitSlice`-compatible.
impl<E, T> Extend<bool> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Extend a `BitVec` from another bitstream.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![0; 4];
	/// bv.extend(bitvec![1; 4]);
	/// assert_eq!("00001111", &format!("{}", bv));
	/// ```
	fn extend<I>(&mut self, src: I)
	where I: IntoIterator<Item=bool> {
		let iter = src.into_iter();
		match iter.size_hint() {
			(_, Some(hi)) => self.reserve(hi),
			(lo, None) => self.reserve(lo),
		}
		for bit in iter {
			self.push(bit);
		}
		self.shrink_to_fit();
	}
}

/// Clone a `BitSlice` into an owned `BitVec`.
///
/// The idiomatic `BitSlice` to `BitVec` conversion is `BitSlice::to_owned`, but
/// just as `&[T].into()` yields a `Vec`, `&BitSlice.into()` yields a `BitVec`.
impl<'a, E, T> From<&'a BitSlice<E, T>> for BitVec<E, T>
where E: Endian, T: 'a + Bits {
	fn from(src: &'a BitSlice<E, T>) -> Self {
		src.to_owned()
	}
}

/// Build a `BitVec` out of a slice of `bool`.
///
/// This is primarily for the `bitvec!` macro; it is not recommended for general
/// use.
impl<'a, E, T> From<&'a [bool]> for BitVec<E, T>
where E: Endian, T: 'a + Bits {
	fn from(src: &'a [bool]) -> Self {
		let mut out = Self::with_capacity(src.len());
		for bit in src {
			out.push(*bit);
		}
		out
	}
}

/// Build a `BitVec` out of a borrowed slice of elements.
///
/// This copies the memory as-is from the source buffer into the new `BitVec`.
/// The source buffer will be unchanged by this operation, so you don't need to
/// worry about using the correct cursor type for the read.
///
/// This operation does a copy from the source buffer into a new allocation, as
/// it can only borrow the source and not take ownership.
impl<'a, E, T> From<&'a [T]> for BitVec<E, T>
where E: Endian, T: 'a + Bits {
	/// Build a `BitVec<E: Endian, T: Bits>` from a borrowed `&[T]`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let src: &[u8] = &[5, 10];
	/// let bv: BitVec = src.into();
	/// assert_eq!("00000101 00001010", &format!("{}", bv));
	/// ```
	fn from(src: &'a [T]) -> Self {
		<&BitSlice<E, T>>::from(src).to_owned()
	}
}

/// Build a `BitVec` out of an owned slice of elements.
///
/// This moves the memory as-is from the source buffer into the new `BitVec`.
/// The source buffer will be unchanged by this operation, so you don't need to
/// worry about using the correct cursor type.
impl<E, T> From<Box<[T]>> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Consume a `Box<[T: Bits]>` and creates a `BitVec<E: Endian, T>` from it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let src: Box<[u8]> = Box::new([3, 6, 9, 12, 15]);
	/// let bv: BitVec = src.into();
	/// assert_eq!("00000011 00000110 00001001 00001100 00001111", &format!("{}", bv));
	/// ```
	fn from(src: Box<[T]>) -> Self {
		assert!(src.len() <= T::MAX_ELT, "Source slice too long!");
		Self::from(Vec::from(src))
	}
}

/// Build a `BitVec` out of a `Vec` of elements.
///
/// This moves the memory as-is from the source buffer into the new `BitVec`.
/// The source buffer will be unchanged by this operation, so you don't need to
/// worry about using the correct cursor type.
impl<E, T> From<Vec<T>> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Consume a `Vec<T: Bits>` and creates a `BitVec<E: Endian, T>` from it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let src: Vec<u8> = vec![1, 2, 4, 8];
	/// let bv: BitVec = src.into();
	/// assert_eq!("00000001 00000010 00000100 00001000", &format!("{}", bv));
	/// ```
	fn from(src: Vec<T>) -> Self {
		let elts = src.len();
		assert!(elts <= T::MAX_ELT, "Source vector too long!");
		let mut out = Self {
			inner: src,
			_endian: PhantomData::<E>,
		};
		unsafe {
			out.set_bits(0);
			out.set_elts(elts);
		}
		out
	}
}

/// Change cursors on a `BitVec` without mutating the underlying data.
///
/// I don't know why this would be useful at the time of writing, as the `From`
/// implementations on collections crawl the collection elements in the order
/// requested and so the source and destination storage collections will be
/// bitwise identical, but here's the option anyway.
///
/// If the tail element is partially filled, then this operation will shift the
/// tail element so that the edge of the filled section is on the correct edge
/// of the tail element.
impl<T: Bits> From<BitVec<LittleEndian, T>> for BitVec<BigEndian, T> {
	fn from(mut src: BitVec<LittleEndian, T>) -> Self {
		let bits = src.bits();
		//  If bits() is zero, then the tail is full and cannot shift.
		//  If bits() is nonzero, then the shamt is WIDTH - bits().
		//  E.g. a WIDTH of 32 and a bits() of 31 means bit 30 is the highest
		//  bit set, and the element should shl by 1 so that bit 31 is the
		//  highest bit set, and bit 0 will be empty.
		if bits > 0 {
			let shamt = T::WIDTH - bits;
			src.do_with_tail(|elt| *elt <<= shamt);
		}
		//  The cursor is stored in PhantomData, and known only to the complier.
		//  Transmutation is perfectly safe, since the only concrete item is the
		//  storage, which this explicitly does not alter.
		unsafe { mem::transmute(src) }
	}
}

/// Change cursors on a `BitVec` without mutating the underlying data.
///
/// I don't know why this would be useful at the time of writing, as the `From`
/// implementations on collections crawl the collection elements in the order
/// requested and so the source and destination storage collections will be
/// bitwise identical, but here's the option anyway.
///
/// If the tail element is partially filled, then this operation will shift the
/// tail element so that the edge of the filled section is on the correct edge
/// of the tail element.
impl<T: Bits> From<BitVec<BigEndian, T>> for BitVec<LittleEndian, T> {
	fn from(mut src: BitVec<BigEndian, T>) -> Self {
		let bits = src.bits();
		if bits > 0 {
			let shamt = T::WIDTH - bits;
			src.do_with_tail(|elt| *elt >>= shamt);
		}
		unsafe { mem::transmute(src) }
	}
}

/// Permit the construction of a `BitVec` by using `.collect()` on an iterator
/// of `bool`.
impl<E, T> FromIterator<bool> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Collect an iterator of `bool` into a vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// use std::iter::repeat;
	/// let bv: BitVec = repeat(true).take(4).chain(repeat(false).take(4)).collect();
	/// assert_eq!("11110000", &format!("{}", bv));
	/// ```
	fn from_iter<I: IntoIterator<Item=bool>>(src: I) -> Self {
		let iter = src.into_iter();
		let mut out = match iter.size_hint() {
			(_, Some(len)) |
			(len, _) if len > 0 => Self::with_capacity(len),
			_ => Self::new(),
		};
		for bit in iter {
			out.push(bit);
		}
		out
	}
}

/// Get the bit at a specific index. The index must be less than the length of
/// the `BitVec`.
impl<E, T> Index<usize> for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = bool;

	/// Look up a single bit by semantic count.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0];
	/// assert!(!bv[7]); // ---------------------------------^  |  |
	/// assert!( bv[8]); //-------------------------------------^  |
	/// assert!(!bv[9]); // ---------------------------------------^
	/// ```
	///
	/// If the index is greater than or equal to the length, indexing will panic.
	///
	/// The below test will panic when accessing index 1, as only index 0 is valid.
	///
	/// ```rust,should_panic
	/// use bitvec::*;
	/// let mut bv: BitVec = BitVec::new();
	/// bv.push(true);
	/// bv[1];
	/// ```
	fn index(&self, cursor: usize) -> &Self::Output {
		assert!(cursor < self.inner.len(), "Index out of range!");
		self.index(T::split(cursor))
	}
}

/// Get the bit in a specific element. The element index must be less than or
/// equal to the value returned by `elts()`, and the bit index must be less
/// than the width of the storage type.
///
/// If the `BitVec` has a partially-filled tail, then the value returned by
/// `elts()` is a valid index.
///
/// The element and bit indices are combined using `Bits::join` for the storage
/// type.
///
/// This index is not recommended for public use.
impl<E, T> Index<(usize, u8)> for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = bool;

	/// Index into a `BitVec` using a known element index and a count into that
	/// element. The count must not be converted for endianness outside the
	/// call.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 1, 1, 1, 1, 0, 0, 0, 0, 0, 1];
	/// assert!(bv[(1, 1)]); // -----------------------------------^
	/// ```
	fn index(&self, (elt, bit): (usize, u8)) -> &Self::Output {
		assert!(T::join(elt, bit) < self.len(), "Index out of range!");
		match (self.inner[elt]).get(E::curr::<T>(bit)) {
			true => &TRUE,
			false => &FALSE,
		}
	}
}

/// Produce an iterator over all the bits in the vector.
///
/// This iterator follows the ordering in the vector type, and implements
/// `ExactSizeIterator`, since `BitVec`s always know exactly how large they are,
/// and `DoubleEndedIterator`, since they have known ends.
impl<E, T> IntoIterator for BitVec<E, T>
where E: Endian, T: Bits {
	type Item = bool;
	#[doc(hidden)]
	type IntoIter = IntoIter<E, T>;

	/// Iterate over the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 1, 1, 1, 1, 0, 0, 0, 0];
	/// let mut count = 0;
	/// for bit in bv {
	///     if bit { count += 1; }
	/// }
	/// assert_eq!(count, 4);
	/// ```
	fn into_iter(self) -> Self::IntoIter {
		Self::IntoIter::from(self)
	}
}

impl<E, T> Neg for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		self = !self;
		self += BitVec::<E, T>::from(&[true] as &[bool]);
		self
	}
}

/// Flip all bits in the vector.
///
/// This invokes the `!` operator on each element of the borrowed storage, and
/// so it will also flip bits in the tail that are outside the `BitVec` length
/// if any. Use `^= repeat(true)` to flip only the bits actually inside the
/// `BitVec` purview. `^=` also has the advantage of being a borrowing operator
/// rather than a consuming/returning operator.
/// ```
impl<E, T> Not for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	/// Invert all bits in the vector.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv: BitVec<BigEndian, u32> = BitVec::from(&[0u32] as &[u32]);
	/// let flip = !bv;
	/// assert_eq!(!0u32, flip.as_ref()[0]);
	//  Because self does not have to interact with any other `BitVec`, and bits
	//  beyond `BitVec.len()` are uninitialized and don't matter, this is free
	//  to simply negate the elements in place and then return self.
	fn not(mut self) -> Self::Output {
		!&mut *self;
		self
	}
}

/// Test if two `BitVec`s are semantically — not bitwise — equal.
///
/// It is valid to compare two vectors of different endianness or element types.
///
/// The equality condition requires that they have the same number of stored
/// bits and that each pair of bits in semantic order are identical.
impl<A, B, C, D> PartialEq<BitVec<C, D>> for BitVec<A, B>
where A: Endian, B: Bits, C: Endian, D: Bits {
	/// Perform a comparison by `==`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let l: BitVec<LittleEndian, u16> = bitvec![LittleEndian, u16; 0, 1, 0, 1];
	/// let r: BitVec<BigEndian, u32> = bitvec![BigEndian, u32; 0, 1, 0, 1];
	/// assert!(l == r);
	/// ```
	fn eq(&self, rhs: &BitVec<C, D>) -> bool {
		BitSlice::eq(&self, &rhs)
	}
}

impl<E, T> Eq for BitVec<E, T>
where E: Endian, T: Bits {}

/// Compare two `BitVec`s by semantic — not bitwise — ordering.
///
/// The comparison sorts by testing each index for one vector to have a set bit
/// where the other vector has an unset bit. If the vectors are different, the
/// vector with the set bit sorts greater than the vector with the unset bit.
///
/// If one of the vectors is exhausted before they differ, the longer vector is
/// greater.
impl<A, B, C, D> PartialOrd<BitVec<C, D>> for BitVec<A, B>
where A: Endian, B: Bits, C: Endian, D: Bits {
	/// Perform a comparison by `<` or `>`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// use bitvec::*;
	/// let a = bitvec![0, 1, 0, 0];
	/// let b = bitvec![0, 1, 0, 1];
	/// let c = bitvec![0, 1, 0, 1, 1];
	/// assert!(a < b);
	/// assert!(b < c);
	/// ```
	fn partial_cmp(&self, rhs: &BitVec<C, D>) -> Option<Ordering> {
		BitSlice::partial_cmp(&self, &rhs)
	}
}

impl<E, T> Ord for BitVec<E, T>
where E: Endian, T: Bits {
	fn cmp(&self, rhs: &Self) -> Ordering {
		BitSlice::cmp(&self, &rhs)
	}
}

/// Add two `BitVec`s together, zero-extending the shorter.
///
/// `BitVec` addition works just like adding numbers longhand on paper. The
/// first bits in the `BitVec` are the highest, so addition works from right to
/// left, and the shorter `BitVec` is assumed to be extended to the left with
/// zero.
///
/// The output `BitVec` may be one bit longer than the longer input, if addition
/// overflowed.
impl<E, T> Add for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	/// Add two `BitVec`s.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let a = bitvec![0, 1, 0, 1];
	/// let b = bitvec![0, 0, 1, 1];
	/// let s = a + b;
	/// assert_eq!(bitvec![1, 0, 0, 0], s);
	/// ```
	///
	/// This example demonstrates the addition of differently-sized `BitVec`s,
	/// and will overflow.
	///
	/// ```rust
	/// use bitvec::*;
	/// let a = bitvec![1; 4];
	/// let b = bitvec![1; 1];
	/// let s = b + a;
	/// assert_eq!(bitvec![1, 0, 0, 0, 0], s);
	/// ```
	fn add(mut self, addend: Self) -> Self::Output {
		self += addend;
		self
	}
}

/// Add another `BitVec` into `self`, zero-extending the shorter.
///
/// `BitVec` addition works just like adding numbers longhand on paper. The
/// first bits in the `BitVec` are the highest, so addition works from right to
/// left, and the shorter `BitVec` is assumed to be extended to the left with
/// zero.
///
/// The output `BitVec` may be one bit longer than the longer input, if addition
/// overflowed.
impl<E, T> AddAssign for BitVec<E, T>
where E: Endian, T: Bits {
	/// Add another `BitVec` into `self`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut a = bitvec![1, 0, 0, 1];
	/// let b = bitvec![0, 1, 1, 1];
	/// a += b;
	/// assert_eq!(a, bitvec![1, 0, 0, 0, 0]);
	/// ```
	fn add_assign(&mut self, mut addend: Self) {
		use std::iter::repeat;
		//  If the other vec is longer, swap them and try again.
		if addend.len() > self.len() {
			mem::swap(self, &mut addend);
			return *self += addend;
		}
		//  Now that self.len() >= addend.len(), proceed with addition.
		//
		//  I don't, at this time, want to implement a carry-lookahead adder in
		//  software, so this is going to be a plain ripple-carry adder with
		//  O(n) runtime. Furthermore, until I think of an optimization
		//  strategy, it is going to build up another bitvec to use as a stack.
		//
		//  Computers are fast. Whatever.
		let mut c = false;
		let mut stack = BitVec::<E, T>::with_capacity(self.len());
		//  Reverse self, reverse addend and zero-extend, and zip both together.
		//  This walks both vecs from rightmost to leftmost, and considers an
		//  early expiration of addend to continue with 0 bits.
		//
		//  100111
		// +  0010
		//  ^^---- semantically zero
		for (a, b) in self.iter().rev().zip(addend.into_iter().rev().chain(repeat(false))) {
			//  Addition is a finite state machine that can be precomputed into a single
			//  jump table rather than requiring more complex branching.
			//  The table is indexed as (carry, a, b).
			static JUMP: [u8; 8] = [
				//  0 + 0 + 0 = 0, 0
				0,
				//  0 + 1 + 0 = 1, 0
				2,
				//  1 + 0 + 0 = 1, 0
				2,
				//  1 + 1 + 1 = 0, 1
				1,
				//  0 + 0 + 1 = 1, 0
				2,
				//  0 + 1 + 0 = 0, 1
				1,
				//  1 + 0 + 0 = 0, 1
				1,
				//  1 + 1 + 1 = 1, 1
				3,
			];
			let idx = ((c as u8) << 2) | ((a as u8) << 1) | (b as u8);
			let yz = JUMP[idx as usize];
			let (y, z) = (yz & 2 == 2, yz & 1 == 1);
			//  Note: I checked in Godbolt, and the above comes out to ten
			//  simple instructions with the JUMP baked in as immediate values.
			//  The more semantically clear match statement does not optimize
			//  nearly as well.
			stack.push(y);
			c = z;
		}
		//  If the carry made it to the end, push it.
		if c {
			stack.push(true);
		}
		//  Unwind the stack into `self`.
		self.clear();
		while let Some(bit) = stack.pop() {
			self.push(bit);
		}
	}
}

/// Subtract one `BitVec` from another assuming 2's-complement encoding.
///
/// Subtraction is a more complex operation than addition. The bit-level work is
/// largely the same, but semantic distinctions must be made. Unlike addition,
/// which is commutative and tolerant of switching the order of the addends,
/// subtraction cannot swap the minuend (LHS) and subtrahend (RHS).
///
/// Because of the properties of 2's-complement arithmetic, M - S is equivalent
/// to M + (!S + 1). Subtraction therefore bitflips the subtrahend and adds one.
/// This may, in a degenerate case, cause the subtrahend to increase in length.
///
/// Once the subtrahend is stable, the minuend zero-extends its left side in
/// order to match the length of the subtrahend if needed (this is provided by
/// the `>>` operator).
///
/// When the minuend is stable, the minuend and subtrahend are added together
/// by the `<BitVec as Add>` implementation. The output will be encoded in
/// 2's-complement, so a leading one means that the output is considered
/// negative.
///
/// Interpreting the contents of a `BitVec` as an integer is beyond the scope of
/// this crate.
impl<E, T> Sub for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	/// Subtract one `BitVec` from another.
	///
	/// # Examples
	///
	/// Minuend larger than subtrahend, positive difference.
	///
	/// ```rust
	/// use bitvec::*;
	/// let a = bitvec![1, 0];
	/// let b = bitvec![   1];
	/// let c = a - b;
	/// assert_eq!(bitvec![0, 1], c);
	/// ```
	///
	/// Minuend smaller than subtrahend, negative difference.
	///
	/// ```rust
	/// use bitvec::*;
	/// let a = bitvec![   1];
	/// let b = bitvec![1, 0];
	/// let c = a - b;
	/// assert_eq!(bitvec![1, 1], c);
	/// ```
	///
	/// Subtraction from self is correctly handled.
	///
	/// ```rust
	/// use bitvec::*;
	/// let a = bitvec![1; 4];
	/// let b = a.clone();
	/// let c = a - b;
	/// assert!(c.none(), "{:?}", c);
	/// ```
	fn sub(mut self, subtrahend: Self) -> Self::Output {
		self -= subtrahend;
		self
	}
}

impl<E, T> SubAssign for BitVec<E, T>
where E: Endian, T: Bits {
	fn sub_assign(&mut self, mut subtrahend: Self) {
		//  Invert the subtrahend in preparation for addition
		subtrahend = -subtrahend;
		let (llen, rlen) = (self.len(), subtrahend.len());
		//  If the subtrahend is longer than the minuend, 0-extend the minuend.
		if rlen > llen {
			let diff = rlen - llen;
			*self >>= diff;
			*self += subtrahend;
		}
		//  If the minuend is longer than the subtrahend, 1-extend the
		//  subtrahend.
		else if llen > rlen {
			let diff = llen - rlen;
			subtrahend >>= diff;
			//  Implementing BitVec >> (usize, bool) would permit sign extension
			//  in fewer steps.
			for idx in 0 .. diff {
				subtrahend.set(idx, true);
			}
			let old = self.len();
			*self += subtrahend;
			//  If the subtraction emitted a carry, remove it.
			if self.len() > old {
				*self <<= 1;
			}
		}
	}
}

__bitvec_shift!(u8, u16, u32, u64, i8, i16, i32, i64);

/// Shift all bits in the vector to the left – DOWN AND TOWARDS THE FRONT.
///
/// On primitives, the left-shift operator `<<` moves bits away from origin and
/// towards the ceiling. This is because we label the bits in a primitive with
/// the minimum on the right and the maximum on the left, which is big-endian
/// bit order. This increases the value of the primitive being shifted.
///
/// **THAT IS NOT HOW `BITVEC` WORKS!**
///
/// `BitVec` defines its layout with the minimum on the left and the maximum on
/// the right! Thus, left-shifting moves bits towards the **minimum**.
///
/// In BigEndian order, the effect in memory will be what you expect the `<<`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `>>` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effects in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The length of the vector is decreased by the shift amount.
///
/// If the shift amount is greater than the length, the vector calls `clear()`
/// and zeroes its memory. This is *not* an error.
impl<E, T> Shl<usize> for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	/// Shift a `BitVec` to the left, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("000111", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let ls = bv << 2usize;
	/// assert_eq!("0111", &format!("{}", ls));
	/// assert_eq!(0b0111_0000, ls.as_ref()[0]);
	/// assert_eq!(ls.len(), 4);
	/// ```
	fn shl(mut self, shamt: usize) -> Self::Output {
		self <<= shamt;
		self
	}
}

/// Shift all bits in the vector to the left – DOWN AND TOWARDS THE FRONT.
///
/// On primitives, the left-shift operator `<<` moves bits away from origin and
/// towards the ceiling. This is because we label the bits in a primitive with
/// the minimum on the right and the maximum on the left, which is big-endian
/// bit order. This increases the value of the primitive being shifted.
///
/// **THAT IS NOT HOW `BITVEC` WORKS!**
///
/// `BitVec` defines its layout with the minimum on the left and the maximum on
/// the right! Thus, left-shifting moves bits towards the **minimum**.
///
/// In BigEndian order, the effect in memory will be what you expect the `<<`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `>>` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effects in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The length of the vector is decreased by the shift amount.
///
/// If the shift amount is greater than the length, the vector calls `clear()`
/// and zeroes its memory. This is *not* an error.
impl<E, T> ShlAssign<usize> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Shift a `BitVec` to the left in place, shortening it.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![LittleEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("000111", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv <<= 2;
	/// assert_eq!("0111", &format!("{}", bv));
	/// assert_eq!(0b0000_1110, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 4);
	/// ```
	fn shl_assign(&mut self, shamt: usize) {
		let len = self.len();
		if shamt >= len {
			self.clear();
			let buf = self.as_mut();
			let ptr = buf.as_mut_ptr();
			let len = buf.len();
			unsafe { ::std::ptr::write_bytes(ptr, 0, len); }
			return;
		}
		for idx in shamt .. len {
			let val = self.get(idx);
			self.set(idx - shamt, val);
		}
		let trunc = len - shamt;
		for idx in trunc .. len {
			self.set(idx, false);
		}
		self.truncate(trunc);
	}
}

/// Shift all bits in the vector to the right – UP AND TOWARDS THE BACK.
///
/// On primitives, the right-shift operator `>>` moves bits towards the origin
/// and away from the ceiling. This is because we label the bits in a primitive
/// with the minimum on the right and the maximum on the left, which is
/// big-endian bit order. This decreases the value of the primitive being
/// shifted.
///
/// **THAT IS NOT HOW `BITVEC` WORKS!**
///
/// `BitVec` defines its layout with the minimum on the left and the maximum on
/// the right! Thus, right-shifting moves bits towards the **maximum**.
///
/// In BigEndian order, the effect in memory will be what you expect the `>>`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `<<` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effects in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The length of the vector is increased by the shift amount.
///
/// If the new length of the vector would overflow, a panic occurs. This *is* an
/// error.
impl<E, T> Shr<usize> for BitVec<E, T>
where E: Endian, T: Bits {
	type Output = Self;

	/// Shift a `BitVec` to the right, lengthening it and filling the front with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("000111", &format!("{}", bv));
	/// assert_eq!(0b0001_1100, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 6);
	/// let rs = bv >> 2usize;
	/// assert_eq!("00000111", &format!("{}", rs));
	/// assert_eq!(0b0000_0111, rs.as_ref()[0]);
	/// assert_eq!(rs.len(), 8);
	/// ```
	fn shr(mut self, shamt: usize) -> Self::Output {
		self >>= shamt;
		self
	}
}

/// Shift all bits in the vector to the right – UP AND TOWARDS THE BACK.
///
/// On primitives, the right-shift operator `>>` moves bits towards the origin
/// and away from the ceiling. This is because we label the bits in a primitive
/// with the minimum on the right and the maximum on the left, which is
/// big-endian bit order. This decreases the value of the primitive being
/// shifted.
///
/// **THAT IS NOT HOW `BITVEC` WORKS!**
///
/// `BitVec` defines its layout with the minimum on the left and the maximum on
/// the right! Thus, right-shifting moves bits towards the **maximum**.
///
/// In BigEndian order, the effect in memory will be what you expect the `>>`
/// operator to do.
///
/// **In LittleEndian order, the effect will be equivalent to using `<<` on**
/// **the primitives in memory!**
///
/// # Notes
///
/// In order to preserve the effects in memory that this operator traditionally
/// expects, the bits that are emptied by this operation are zeroed rather than
/// left to their old value.
///
/// The length of the vector is increased by the shift amount.
///
/// If the new length of the vector would overflow, a panic occurs. This *is* an
/// error.
impl<E, T> ShrAssign<usize> for BitVec<E, T>
where E: Endian, T: Bits {
	/// Shift a `BitVec` to the right in place, lengthening it and filling the
	/// front with 0.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let mut bv = bitvec![LittleEndian, u8; 0, 0, 0, 1, 1, 1];
	/// assert_eq!("000111", &format!("{}", bv));
	/// assert_eq!(0b0011_1000, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 6);
	/// bv >>= 2;
	/// assert_eq!("00000111", &format!("{}", bv));
	/// assert_eq!(0b1110_0000, bv.as_ref()[0]);
	/// assert_eq!(bv.len(), 8);
	/// ```
	fn shr_assign(&mut self, shamt: usize) {
		let old_len = self.len();
		for _ in 0 .. shamt {
			self.push(false);
		}
		for idx in (0 .. old_len).rev() {
			let val = self.get(idx);
			self.set(idx + shamt, val);
		}
		for idx in 0 .. shamt {
			self.set(idx, false);
		}
	}
}

/// Iterate over an owned `BitVec`.
#[doc(hidden)]
pub struct IntoIter<E, T>
where E: Endian, T: Bits {
	bv: BitVec<E, T>,
	head: usize,
	tail: usize,
}

impl<E, T> IntoIter<E, T>
where E: Endian, T: Bits {
	fn new(bv: BitVec<E, T>) -> Self {
		let tail = bv.len();
		Self {
			bv,
			head: 0,
			tail,
		}
	}

	fn reset(&mut self) {
		self.head = 0;
		self.tail = self.bv.len();
	}
}

impl<E, T> DoubleEndedIterator for IntoIter<E, T>
where E: Endian, T: Bits {
	/// Yield the back-most bit of the collection.
	///
	/// This iterator is self-resetting; when the cursor reaches the front of
	/// the collection, it returns None after setting the cursor to the length
	/// of the underlying collection. If the collection is not empty when this
	/// occurs, then the iterator will resume at the back if called again.
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.tail > self.head && self.tail <= self.bv.len() {
			self.tail -= 1;
			Some(self.bv[self.tail])
		}
		else {
			self.reset();
			None
		}
	}
}

impl<E, T> ExactSizeIterator for IntoIter<E, T>
where E: Endian, T: Bits {
	//  Override the default implementation with a fixed calculation. The type
	//  is guaranteed to be well-behaved, so there is no point in building two
	//  copies of the remnant, checking an always-safe condition, and dropping
	//  one.
	//
	//  THIS IS A LOAD BEARING OVERRIDE! IF IT IS REMOVED, THEN
	//  Iterator::size_hint MUST BE CHANGED TO NOT CALL THIS FUNCTION, BECAUSE
	//  THE DEFAULT IMPLEMENTATION CALLS Iterator::size_hint! FAILURE TO DO SO
	//  WILL RESULT IN A VALID COMPILE AND A BLOWN STACK AT RUNTIME DUE TO
	//  INFINITE MUTUAL RECURSION!
	fn len(&self) -> usize {
		self.tail - self.head
	}
}

impl<E, T> From<BitVec<E, T>> for IntoIter<E, T>
where E: Endian, T: Bits {
	fn from(bv: BitVec<E, T>) -> Self {
		Self::new(bv)
	}
}

impl<E, T> Iterator for IntoIter<E, T>
where E: Endian, T: Bits {
	type Item = bool;

	/// Advance the iterator forward, yielding the front-most bit.
	///
	/// This iterator is self-resetting: when the cursor reaches the back of the
	/// collection, it returns None after setting the cursor to zero. If the
	/// collection is not empty when this occurs, then the iterator will resume
	/// at the front if called again.
	fn next(&mut self) -> Option<Self::Item> {
		if self.head < self.tail {
			let ret = self.bv[self.head];
			self.head += 1;
			Some(ret)
		}
		else {
			self.reset();
			None
		}
	}

	//  Note that the default ExactSizeIterator::len calls this method, so
	//  removing that implementation will cause an infinite mutual recursion,
	//  only detectable *at runtime* when the stack blows.
	//
	//  THIS METHOD MUST BE CHANGED TO NOT CALL ExactSizeIterator::len BEFORE
	//  REMOVING THE SPECIALIZATION FOR ESI! THE DEFAULT IMPLEMENTATION OF ESI
	//  CALLS THIS FUNCTION, WHICH WILL COMPILE CLEANLY AND THEN BLOW THE STACK
	//  AT RUNTIME DUE TO INFINITE MUTUAL RECURSION!
	fn size_hint(&self) -> (usize, Option<usize>) {
		let rem = ExactSizeIterator::len(self);
		(rem, Some(rem))
	}

	/// Count how many bits are live in the iterator, consuming it.
	///
	/// You are probably looking to use this on a borrowed iterator rather than
	/// an owning iterator. See `BitSlice`.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 1, 0, 1, 0];
	/// assert_eq!(bv.into_iter().count(), 5);
	/// ```
	fn count(self) -> usize {
		ExactSizeIterator::len(&self)
	}

	/// Advance the iterator by `n` bits, starting from zero.
	///
	/// It is not an error to advance past the end of the iterator! Doing so
	/// returns `None`, and resets the iterator to its beginning.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// let mut bv_iter = bv.into_iter();
	/// assert_eq!(bv_iter.len(), 4);
	/// assert!(bv_iter.nth(3).unwrap());
	/// ```
	///
	/// This example intentionally overshoots the iterator bounds, which causes
	/// a reset to the initiol state. It then demonstrates that `nth` is
	/// stateful, and is not an absolute index, by seeking ahead by two (to the
	/// third zero bit) and then taking the bit immediately after it, which is
	/// set. This shows that the argument to `nth` is how many bits to discard
	/// before yielding the next.
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// let mut bv_iter = bv.into_iter();
	/// assert!(bv_iter.nth(4).is_none());
	/// assert!(!bv_iter.nth(2).unwrap());
	/// assert!(bv_iter.nth(0).unwrap());
	/// ```
	fn nth(&mut self, n: usize) -> Option<bool> {
		self.head += n;
		self.next()
	}

	/// Consume the iterator, returning only the last bit.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![BigEndian, u8; 0, 0, 0, 1];
	/// assert!(bv.into_iter().last().unwrap());
	/// ```
	///
	/// Empty iterators return `None`
	///
	/// ```rust
	/// use bitvec::*;
	/// let bv = bitvec![];
	/// assert!(bv.into_iter().last().is_none());
	/// ```
	fn last(mut self) -> Option<bool> {
		self.next_back()
	}
}
