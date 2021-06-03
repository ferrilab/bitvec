use alloc::borrow::Cow;
use core::{
	borrow::Borrow,
	cmp,
	convert::AsRef,
	fmt::{
		self,
		Debug,
		Display,
		Formatter,
		LowerHex,
		Octal,
		Pointer,
		UpperHex,
	},
	hash::{
		Hash,
		Hasher,
	},
	iter::FromIterator,
	ops::{
		Deref,
		Drop,
	},
	pin::Pin,
};

use radium::Radium;
use tap::Pipe;

use super::{
	boxed::BitRefHandle,
	BitRefWeak,
};
use crate::{
	boxed::BitBox,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

#[repr(transparent)]
pub struct BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	pub(super) inner: BitRefHandle<R, O, T>,
}

impl<R, O, T> BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	#[cfg(not(tarpaulin_include))]
	#[deprecated = "Prefer `from_bitslice`"]
	pub fn new(bits: &BitSlice<O, T>) -> Self {
		Self::from_bitslice(bits)
	}

	#[inline]
	#[cfg(not(tarpaulin_include))]
	pub fn pin(bits: &BitSlice<O, T>) -> Pin<Self> {
		bits.pipe(Self::from_bitslice)
			.pipe(|x| unsafe { Pin::new_unchecked(x) })
	}

	/// Copies a [`BitSlice`] into a new reference-counted heap allocation.
	///
	/// # Parameters
	///
	/// - `bits`: Any borrowed `BitSlice` region.
	///
	/// # Returns
	///
	/// A strong handle to a newly-allocated `BitSlice` region.
	///
	/// [`BitSlice`]: crate::slice::BitSlice
	#[inline(always)]
	pub fn from_bitslice(bits: &BitSlice<O, T>) -> Self {
		Self {
			inner: BitRefHandle::alloc(bits),
		}
	}

	/// Accesses the contained [`BitSlice`].
	///
	/// [`BitSlice]: crate::slice::BitSlice
	#[inline]
	pub fn as_bitslice(this: &Self) -> &BitSlice<O, T> {
		this.inner.ptr.to_bitslice_ref()
	}

	/// Consumes the `BitRefStrong`, returning the wrapped bit-slice pointer.
	///
	/// To avoid a memory leak, the pointer must be converted back into a
	/// reference handle using [`Self::from_raw`].
	///
	/// # Original
	///
	/// [`Rc::into_raw`](alloc::rc::Rc::into_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let x = bitrc![1, 0, 1, 1];
	/// let x_ptr = BitRc::into_raw(x);
	/// assert_eq!(unsafe { &*x_ptr }, bits![1, 0, 1, 1]);
	/// ```
	#[inline]
	pub fn into_raw(this: Self) -> *const BitSlice<O, T> {
		Self::as_ptr(&this)
	}

	/// Provides a raw pointer to the [`BitSlice`] data.
	///
	/// The counts are not affected in any way and the `BitRefStrong` is not
	/// consumed. The pointer is valid for as long there are strong counts in
	/// the allocation.
	///
	/// # Original
	///
	/// [`Rc::as_ptr`](alloc::rc::Rc::as_ptr)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let x = bitrc![1, 0, 1, 1];
	/// let y = BitRc::clone(&x);
	/// let x_ptr = BitRc::as_ptr(&x);
	///
	/// assert_eq!(x_ptr, BitRc::as_ptr(&y));
	/// assert_eq!(unsafe { &*x_ptr }, bits![1, 0, 1, 1]);
	/// ```
	#[inline]
	pub fn as_ptr(this: &Self) -> *const BitSlice<O, T> {
		this.inner.ptr.to_bitslice_ptr()
	}

	/// Constructs a `BitRefStrong` from a raw pointer.
	///
	/// # Safety
	///
	/// The raw pointer **must** have been previously constructed by calling
	/// [`Self::into_raw`]. Any other production of a bit-slice pointer will
	/// result in memory unsafety.
	///
	/// Producing a pointer from a reference-counted buffer without forgetting
	/// the handle (such as [`Self::as_ptr`]) will result in an incorrect number
	/// of strong counts, and permit dangling pointers to possibly-deällocated
	/// memory.
	///
	/// Producing a pointer from some other bit-slice that is *not* a
	/// reference-counted buffer will break the allocator.
	///
	/// # Original
	///
	/// [`Rc::from_raw`](alloc::rc::Rc::from_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let x = bitrc![1, 0, 1, 1, 0];
	/// let x_ptr = BitRc::into_raw(x);
	///
	/// unsafe {
	///   // Convert back to a `BitRc` to prevent leak.
	///   let x = BitRc::from_raw(x_ptr);
	///   assert_eq!(&*x, bits![1, 0, 1, 1, 0]);
	///
	///   // Further calls to `BitRc::from_raw(x_ptr)`
	///   // would be memory-unsafe.
	/// }
	///
	/// // The memory was freed when `x` went out of
	/// // scope above, so `x_ptr` is now dangling!
	/// ```
	#[inline]
	pub unsafe fn from_raw(ptr: *const BitSlice<O, T>) -> Self {
		Self {
			inner: BitRefHandle::from_raw(ptr),
		}
	}

	/// Creates a new [`Weak`] handle to this allocation.
	///
	/// # Original
	///
	/// [`Rc::downgrade`](alloc::rc::Rc::downgrade)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let strong = bitrc![1, 0, 1, 0, 0];
	///
	/// let weak = BitRc::downgrade(&strong);
	/// ```
	///
	/// [`Weak`]: crate::rc::BitRefWeak
	#[inline]
	pub fn downgrade(this: &Self) -> BitRefWeak<R, O, T> {
		this.inner.get_counters().incr_weak();
		BitRefWeak {
			inner: Some(this.inner),
		}
	}

	/// Gets the number of [`Weak`] handles to this allocation.
	///
	/// # Original
	///
	/// [`Rc::weak_count`](alloc::rc::Rc::weak_count)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let bits = bitrc![1, 0, 1, 1, 0];
	/// assert_eq!(BitRc::weak_count(&bits), 0);
	///
	/// let _weak = BitRc::downgrade(&bits);
	/// assert_eq!(BitRc::weak_count(&bits), 1);
	/// ```
	///
	/// [`Weak`]: crate::rc::BitRefWeak
	#[inline]
	pub fn weak_count(this: &Self) -> usize {
		this.inner.get_counters().get_weak() - 1
	}

	/// Gets the number of strong handles to this allocation.
	///
	/// # Original
	///
	/// [`Rc::strong_count`](alloc::rc::Rc::strong_count)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let bits = bitrc![1, 0, 1, 1, 0];
	/// assert_eq!(BitRc::strong_count(&bits), 1);
	///
	/// let also_bits = BitRc::clone(&bits);
	/// assert_eq!(BitRc::strong_count(&also_bits), 2);
	/// ```
	#[inline]
	pub fn strong_count(this: &Self) -> usize {
		this.inner.get_counters().get_strong()
	}

	/// Returns a mutable reference into the given ref-counted bit-slice, if
	/// there are no other handles to the same allocation.
	///
	/// Returns [`None`] otherwise, because it is not safe to mutate a shared
	/// value.
	///
	/// See also [`Self::make_mut`], which will clone the inner value when there
	/// are other handles.
	///
	/// # Original
	///
	/// [`Rc::get_mut`](alloc::rc::Rc::get_mut)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let mut x = bitrc![0; 5];
	/// BitRc::get_mut(&mut x).unwrap().set(0, true);
	/// assert_eq!(*x, bits![1, 0, 0, 0, 0]);
	///
	/// let _y = BitRc::clone(&x);
	/// assert!(BitRc::get_mut(&mut x).is_none());
	/// ```
	#[inline]
	pub fn get_mut(this: &mut Self) -> Option<&mut BitSlice<O, T>> {
		if Self::is_unique(this) {
			unsafe { Some(Self::get_mut_unchecked(this)) }
		}
		else {
			None
		}
	}

	#[inline]
	pub(crate) unsafe fn get_mut_unchecked(
		this: &mut Self,
	) -> &mut BitSlice<O, T> {
		this.inner.ptr.to_bitslice_mut()
	}

	/// Makes a mutable reference into the given ref-counted bit-slice.
	///
	/// If there are any other handles, strong or weak, to the buffer, then the
	/// buffer is copied into a new allocation and `this` is updated to point to
	/// it. If there are no other handles, then a reference to the buffer
	/// contents is returned directly.
	///
	/// See also [`Self::get_mut`], which will fail rather than cloning.
	///
	/// # Original
	///
	/// [`Rc::make_mut`](alloc::rc::Rc::make_mut)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let mut data = bitrc![1, 0, 1, 1, 0];
	///
	/// // no alloc
	/// BitRc::make_mut(&mut data).set(1, true);
	/// // no alloc
	/// let mut other = BitRc::clone(&data);
	///
	/// // clones and modifies
	/// BitRc::make_mut(&mut data).set(4, true);
	/// // `data` and `other` now point to distinct buffers
	///
	/// // no alloc
	/// BitRc::make_mut(&mut data).set(0, false);
	/// // no alloc
	/// BitRc::make_mut(&mut other).set(2, false);
	/// ```
	///
	/// [`Weak`] handles will be disassociated:
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let mut data = bitrc![1, 0, 0, 1, 0];
	/// let weak = BitRc::downgrade(&data);
	///
	/// assert_eq!(*data, bits![1, 0, 0, 1, 0]);
	/// assert_eq!(*weak.upgrade().unwrap(), bits![1, 0, 0, 1, 0]);
	///
	/// BitRc::make_mut(&mut data).set(1, true);
	///
	/// assert_eq!(*data, bits![1, 1, 0, 1, 0]);
	/// assert!(weak.upgrade().is_none());
	/// ```
	///
	/// [`Weak`]: crate::rc::BitRefWeak
	#[inline]
	pub fn make_mut(this: &mut Self) -> &mut BitSlice<O, T> {
		if !Self::is_unique(this) {
			*this = Self::from_bitslice(&**this);
		}
		unsafe { Self::get_mut_unchecked(this) }
	}

	#[inline]
	pub(crate) fn is_unique(this: &Self) -> bool {
		Self::weak_count(this) == 0 && Self::strong_count(this) == 1
	}
}

impl<R, O, T> Borrow<BitSlice<O, T>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn borrow(&self) -> &BitSlice<O, T> {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> Clone for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn clone(&self) -> Self {
		self.inner.get_counters().incr_strong();
		Self { ..*self }
	}
}

impl<R, O, T> Eq for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}

impl<R, O, T> Ord for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		Self::as_bitslice(self).cmp(Self::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRefStrong<R, O2, T2>> for BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRefStrong<R, O2, T2>) -> bool {
		self == BitRefStrong::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRefStrong<R, O2, T2>> for &BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRefStrong<R, O2, T2>) -> bool {
		*self == BitRefStrong::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialEq<BitRefStrong<R, O2, T2>>
	for &mut BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn eq(&self, other: &BitRefStrong<R, O2, T2>) -> bool {
		**self == BitRefStrong::as_bitslice(other)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> PartialEq<Rhs> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialEq<BitSlice<O, T>>,
{
	#[inline]
	fn eq(&self, other: &Rhs) -> bool {
		other == Self::as_bitslice(self)
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O1, O2, T1, T2> PartialOrd<BitRefStrong<R, O2, T2>> for BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRefStrong<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRefStrong::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T, Rhs> PartialOrd<Rhs> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	Rhs: ?Sized + PartialOrd<BitSlice<O, T>>,
{
	#[inline]
	fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
		other.partial_cmp(Self::as_bitslice(self))
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, R, O1, O2, T1, T2> PartialOrd<BitRefStrong<R, O2, T2>>
	for &'a BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRefStrong<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRefStrong::as_bitslice(other))
	}
}

#[cfg(not(tarpaulin_include))]
impl<'a, R, O1, O2, T1, T2> PartialOrd<BitRefStrong<R, O2, T2>>
	for &'a mut BitSlice<O1, T1>
where
	R: Radium<Item = usize>,
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	#[inline]
	fn partial_cmp(
		&self,
		other: &BitRefStrong<R, O2, T2>,
	) -> Option<cmp::Ordering> {
		self.partial_cmp(BitRefStrong::as_bitslice(other))
	}
}

impl<R, O, T> AsRef<BitSlice<O, T>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn as_ref(&self) -> &BitSlice<O, T> {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> From<&BitSlice<O, T>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from(bits: &BitSlice<O, T>) -> Self {
		Self::from_bitslice(bits)
	}
}

impl<R, O, T> From<BitBox<O, T>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from(bits: BitBox<O, T>) -> Self {
		Self::from_bitslice(&*bits)
	}
}

impl<R, O, T> From<BitVec<O, T>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from(bits: BitVec<O, T>) -> Self {
		Self::from_bitslice(&*bits)
	}
}

impl<'a, R, O, T> From<Cow<'a, BitSlice<O, T>>> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn from(bits: Cow<'a, BitSlice<O, T>>) -> Self {
		Self::from_bitslice(bits.borrow())
	}
}

impl<R, O, T> Debug for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Debug::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Display for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Display::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> LowerHex for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		LowerHex::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Octal for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Octal::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T> Pointer for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		Pointer::fmt(&self.inner.ptr, fmt)
	}
}

impl<R, O, T> UpperHex for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		UpperHex::fmt(Self::as_bitslice(self), fmt)
	}
}

impl<R, O, T, I> FromIterator<I> for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
	BitVec<O, T>: FromIterator<I>,
{
	fn from_iter<II>(iter: II) -> Self
	where II: IntoIterator<Item = I> {
		Self::from(BitVec::<O, T>::from_iter(iter))
	}
}

#[cfg(not(tarpaulin_include))]
impl<R, O, T> Hash for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline(always)]
	fn hash<H>(&self, state: &mut H)
	where H: Hasher {
		Self::as_bitslice(self).hash(state)
	}
}

unsafe impl<R, O, T> Send for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync + Send,
{
}

unsafe impl<R, O, T> Sync for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync + Send,
{
}

impl<R, O, T> Unpin for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
}

impl<R, O, T> Deref for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	type Target = BitSlice<O, T>;

	#[inline]
	fn deref(&self) -> &Self::Target {
		Self::as_bitslice(self)
	}
}

impl<R, O, T> Drop for BitRefStrong<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn drop(&mut self) {
		if self.inner.get_counters().decr_strong() == 1 {
			drop(BitRefWeak {
				inner: Some(self.inner),
			});
		}
	}
}
