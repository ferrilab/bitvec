use core::{
	fmt::{
		self,
		Debug,
		Formatter,
	},
	mem::ManuallyDrop,
	ops::Drop,
	sync::atomic::Ordering,
};

use radium::Radium;
use tap::{
	Pipe,
	TapOptional,
};

use super::{
	boxed::BitRefHandle,
	BitRefStrong,
};
use crate::{
	order::BitOrder,
	ptr::BitSpan,
	slice::BitSlice,
	store::BitStore,
};

#[repr(transparent)]
pub struct BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Weak handles can be constructed without creating a referent box, so this
	/// must be optional to denote the case where they are awaiting a target.
	pub(super) inner: Option<BitRefHandle<R, O, T>>,
}

impl<R, O, T> BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	/// Constructs a new weak handle without allocating any memory. Calling
	/// [`upgrade`] on the return value always gives [`None`].
	///
	/// # Original
	///
	/// [`Weak::new`](alloc::rc::Weak::new)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let empty = BitRcWeak::<Msb0, u8>::new();
	/// assert!(empty.upgrade().is_none());
	/// ```
	///
	/// [`upgrade`]: Self::upgrade
	#[inline(always)]
	pub fn new() -> Self {
		Self { inner: None }
	}

	/// Returns a raw pointer to the `BitSlice` pointed to by this handle.
	///
	/// The pointer is only valid if there are some strong handles. The pointer
	/// may be dangling or even null otherwise.
	///
	/// # Original
	///
	/// [`Weak::as_ptr`](alloc::rc::Weak::as_ptr)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	/// use core::ptr;
	///
	/// let strong = bitrc![1, 0, 1, 1, 0];
	/// let weak = BitRc::downgrade(&strong);
	///
	/// // Both point to the same allocation
	/// assert!(ptr::eq(&*strong, weak.as_ptr()));
	/// // The strong here keeps it alive, so we can still access the bit-slice.
	/// assert_eq!(bits![1, 0, 1, 1, 0], unsafe { &*weak.as_ptr() });
	///
	/// drop(strong);
	/// // But not anymore. We can do weak.as_ptr(), but accessing the pointer
	/// // would lead to undefined behavior.
	/// // assert_eq!(bits![1, 0, 1, 1, 0], unsafe { &*weak.as_ptr() });
	/// ```
	#[inline]
	pub fn as_ptr(&self) -> *const BitSlice<O, T> {
		match self.inner {
			Some(brh) => brh.ptr,
			None => BitSpan::EMPTY,
		}
		.to_bitslice_ptr()
	}

	/// Consumes the weak handle and turns it into a raw pointer.
	///
	/// This converts the weak pointer into a raw pointer, while still
	/// preserving the ownership of one weak reference (the weak count is not
	/// modified by this operation). It can be turned back into the weak handle
	/// with [`from_raw`].
	///
	/// The same restrictions of accessing the target of the pointer as with
	/// [`as_ptr`] apply.
	///
	/// # Original
	///
	/// [`Weak::into_raw`](alloc::rc::Weak::into_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let strong = bitrc![1, 0, 1, 1, 0];
	/// let weak = BitRc::downgrade(&strong);
	/// let raw = weak.into_raw();
	///
	/// assert_eq!(1, BitRc::weak_count(&strong));
	/// assert_eq!(bits![1, 0, 1, 1, 0], unsafe { &*raw });
	///
	/// drop(unsafe { BitRcWeak::from_raw(raw) });
	/// assert_eq!(0, BitRc::weak_count(&strong));
	/// ```
	///
	/// [`from_raw`]: Self::from_raw
	/// [`as_ptr`]: Self::as_ptr
	#[inline]
	pub fn into_raw(self) -> *const BitSlice<O, T> {
		self.pipe(ManuallyDrop::new).as_ptr()
	}

	/// Converts a raw pointer previously created by [`into_raw`] back into a
	/// weak handle.
	///
	/// This can be used to safely get a strong reference (by calling
	/// [`upgrade`] later) or to deallocate the weak count by dropping the weak
	/// handle.
	///
	/// It takes ownership of one weak reference (with the exception of pointers
	/// created by [`new`], as these don't own anything; the method still works
	/// on them).
	///
	/// # Safety
	///
	/// The pointer must have originated from the [`into_raw`] and must still
	/// own its potential weak reference.
	///
	/// It is allowed for the strong count to be 0 at the time of calling this.
	/// Nevertheless, this takes ownership of one weak reference currently
	/// represented as a raw pointer (the weak count is not modified by this
	/// operation) and therefore it must be paired with a previous
	/// call to [`into_raw`].
	///
	/// # Original
	///
	/// [`Weak::from_raw`](alloc::rc::Weak::from_raw)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let strong = bitrc![1, 0, 1, 1, 0];
	///
	/// let raw_1 = BitRc::downgrade(&strong).into_raw();
	/// let raw_2 = BitRc::downgrade(&strong).into_raw();
	///
	/// assert_eq!(2, BitRc::weak_count(&strong));
	///
	/// assert_eq!(
	///   bits![1, 0, 1, 1, 0],
	///   &*unsafe { BitRcWeak::from_raw(raw_1) }.upgrade().unwrap(),
	/// );
	/// assert_eq!(1, BitRc::weak_count(&strong));
	///
	/// drop(strong);
	///
	/// // Decrement the last weak count.
	/// assert!(unsafe { BitRcWeak::from_raw(raw_2) }.upgrade().is_none());
	/// ```
	///
	/// [`new`]: Self::new
	/// [`into_raw`]: Self::into_raw
	/// [`upgrade`]: Self::upgrade
	/// [`forget`]: std::mem::forget
	#[inline]
	pub unsafe fn from_raw(ptr: *const BitSlice<O, T>) -> Self {
		Self {
			inner: if ptr == BitSlice::<O, T>::empty() {
				None
			}
			else {
				Some(BitRefHandle::from_raw(ptr))
			},
		}
	}

	/// Attempts to upgrade the `Weak` handle to a [`Strong`] handle.
	///
	/// Returns [`None`] if all strong handles to the bit-slice have previously
	/// been dropped.
	///
	/// # Original
	///
	/// [`Weak::upgrade`](alloc::rc::Weak::upgrade)
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let bits = bitrc![1, 0, 1, 1, 0];
	/// let weak = BitRc::downgrade(&bits);
	///
	/// let strong = weak.upgrade().unwrap();
	///
	/// // destroy all strong handles
	/// drop(strong);
	/// drop(bits);
	///
	/// assert!(weak.upgrade().is_none());
	/// ```
	///
	/// [`Strong`]: crate::rc::BitRefStrong
	#[inline]
	pub fn upgrade(&self) -> Option<BitRefStrong<R, O, T>> {
		let inner = self.inner?;
		let counters = inner.get_counters();

		//  See `alloc::sync::Weak::upgrade`.

		//  Fetch the current strong count.
		let mut n = counters.strong.load(Ordering::Relaxed);

		loop {
			//  If there are no strong handles, exit immediately.
			if n == 0 {
				return None;
			}

			/* Otherwise, because there are other strong handles, those handles
			could have updated the strong count before reaching this point. The
			CAS loop ensures that our view of the strong count is always
			consistent and up-to-date. This attempts to increment the strong
			count, but if the count has changed since we last saw it, the loop
			restarts.
			*/
			match counters.strong.compare_exchange_weak(
				n,
				n + 1,
				Ordering::Acquire,
				Ordering::Relaxed,
			) {
				Ok(_) => return Some(BitRefStrong { inner }),
				Err(old) => n = old,
			}
		}
	}

	/// Gets the number of strong handles pointing to this allocation.
	////
	/// If `self` was created using `BitRefWeak::new`, this will return 0.
	///
	/// # Original
	///
	/// [`Weak::strong_count`](alloc::rc::Weak::strong_count)

	#[inline]
	pub fn strong_count(&self) -> usize {
		match self.inner {
			Some(brh) => brh.get_counters().get_strong(),
			None => 0,
		}
	}

	/// Gets an approximation of the number of weak handles pointing to this
	/// allocation.
	///
	/// If `self` was created using [`BitRefWeak::new`], or if there are no
	/// remaining strong handles, this will return 0.
	///
	/// # Accuracy
	///
	/// Due to implementation details, the returned value can be off by 1 in
	/// either direction when other threads are manipulating any `BitRefStrong`s
	/// or `BitRefWeak`s pointing to the same allocation.
	///
	/// # Original
	///
	/// [`Weak::weak_count`](alloc::rc::Weak::weak_count)
	#[inline]
	pub fn weak_count(&self) -> usize {
		match self.inner {
			Some(brh) => {
				let counters = brh.get_counters();
				// Snapshot the weak count
				let weak = counters.get_weak();
				// If the strong count is zero, return zero immediately.
				if counters.get_strong() == 0 {
					0
				}
				//  If it is not, then the weak count includes the implicit-weak
				//  held by the strongs, and must be decremented.
				else {
					weak - 1
				}
			},
			None => 0,
		}
	}

	/// Returns `true` if the two weak handles point to the same allocation
	/// (similar to [`ptr::eq`]), or if both don't point to any allocation
	/// (because they were created with `BitRefWeak::new()`).
	///
	/// # Original
	///
	/// [`Weak::ptr_eq`](alloc::rc::Weak::ptr_eq)
	///
	/// # Notes
	///
	/// Since this compares pointers it means that `BitRefWeak::new()` will
	/// equal each other, even though they don't point to any allocation.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let first_rc = bitrc![1, 0, 1, 1, 0];
	/// let first = BitRc::downgrade(&first_rc);
	/// let second = BitRc::downgrade(&first_rc);
	///
	/// assert!(first.ptr_eq(&second));
	///
	/// let third_rc = bitrc![1, 0, 1, 1, 0];
	/// let third = BitRc::downgrade(&third_rc);
	///
	/// assert!(!first.ptr_eq(&third));
	/// ```
	///
	/// Comparing `BitRefWeak::new`.
	///
	/// ```rust
	/// use bitvec::{prelude::*, rc::*};
	///
	/// let first = BitRcWeak::new();
	/// let second = BitRcWeak::new();
	/// assert!(first.ptr_eq(&second));
	///
	/// let third_rc = bitrc![1, 0];
	/// let third = BitRc::downgrade(&third_rc);
	/// assert!(!first.ptr_eq(&third));
	/// ```
	///
	/// [`ptr::eq`]: crate::ptr::eq
	#[inline]
	pub fn ptr_eq(&self, other: &Self) -> bool {
		self.inner == other.inner
	}
}

impl<R, O, T> Clone for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.tap_some(|brh| {
				brh.get_counters().incr_weak();
			}),
		}
	}
}

impl<R, O, T> Default for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn default() -> Self {
		Self::new()
	}
}

impl<R, O, T> Debug for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	#[inline]
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		write!(fmt, "(Weak)")
	}
}

unsafe impl<R, O, T> Send for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync + Send,
{
}

unsafe impl<R, O, T> Sync for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize> + Sync,
	O: BitOrder,
	T: BitStore + Sync + Send,
{
}

impl<R, O, T> Drop for BitRefWeak<R, O, T>
where
	R: Radium<Item = usize>,
	O: BitOrder,
	T: BitStore,
{
	fn drop(&mut self) {
		if let Some(mut inner) = self.inner {
			if inner.get_counters().decr_weak() == 1 {
				inner.dealloc()
			}
		}
	}
}
