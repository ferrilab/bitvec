/*! Atomic Element Access

This module allows the `Bits` trait to access its storage elements as atomic
variants, in order to ensure parallel consistency.

This is necessary because while individual bit domains are forbidden from
parallel overlap by the Rust type system, CPUs do not have bit-level granularity
(that is the whole *raison d’être* of this crate), and so adjacent bit domains
that use the same storage element encounter race conditions.

The sequence of operations needed to modify a single bit is:

1. read the entire element from memory into a CPU register
2. modify that element
3. write it back to memory

If two bit domains share the same element, modifying that element in parallel
results in a race condition. The following snippet is an example:

```rust
# #[cfg(feature = "std")] {
use bitvec::*;
use std::thread;

static mut src: [u8; 1] = [0];
let bs: &mut BitSlice<BigEndian, u8> = (unsafe { &mut src as &mut [u8] }).into();
let (left, right) = bs.split_at_mut(4);
let l = thread::spawn(move || {
  left.set(1, true);
  println!("{}", left[1]);
});
let r = thread::spawn(move || {
  right.set(1, true);
  println!("{}", right[1]);
});
# }
```

Each thread is permitted to print `true` or `false`, depending on execution
order, because unsynchronized access writes to the entire byte, not just the
bit being manipulated by `set`.

> The Rust compiler (rightly) warns that use of a `static mut` item is a race
> condition waiting to happen. However, `thread::spawn` requires `'static`
> lifetimes, while other threading libraries do not. As there is no reason to
> pull in another crate just for scoped threads, the `unsafe` use of
> `static mut` remains as a demonstration.
>
> Note that there would be no race condition if the source array was two bytes,
> and each thread receieved one of those bytes.

This crate provides a trait, `Atomic`, which is implemented by the atomic types
in the core library corresponding to each storage element, and enforces the use
of synchronized read/modify/write sequences.
!*/

use crate::bits::BitPos;

use core::sync::atomic::{
	AtomicU8,
	AtomicU16,
	AtomicU32,
	Ordering,
};

#[cfg(target_pointer_width = "64")]
use core::sync::atomic::AtomicU64;

/** Atomic Element Access

This is not part of the public API; it is an implementation detail of `Bits`,
which is public API but is not publicly implementable.

This trait provides three methods, which the `Bits` trait uses to manipulate or
inspect storage items in a synchronized manner.

# Type Parameters

- `Fundamental`: This type is used to pass in to the trait what the underlying
  fundamental type is, so that `.get()` can return it directly, rather than as
  a set of trait bounds.

# Synchrony

All access uses [`Relaxed`] ordering.
**/
#[cfg_attr(not(feature = "std"), doc = "[`Relaxed`]: https://doc.rust-lang.org/core/sync/atomic/enum.Ordering.html#variant.Relaxed")]
#[cfg_attr(feature = "std", doc = "[`Relaxed`]: https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html#variant.Relaxed")]
pub trait Atomic<Fundamental: Sized>: Sized {
	/// Sets the bit at a position to `0`.
	///
	/// # Parameters
	///
	/// - `&self`: This is able to be immutable, rather than mutable, because
	///   the atomic type is a `Cell`-type wrapper.
	/// - `bit`: The position in the element to set low.
	fn clear(&self, bit: BitPos);

	/// Sets the bit at a position to `1`.
	///
	/// - `&self`
	/// - `bit`: The position in the element to set high.
	fn set(&self, bit: BitPos);

	/// Gets the element underneath the atomic access.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The fundamental type underneath the atomic type.
	fn get(&self) -> Fundamental;
}

impl Atomic<u8> for AtomicU8 {
	fn clear(&self, bit: BitPos) {
		self.fetch_and(!(1 << *bit), Ordering::Relaxed);
	}

	fn set(&self, bit: BitPos) {
		self.fetch_or(1 << *bit, Ordering::Relaxed);
	}

	fn get(&self) -> u8 {
		self.load(Ordering::Relaxed)
	}
}

impl Atomic<u16> for AtomicU16 {
	fn clear(&self, bit: BitPos) {
		self.fetch_and(!(1 << *bit), Ordering::Relaxed);
	}

	fn set(&self, bit: BitPos) {
		self.fetch_or(1 << *bit, Ordering::Relaxed);
	}

	fn get(&self) -> u16 {
		self.load(Ordering::Relaxed)
	}
}

impl Atomic<u32> for AtomicU32 {
	fn clear(&self, bit: BitPos) {
		self.fetch_and(!(1 << *bit), Ordering::Relaxed);
	}

	fn set(&self, bit: BitPos) {
		self.fetch_or(1 << *bit, Ordering::Relaxed);
	}

	fn get(&self) -> u32 {
		self.load(Ordering::Relaxed)
	}
}

#[cfg(target_pointer_width = "64")]
impl Atomic<u64> for AtomicU64 {
	fn clear(&self, bit: BitPos) {
		self.fetch_and(!(1 << *bit), Ordering::Relaxed);
	}

	fn set(&self, bit: BitPos) {
		self.fetch_or(1 << *bit, Ordering::Relaxed);
	}

	fn get(&self) -> u64 {
		self.load(Ordering::Relaxed)
	}
}
