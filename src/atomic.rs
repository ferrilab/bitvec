/*! Atomic element access

This module enables the `BitStore` trait to access its storage elements as
atomic variants, in order to ensure parallel consistency.

This is necessary because while individual bit domains are forbidden from
parallel overlap by the Rust type system, CPUs do not have bit-level granularity
(that is the whole *raison d’être* of this crate), and so adjacent bit domains
that use the same storage element may encounter race conditions.

The sequence of operations needed to modify a single bit is:

1. read the entire element from memory into a CPU register
2. modify that element
3. write it back to memory

If two bit domains share the same element, modifying that element in parallel
results in a race condition. The following snippet is an example:

```rust
# #[cfg(feature = "std")] {
use bitvec::prelude::*;
use std::thread;

static mut SRC: [u8; 1] = [0];
let bs = unsafe { SRC.as_mut_bitslice::<BigEndian>() };
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
> pull in another crate just for scoped threads in an example, the `unsafe` use
> of `static mut` remains as a demonstration.
>
> Note that there would be no race condition if the source array was two bytes,
> and each thread receieved one of those bytes.

This module provides a trait, `Atomic`, which is implemented on the atomic types
in the core library corresponding to each storage element, and enforces the use
of synchronized read/modify/write sequences. The module is feature-gated so that
it may be removed on systems which lack either atomic instructions or the
concurrency mechanisms needed to induce a race condition.
!*/

#![cfg(feature = "atomic")]

use crate::store::{
	BitPos,
	BitStore,
};

use core::sync::atomic::{
	AtomicU8,
	AtomicU16,
	AtomicU32,
	Ordering,
};

#[cfg(target_pointer_width = "64")]
use core::sync::atomic::AtomicU64;

/** Atomic element access

This is not part of the public API; it is an implementation detail of
[`BitStore`], which is public API but is not publicly implementable.

This trait provides four methods, which the `BitStore` trait uses to manipulate
or inspect storage items in a synchronized manner.

# Synchrony

All access uses [`Relaxed`] ordering.

[`BitStore`]: ../store/trait.BitStore.html
**/
#[cfg_attr(not(feature = "std"), doc = "[`Relaxed`]: https://doc.rust-lang.org/stable/core/sync/atomic/enum.Ordering.html#variant.Relaxed")]
#[cfg_attr(feature = "std", doc = "[`Relaxed`]: https://doc.rust-lang.org/stable/std/sync/atomic/enum.Ordering.html#variant.Relaxed")]
pub trait Atomic: Sized {
	/// Defines the underlying fundamental type that this trait is wrapping.
	type Fundamental: BitStore;

	/// Sets the bit at some position to `0`.
	///
	/// # Parameters
	///
	/// - `&self`: This is able to be immutable, rather than mutable, because
	///   the atomic type is a `Cell`-type wrapper.
	/// - `bit`: The position in the element to set low.
	fn clear(&self, bit: BitPos<Self::Fundamental>);

	/// Sets the bit at some position to `1`.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `bit`: The position in the element to set high.
	fn set(&self, bit: BitPos<Self::Fundamental>);

	/// Inverts the bit at some position.
	///
	/// # Parameters
	///
	/// - `&self`
	/// - `bit`: The position in the element to invert.
	fn invert(&self, bit: BitPos<Self::Fundamental>);

	/// Gets the element underneath the atomic access.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// The fundamental type underneath the atomic type.
	fn get(&self) -> Self::Fundamental;
}

impl Atomic for AtomicU8 {
	type Fundamental = u8;

	#[inline(always)]
	fn clear(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_and(!<u8 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn set(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_or(<u8 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_xor(<u8 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn get(&self) -> u8 {
		self.load(Ordering::Relaxed)
	}
}

impl Atomic for AtomicU16 {
	type Fundamental = u16;

	#[inline(always)]
	fn clear(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_and(!<u16 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn set(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_or(<u16 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_xor(<u16 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn get(&self) -> u16 {
		self.load(Ordering::Relaxed)
	}
}

impl Atomic for AtomicU32 {
	type Fundamental = u32;

	#[inline(always)]
	fn clear(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_and(!<u32 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn set(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_or(<u32 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_xor(<u32 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn get(&self) -> u32 {
		self.load(Ordering::Relaxed)
	}
}

#[cfg(target_pointer_width = "64")]
impl Atomic for AtomicU64 {
	type Fundamental = u64;

	#[inline(always)]
	fn clear(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_and(!<u64 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn set(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_or(<u64 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn invert(&self, bit: BitPos<Self::Fundamental>) {
		self.fetch_xor(<u64 as BitStore>::mask_at(bit), Ordering::Relaxed);
	}

	#[inline(always)]
	fn get(&self) -> u64 {
		self.load(Ordering::Relaxed)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use core::sync::atomic::{
		AtomicU8,
		AtomicU16,
		AtomicU32,
	};

	#[cfg(target_pointer_width = "64")]
	use core::sync::atomic::AtomicU64;

	#[test]
	fn atomic_u8() {
		let atom = AtomicU8::new(0);

		Atomic::set(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 1);

		Atomic::clear(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 0);

		Atomic::invert(&atom, BitPos::new(1));
		assert_eq!(Atomic::get(&atom), 2);
	}

	#[test]
	fn atomic_u16() {
		let atom = AtomicU16::new(0);

		Atomic::set(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 1);

		Atomic::clear(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 0);

		Atomic::invert(&atom, BitPos::new(1));
		assert_eq!(Atomic::get(&atom), 2);
	}

	#[test]
	fn atomic_u32() {
		let atom = AtomicU32::new(0);

		Atomic::set(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 1);

		Atomic::clear(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 0);

		Atomic::invert(&atom, BitPos::new(1));
		assert_eq!(Atomic::get(&atom), 2);
	}

	#[cfg(target_pointer_width = "64")]
	#[test]
	fn atomic_u64() {
		let atom = AtomicU64::new(0);

		Atomic::set(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 1);

		Atomic::clear(&atom, BitPos::new(0));
		assert_eq!(Atomic::get(&atom), 0);

		Atomic::invert(&atom, BitPos::new(1));
		assert_eq!(Atomic::get(&atom), 2);
	}
}
