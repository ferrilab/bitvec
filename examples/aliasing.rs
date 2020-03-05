/*! Memory region aliasing.

This test demonstrates how `bitvec` handles creation of slices that do not alias
individual *bits* in memory, but do alias the *elements* that contain those
bits. Because the hardware executing the `bitvec` instructions operates at the
element level, `bitvec` is forbidden from introducing conditions that cause
element-wide modifications to interfere with each other.

# How It Works

The `&mut BitSlice` reference is capable of analyzing its address value to
determine if it is possible for another reference handle to view the elements it
touches. It is undefined behavior to even *read* a memory element that is being
simultaneously written, *even if the bits subject to change will be erased*.

Fortunately, the Rust `&`/`&mut` reference exclusion rules already forbid the
possibility of a read reference viewing as unaliased the same element that a
write reference is modifying.

`BitSlice` only has a small number of methods that are capable of introducing an
alias, and they are all ultimately descended from `.split_at_mut()` and
`.split_at_mut_unchecked()`. Methods such as `.get_mut()` are *not* aliasing,
because Rust’s lifetime rules prevent the reference to the rest of the slice
from being used while the narrower reference handle is alive!

The methods that introduce parallel, disjoint, handles to memory that may alias
are all marked in the type system as producing handles to aliased memory. These
handles will either use atomic `lock` instructions to synchronize access across
threads, or use `Cell` access and remove their ability to cross thread
boundaries. Both mechanisms prevent race conditions from occurring.

# What This Test Does

This test demonstrates the effects in the type system of performing aliasing
work, and how users may remove the over-conservative alias taint on a slice. The
alias marker is added for *all* elements in a slice domain, after all, but only
the elements on the edges are actually aliased! This test demonstrates using
`.split_at_mut()` to taint slice handles, and `.bit_domain_mut()` to narrow the
taint to only the affected addresses.
!*/

#[cfg(feature = "std")]
extern crate bitvec;

#[cfg(feature = "std")]
use bitvec::{
	domain::Domain,
	prelude::*,
};

#[cfg(feature = "std")]
use std::{
	sync::atomic::AtomicU8,
	sync::atomic::Ordering,
	thread,
	time::Duration,
};

#[cfg(feature = "std")]
fn snooze() {
	thread::sleep(Duration::from_millis(10));
}

#[cfg(feature = "std")]
fn main() {
	let data = BitBox::from_bitslice([0u8; 5].bits::<Local>());
	let bits: &'static mut BitSlice<Local, u8> = BitBox::leak(data);

	//  This slice is all zeros.
	assert!(bits.not_any());

	//  `bits` is an unaliased slice, and is currently `Send`. Let’s make a
	//  thread manipulate it, and send it back.
	let handle = thread::spawn(move || {
		bits.set_all(true);
		bits
	});
	let bits: &'static mut BitSlice<Local, u8> = handle.join().unwrap();

	assert!(bits.all());

	//  Now, like the wise Solomon, we are going to cut this slice in half.
	let (left, right): (
		&'static mut BitSlice<Local, AtomicU8>,
		&'static mut BitSlice<Local, AtomicU8>,
	) = bits.split_at_mut(bits.len() / 2);

	/* If you look at the `.split_at_mut` docs, you’ll see that it returns a
	slice typed as `&mut BitSlice<O, T::Alias>`. If you follow that into the
	`BitStore` trait docs, you’ll see in the `u8` implementation that
	`type Alias = AtomicU8;`. If you see `type Alias = Cell<u8>;`, then this
	example won’t compile! Turn on `feature = "atomic"` in your build settings.

	`AtomicU8` is *still `Send`*, so we can still move these slices across
	threads!

	`&mut BitSlice` implements `Not`, and it does so by writing batched masks to
	the whole element. If we invert one side, then send them to threads and
	invert them both, we might hit a race condition in the middle!
	*/
	let left = !left;
	assert!(left.not_any());
	assert!(right.all());
	let (left, right) = (
		thread::spawn(move || {
			snooze();
			!left
		})
		.join()
		.unwrap(),
		thread::spawn(move || {
			snooze();
			!right
		})
		.join()
		.unwrap(),
	);

	//  Let’s check:
	assert!(left.all());
	assert!(right.not_any());

	/* The reason this worked is that these slices use `AtomicU8` for every
	mutation. But, `left` can only touch elements `[0 ..= 2]` and `right` can
	only touch elements `[2 ..= 4]`. They don’t *all* need atomic ops, only
	element `[2]`. How can we fix that? Introducing: `.bit_domain()` and
	`.bit_domain_mut()`. These methods are identical, except that `_mut` permits
	writing to the produced slices.
	*/
	let left = thread::spawn(move || {
		snooze();
		match left.bit_domain_mut() {
			BitDomainMut::Enclave { .. } => {
				unreachable!("I have selected the pattern that works")
			},
			BitDomainMut::Region { head, body, tail } => {
				//  Bind in reverse order, so that access to the contended
				//  element is likely simultaneous.
				let _back: &mut BitSlice<Local, AtomicU8> = !tail;
				let _middle: &mut BitSlice<Local, u8> = body;
				let _front: &mut BitSlice<Local, AtomicU8> = head;
			},
		}
		left
	})
	.join()
	.unwrap();
	let right = thread::spawn(move || {
		snooze();
		match right.bit_domain_mut() {
			BitDomainMut::Enclave { .. } => {
				unreachable!("I have selected the pattern that works")
			},
			BitDomainMut::Region { head, body, tail } => {
				let _front: &mut BitSlice<Local, AtomicU8> = !head;
				let _middle: &mut BitSlice<Local, u8> = body;
				let _back: &mut BitSlice<Local, AtomicU8> = tail;
			},
		}
		right
	})
	.join()
	.unwrap();

	/* Now let’s look at the memory elements, with `.domain()`.

	`.domain()` and `.domain_mut()` produce descriptions of the memory elements
	underneath the slice. They carry the same aliasing types, but because they
	refer to elements, rather than bits, they must also carry the start and stop
	counters. As with the bit domains, the `body` field is unaliased.

	The values from a slice domain let you work with the underlying memory
	directly, rather than still going through the `BitSlice` wrapper view.
	*/
	match left.domain() {
		Domain::Region {
			//  `head` is `None` when the slice fills its first element
			head: None,
			//  `body` is all the full elements
			body,
			//  `tail` refers to the partial element, and where the slice stops
			tail: Some((tail_atom, _tail_idx)),
		} if body == [!0u8; 2] => {
			assert_eq!(tail_atom.load(Ordering::Relaxed), 0b1111_0000u8)
		},
		_ => unreachable!("I have selected the pattern that works"),
	}
	match right.domain() {
		Domain::Region {
			//  `head` starts the slice, and refers to the partial element
			head: Some((_head_idx, head_atom)),
			body,
			//  `tail` is `None` when the slice fills its last element
			tail: None,
		} if body == [0u8; 2] => {
			assert_eq!(head_atom.load(Ordering::Relaxed), 0b1111_0000u8)
		},
		_ => unreachable!("I have selected the pattern that works"),
	}
}

#[cfg(not(feature = "std"))]
fn main() {
	//  This example requires the presence of a standard library.
}
