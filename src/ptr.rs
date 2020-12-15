/*! Bit-region pointer encoding.

This module defines the in-memory representations of various pointers to bits.
These include single-bit pointers, and pairs of them, which cannot be encoded
into a raw Rust pointer, and span descriptors, which can be encoded into a raw
Rust slice pointer and retyped as [`*BitSlice`].

This module makes the type symbols available to the public API, but they are all
opaque types and their values **cannot** be modified by user code. The encoding
system used to pack span descriptors into slice-pointer types is not public API,
and is not available for general inspection or modification.

[`*BitSlice`]: crate::slice::BitSlice
!*/

use crate::{
	mutability::{
		Const,
		Mut,
	},
	order::BitOrder,
	store::BitStore,
};

use core::any::TypeId;

mod address;
mod proxy;
mod range;
mod single;
mod span;

pub use self::{
	address::{
		Address,
		AddressError,
	},
	proxy::BitMut,
	range::BitPtrRange,
	single::BitPtr,
};

pub(crate) use self::span::{
	BitSpan,
	BitSpanError,
};

/** Copies `count` bits from `src` to `dst`. The source and destination may
overlap.

If the source and destination will *never* overlap, [`copy_nonoverlapping`] can
be used instead.

# Additional Constraints

`bitvec` considers it Undefined Behavior for two descriptors to overlap in
memory if their `BitOrder` parameters differ.

```rust
use bitvec::prelude::*;

let mut x = 0u8;
let lsb0: BitPtr<_, Lsb0, _> = (&mut x).into();
let msb0: BitPtr<_, Msb0, _> = (&x).into();

unsafe {
  //  Defined: the regions do not select the same bits
  bitvec::ptr::copy(msb0, lsb0, 4);

  //  Undefined: the regions overlap in bits
  // bitvec::ptr::copy(msb0, lsb0, 5);
}
```

`bitvec` assumes that if `O1` and `O2` differ, then the regions will never
overlap in actual bits, and copies naïvely. If `O1` and `O2` are the same type,
then this performs overlap analysis to determine the copy direction.

If `T1` and `T2` have different memory types, then the behavior will follow the
tables of order/store traversal shown in the manual. Overlapping bytes in this
condition will likely clobber, and the function will make no attempt to preserve
them for correct copying.

Do not use this function on overlapping memory regions unless the source and
destination pointers have the same type parameters.

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
[`copy_nonoverlapping`]: crate::ptr::copy_nonoverlapping
**/
pub unsafe fn copy<O1, O2, T1, T2>(
	src: BitPtr<Const, O1, T1>,
	dst: BitPtr<Mut, O2, T2>,
	count: usize,
) where
	O1: BitOrder,
	O2: BitOrder,
	T1: BitStore,
	T2: BitStore,
{
	if TypeId::of::<O1>() == TypeId::of::<O2>() {
		let (addr, head) = dst.raw_parts();
		let dst = BitPtr::<Mut, O1, T2>::new_unchecked(addr, head);

		let src_pair = src.range(count);
		let dst_pair = dst.range(count);

		if src_pair.contains(&dst) {
			for (src, dst) in src_pair.zip(dst_pair).rev() {
				write(dst, read(src));
			}
		}
		else {
			for (src, dst) in src_pair.zip(dst_pair) {
				write(dst, read(src));
			}
		}
	}
	//  Pointers with different orderings **cannot** overlap. Such an overlap is
	//  a fault in the caller, and `bitvec` undefines this behavior.
	else {
		for (src, dst) in src.range(count).zip(dst.range(count)) {
			write(dst, read(src));
		}
	}
}

/** Reads one bit from a memory location.

# Original

[`ptr::read`](core::ptr::read)

# API Differences

This must load the entire memory element from `*src`, then discard all bits but
the referent.

# Safety

Behavior is undefined if any of the following conditions are violated:

- `src` must be [valid] for reads.
- `src` must be a validly constructed pointer.
- `src` must point to a properly initialized value of type `T`.

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let x = 128u8;
let x_ptr: BitPtr<_, Msb0, _> = (&x).into();
assert!(
  unsafe { bitvec::ptr::read(x_ptr) }
);
```

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
**/
pub unsafe fn read<O, T>(src: BitPtr<Const, O, T>) -> bool
where
	O: BitOrder,
	T: BitStore,
{
	src.read()
}

/** Overwrites a memory location with the given bit.

# Original

[`ptr::write`](core::ptr::write)

# API Differences

The referent memory location must be read, modified in a register, then written
back.

# Safety

Behavior is undefined if any of the following conditions are violated:

- `dst` must be [valid] for writes.
- `dst` must be a validly constructed pointer.

# Examples

Basic usage:

```rust
use bitvec::prelude::*;

let mut x = 0u8;
let x_ptr: BitPtr<_, Lsb0, _> = (&mut x).into();
unsafe { bitvec::ptr::write(x_ptr, true); }
assert_eq!(x, 1);
```

[valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
**/
pub unsafe fn write<O, T>(dst: BitPtr<Mut, O, T>, src: bool)
where
	O: BitOrder,
	T: BitStore,
{
	dst.write(src);
}
