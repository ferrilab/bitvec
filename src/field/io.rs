/*! I/O trait implementations.

The standard library defines byte-based I/O protocols that form the basis of
exchanging memory buffers with I/O controllers. As `BitSlice` is designed to be
used with I/O buffers, it makes sense for it to implement these protocols.

This module is a subset of the `field` module because it relies on the
`BitField` trait’s ability to map `BitSlice` to a value-storage region. The I/O
protocols `Read` and `Write` are strictly byte-based, and cannot be altered to
be bit-based. As such, they are only implemented on types with a `BitField`
implementation.

Calling `BitField` methods in a loop imposes a non-trivial, and irremovable,
per-loop overhead cost. Use of `bitvec` data structures directly, rather than
their underlying buffers, will have a performance penalty.
!*/

#![cfg(feature = "std")]

use crate::{
	field::BitField,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
	vec::BitVec,
};

use core::mem;

use std::io::{
	self,
	Read,
	Write,
};

/** Mirrors the implementation on `[u8]` (found [here]).

The implementation loads bytes out of the `&BitSlice` reference until exhaustion
of either the source `BitSlice` or destination `[u8]`. When `.read()` returns,
`self` will have been updated to no longer include the leading segment copied
out as bytes of `buf`.

[here]: https://doc.rust-lang.org/std/primitive.slice.html#impl-Read
**/
impl<'a, O, T> Read for &'a BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
	Self: BitField,
{
	#[inline]
	fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
		let mut idx = 0;
		for (byte, slot) in self.chunks_exact(8).zip(buf.iter_mut()) {
			*slot = byte.load();
			idx += 1;
		}
		*self = unsafe { self.get_unchecked(idx * 8 ..) };
		Ok(idx)
	}
}

/** Mirrors the implementation on `[u8]` (found [here]).

The implementation copies bytes into the `&mut BitSlice` reference until
exhaustion of either the source `[u8]` or destination `BitSlice`. When
`.write()` returns, `self` will have been updated to no longer include the
leading segment containing bytes copied in from `buf`.

[here]: https://doc.rust-lang.org/std/primitive.slice.html#impl-Write
**/
impl<'a, O, T> Write for &'a mut BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T::Alias>: BitField,
{
	#[inline]
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let mut idx = 0;
		for (slot, byte) in self.chunks_exact_mut(8).zip(buf.iter().copied()) {
			slot.store(byte);
			idx += 1;
		}
		*self = unsafe { mem::take(self).get_unchecked_mut(idx * 8 ..) };
		Ok(idx)
	}

	#[inline(always)]
	fn flush(&mut self) -> io::Result<()> {
		Ok(())
	}
}

/** Mirrors the implementation on `Vec<u8>` (found [here]).

The implementation copies bytes from `buf` into the tail end of `self`. The
performance characteristics of this operation are dependent on the type
parameters of the `BitVec`, and the position of its tail.

[here]: https://doc.rust-lang.org/std/vec/struct.Vec.html#impl-Write
**/
impl<O, T> Write for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore,
	BitSlice<O, T::Alias>: BitField,
{
	#[inline]
	fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
		let len = self.len();
		self.resize(len + buf.len() * 8, false);
		unsafe { self.get_unchecked_mut(len ..) }.write(buf)
	}

	#[inline(always)]
	fn flush(&mut self) -> io::Result<()> {
		Ok(())
	}
}
