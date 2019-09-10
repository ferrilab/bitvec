/*! `BitVec` inherent functions that override `BitSlice` inherents.
!*/

use super::BitVec;

use crate::{
	bits::Bits,
	cursor::Cursor,
	store::{
		BitStore,
	},
};

use core::ptr;

impl<C, T> BitVec<C, T>
where C: Cursor, T: BitStore {
	/// Accesses the underlying store as elements.
	///
	/// Unlike the `BitSlice` implementation, this does produce the tail element
	/// even if it is partial. `BitVec` unconditionally owns its memory, so
	/// there can never be an aliasing condition.
	///
	/// Since the elements are all guaranteed to be fully initialized, this does
	/// not produce any views to uninitialized memory.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// A slice over the raw elements underlying the vector.
	pub fn as_slice(&self) -> &[T] {
		self.pointer.as_slice()
	}

	/// Accesses the underlying store as elements.
	///
	/// Unlike the `BitSlice` implementation, this does produce the tail element
	/// even if it is partial. `BitVec` unconditionally owns its memory, so
	/// there can never be an aliasing condition. Any operation which would
	/// cause a `BitSlice` alias would require the code to have borrowed the
	/// `BitVec`, forbidding access to this method.
	///
	/// Since the elements are all guaranteed to be fully initialized, this does
	/// not produce any views to uninitialized memory.
	///
	/// # Parameters
	///
	/// - `&mut self`
	///
	/// # Returns
	///
	/// A mutable slice over the raw elements underlying the vector.
	pub fn as_mut_slice(&mut self) -> &mut [T] {
		self.pointer.as_mut_slice()
	}

	/// Rotates the contents of the vector left, in-place.
	///
	/// This method is re-written on `BitVec` rather than delegating to the
	/// `BitSlice` implementation because `BitVec`’s guarantee of un-aliased raw
	/// memory allows it to perform more aggressive optimizations that
	/// contaminate adjacent dead memory. `BitSlice` cannot perform those
	/// actions, as its adjacent dead memory is likely observed by other slices.
	///
	/// # Parameters
	///
	/// - `&mut self`: An exclusive lock on the vector undergoing rotation. This
	///   method strictly requires that no external observation of the buffer or
	///   handle can occur for the duration of the call.
	/// - `by`: The rotation distance. This argument is modulated by
	///   `self.len()`, and then `self` is split in two at `by` and the two
	///   segments switch places.
	///
	/// # Behavior
	///
	/// This function has multiple possible execution paths. It attempts to take
	/// the fastest possible path without allocating, but a vector that is full
	/// nearly to capacity has much less room to rotate, and will require more
	/// iterations of partial work to complete.
	///
	/// This function works best when `self.capacity() - self.len()` is at least
	/// the rotation distance.
	pub fn rotate_left(&mut self, by: usize) {
		let len = self.len();
		let by = by % len;

		//  Exit immediately for noöp rotations.
		if by == 0 {
			return;
		}

		//  If the rotation distance exceeds `isize::max_value()`, shift twice.
		let isz_max = isize::max_value() as usize;
		if by > isz_max {
			self.rotate_left(isz_max);
			self.rotate_left(by - isz_max);
			return;
		}

		//  Compute the size of the empty region in the buffer after the live
		//  span ends.
		let orig_head = self.pointer.head();
		let dead_tail = self.capacity() - (*orig_head as usize + len);

		//  Enter this branch if the rotation can be performed solely by
		//  sliding into the excess allocation, then shifting back down.
		if by <= dead_tail {
			let base_ptr = self.pointer.pointer();
			//  Repeatedly throw the front bit to the back of the span, then
			//  slide the span one bit to the right, until rotation is complete.
			for _ in 0 .. by {
				unsafe {
					self.copy(0, len);
					self.pointer.slide(1);
				}
			}

			//  Once the above loop terminates, the live span has climbed `by`
			//  bits higher in the allocation buffer. It must be moved back down
			//  to the buffer origin.
			let span = self.pointer;
			let span_ptr = span.pointer();
			if base_ptr.u() < span_ptr.u() {
				unsafe {
					ptr::copy(span_ptr.r(), base_ptr.w(), span.elements());
					self.pointer.set_pointer(base_ptr);
				}
			}
			return;
		}

		//  Ensure that the live span is aligned at the bottom edge.
		self.force_align();
		let bits = T::BITS as usize;

		/* This loop specializes `[T]::rotate_left` by pulling the front
		element out onto the stack, moving the live span down an element,
		and then re-inserting the stack element to the back of the slice,
		regardless of whether the tail is aligned to an element boundary.

		This loop proceeds an element at a time; it is possible to add
		faster-galloping branches that move two, four, eight elements and
		progressively slow down as the rotation approaches completion, but
		this heuristic does not seem useful at time of writing.
		*/
		let mut by = by;
		while by > bits {
			let tmp = self.as_slice()[0];
			//  `[T]` does not expose a shunt operator other than rotation, but
			//  the extra writeback is not too costly.
			self.as_mut_slice().rotate_left(1);
			//  Write the stack temporary into the back of the slice
			for (b, i) in tmp.bits::<C>().iter().zip(len - bits ..) {
				unsafe { self.set_unchecked(i, b); }
			}
			by -= bits;
		}

		/* If the rotation amount is a partial element, then we need to copy the
		first `by` bits out of the span and onto the stack, then move the entire
		span downwards by `by`, then re-insert the copied bits into the back of
		the span. This will complete the rotation.
		*/
		let tmp = self.as_bits()[.. by].as_native::<T>();
		//  BitSlice <<= has overhead that we know we can skip and just
		//  use the core shunting loop.
		for (to, from) in (by .. len).enumerate() {
			unsafe { self.copy(from, to); }
		}
		let mid = len - by;
		for (b, i) in tmp.bits::<C>().iter().take(by).zip(mid ..) {
			unsafe { self.set_unchecked(i, b); }
		}
	}

	/// Rotates the contents of the vector right, in-place.
	///
	/// This method is provided as a `BitVec` inherent for the same reason as
	/// `rotate_left`.
	///
	/// # Parameters
	///
	/// - `&mut self`: An exclusive lock on the vector undergoing rotation.
	/// - `by`: The rotation distance. This argument is modulated by
	///   `self.len()`, and then `self` is split in two at `len - by` and the
	///   two segments switch places.
	///
	/// # Behavior
	///
	/// This function has multiple possible execution paths. It attempts to take
	/// the fastest possible path without allocating, but a vector that is near
	/// capacity has much less room to rotate, and will require more iterations
	/// of partial work to complete.
	///
	/// Right rotation will always require more effort than left rotation when
	/// the fastest path is not available. Prefer `rotate_left` where possible.
	pub fn rotate_right(&mut self, by: usize) {
		let len = self.len();
		let by = by % len;

		if by == 0 {
			return;
		}

		let isz_max = isize::max_value() as usize;
		if by > isz_max {
			self.rotate_right(isz_max);
			self.rotate_right(by - isz_max);
			return;
		}

		let orig_head = self.pointer.head();
		let dead_head = *orig_head as usize;

		//  If the rotation can be performed solely by moving the back bits into
		//  dead space in the front of the vector, do that and exit.
		if by <= dead_head {
			for _ in 0 .. by {
				unsafe {
					self.pointer.slide(-1);
					self.copy(len, 0);
				}
			}
			return;
		}

		let base_ptr = self.pointer.pointer();

		let capacity = self.capacity();
		let dead_bits = capacity - len;
		let dead_tail = dead_bits - dead_head;

		//  Otherwise, move the live span to be at the back edge of the
		//  allocation,
		if dead_tail > 0 {
			unsafe {
				self.pointer.set_len(capacity - dead_head);
				*self.as_bits_mut() >>= dead_tail;
				self.pointer.set_len(len);
				self.pointer.slide(dead_tail as isize);
			}
		}

		//  Then successively remove elements from the back, rotate the whole
		//  span, then re-insert the removed element at the front.
		let bits = T::BITS as usize;
		let mut by = by;
		while by > bits {
			let tmp = *self.as_slice().last().unwrap();
			self.as_mut_slice().rotate_right(1);
			for (i, b) in tmp.bits::<C>().iter().enumerate() {
				unsafe { self.set_unchecked(i, b); }
			}
			by -= bits;
		}

		//  Now that less than an element remains to be rotated, do the same
		//  work as above, but for a smaller piece and shunt distance.

		let mid = len - by;
		let tmp = self.as_bits()[mid ..].as_native::<T>();
		//  Move data from `0 .. len - by` to `by .. len`, right to left
		for (from, to) in (by .. len).enumerate().rev() {
			unsafe { self.copy(from, to); }
		}
		//  Move data from the tmp register into the front of the slice, from
		//  left to right.
		for (i, b) in tmp.bits::<C>().iter().take(by).enumerate() {
			unsafe { self.set_unchecked(i, b); }
		}

		//  The live span was moved to the back edge of the allocation; it needs
		//  to be moved back down to the front edge.

		let span = self.pointer;
		let span_ptr = span.pointer();
		if base_ptr.u() != span_ptr.u() {
			unsafe {
				ptr::copy(span_ptr.r(), base_ptr.w(), span.elements());
				self.pointer.set_pointer(base_ptr);
			}
		}
	}
}
