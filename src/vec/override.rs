/*! `BitVec` inherent functions that override `BitSlice` inherents.
!*/

use super::BitVec;

use crate::{
	cursor::Cursor,
	store::{
		BitStore,
		IntoBitIdx,
	},
};

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
	pub fn rotate_left(&mut self, shamt: usize) {
		use crate::bits::BitsMut;
		let len = self.len();
		let shamt = shamt % len;

		//  If the shift amount exceeds isz_max, shift twice.
		let isz_max = isize::max_value() as usize;
		if shamt > isz_max {
			self.rotate_left(isz_max);
			self.rotate_left(shamt - isz_max);
			return;
		}

		/* The algorithm has multiple stages. Since Rust does not have literate
		programming yet, so I will be using comments as needed to explain each
		stage.

		First, we compute how many live bits are in the front element and how
		many dead bits are in the back element of the memory store. Moving the
		front-element bits into the dead bits of the back element may allow the
		rotation to occur without any element moves.
		*/
		let head = self.pointer.head();
		let mut live_head = T::BITS - *head;
		let mut dead_tail = T::BITS - *self.pointer.tail();

		/* Small shift optimization: if the shift can be accomplished by just
		moving some bits from the front to the back, do that and exit.

		This branch enters only if the shift amount does not surpass both the
		dead bit count in the back and the live bit count in the front. The
		shift is allowed to completely empty the front element, which will incur
		a rotation of the underlying memory.
		*/
		if shamt <= dead_tail as usize && shamt <= live_head as usize {
			for _ in 1 ..= shamt as u8 {
				bit_shunt(self, len, &mut live_head, &mut dead_tail);
			}
			//  If the head element has been completely drained, then it needs
			//  to be rotated to the back.
			if live_head == 0 || *self.pointer.head() == 0 {
				self.as_mut_slice().rotate_left(1);
			}
			return;
		}

		/* Large shift behavior: compute how many live bits are in the front
		element (`T::BITS - *self.pointer.head()`), then try to move bits from
		the front element to the back element. As above, this moves the head
		cursor without changing the length.

		The head and tail counters computed are our bounds checks; it is safe to
		use unchecked access to get [0], set [len], and increment the head until
		one of the counters runs out.
		*/
		while live_head > 0 && dead_tail > 0 {
			bit_shunt(self, len, &mut live_head, &mut dead_tail);
		}

		/* At this point, the front element of the memory store now has any
		original dead bits at the front, plus any newly vacated bits from the
		shunt performed above. The remaining live bits up until `head + shamt`
		must be rotated to the back of the bit-slice, but before that can
		happen, they must be shifted to the front of the memory span. This will
		move the dead bits from being at the front of the span to being between
		the to-be-rotated bits and the incoming new head bit.

		Compute the number of dead bits in the front of the front element,
		then create a bit slice from the front of the front element (*not* from
		where `self` currently thinks its head is) to the original head plus the
		shift amount, and shift that whole slice down by the number of dead
		front bits.
		*/
		let dead_head = T::BITS - live_head;
		let last_head = *head as usize + shamt;
		self.as_mut_slice()
			.bits_mut::<C>()[.. last_head] <<= dead_head;

		/* Now, we must break the shift distance into an element count and a new
		head index.

		The front elements get rotated to the back, using the standard slice
		rotate function, and the vector head cursor is set to the `last_head`
		modulus the element width, and rotation is complete.
		*/
		self.as_mut_slice().rotate_left(last_head >> T::BITS);
		unsafe { self.pointer.set_head((last_head as u8 & T::MASK).idx()); }

		/// Moves the front bit to the back, and slides the slice one to the
		/// right.
		///
		/// # Parameters
		///
		/// - `this`: Reference to the `BitVec` undergoing rotation. This does
		///   need to be a `&mut BitVec` reference, because the vector’s pointer
		///   member is modified by the function, as well as the referent
		///   slice’s contents.
		/// - `len`: The precomputed length of the referent `BitSlice`.
		/// - `live_head`: Write reference to a loop control counter.
		/// - `dead_tail`: Write reference to a loop control counter.
		fn bit_shunt<C, T>(
			this: &mut BitVec<C, T>,
			len: usize,
			live_head: &mut u8,
			dead_tail: &mut u8,
		)
		where C: Cursor, T: BitStore {
			//  This function does not need to care about wrap; the calling
			//  loops manage that.
			let (new_head, _) = this.pointer.head().incr();
			//  Move the front bit to the back, and slide the span one to the
			//  right.
			unsafe {
				let bit = this.get_unchecked(0);
				this.set_unchecked(len, bit);
				this.pointer.set_head(new_head);
			}
			//  Decrement the control counters.
			*live_head -= 1;
			*dead_tail -= 1;
		}
	}
}
