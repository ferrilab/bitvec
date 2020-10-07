/*! Specialization overrides.

This module contains override functions used when generic bit-by-bit iteration
can be accelerated for specific type parameters.

Call sites that wish to take advantage of specialization methods must first
inspect their type arguments to determine if specialization is even possible,
and transmute generic slices into slices with concrete type arguments applied.
!*/

use crate::{
	devel as dvl,
	field::BitField,
	mem::BitMemory,
	order::{
		Lsb0,
		Msb0,
	},
	slice::BitSlice,
	store::BitStore,
};

use core::ops::RangeBounds;

macro_rules! specialize {
	($( $func:item )*) => {
		impl<T> BitSlice<Lsb0, T> where T: BitStore {
			$( #[inline] $func )*
		}

		impl<T> BitSlice<Msb0, T> where T: BitStore {
			$( #[inline] $func )*
		}
	};
}

specialize! {
	/// Specialized bit mover. This moves bits between two separate slices, and
	/// does not need to be aware of region overlap.
	pub(crate) fn sp_copy_from_bitslice(&mut self, src: &Self) {
		assert_eq!(
			self.len(),
			src.len(),
			"Copying between slices requires equal lengths"
		);

		let chunk_size = <usize as BitMemory>::BITS as usize;
		for (to, from) in self
			.chunks_mut(chunk_size)
			.map(|c| unsafe { BitSlice::<_, T>::unalias_mut(c) })
			.zip(src.chunks(chunk_size))
		{
			to.store::<usize>(from.load::<usize>())
		}
	}

	/// Specialized *internal* bit mover. This moves bits within a single slice,
	/// and must be aware of region overlap.
	pub(crate) unsafe fn sp_copy_within_unchecked<R>(
		&mut self,
		src: R,
		dest: usize,
	)
	where R:RangeBounds<usize> {
		let source = dvl::normalize_range(src, self.len());
		let rev = source.contains(&dest);
		let dest = dest .. dest + source.len();

		/* The `&mut self` receiver ensures that this method has an exclusive
		access to the bits of its region prior to entry. In order to satisfy
		element-based aliasing rules, the correct but pessimal behavior is to
		mark the entirety of the source and destination subregions *may*
		overlap, either in the actual bits they affect **or** merely in the
		elements that contain them. As this is an `_unchecked` method, it is
		preferable to unconditionally taint the regions rather than compute
		whether the taint is necessary. For performance, the fact that this
		method has exclusive access to its bits (and will be already-tainted if
		external aliases exist) should suffice to ensure that issuing lock
		instructions will not in fact result in bus delays while the processor
		clears the bus.

		The actual alias tainting can be deferred to the loop header, since
		construction of aliased *pointers* is fine, and the reference tainting
		precludes the simultaneous liveness of untainted im/mut references.
		*/
		let from: *const Self = self.get_unchecked(source) as *const _;
		//  This can stay unaliased for now, because `.{,r}chunks_mut()` taints.
		let to: *mut Self = self.get_unchecked_mut(dest) as *mut _;
		let chunk_size = <usize as BitMemory>::BITS as usize;
		if rev {
			for (src, dst) in (&*from).alias()
				.rchunks(chunk_size)
				.zip((&mut *to).rchunks_mut(chunk_size))
			{
				dst.store::<usize>(src.load::<usize>());
			}
		}
		else {
			for (src, dst) in (&*from).alias()
				.chunks(chunk_size)
				.zip((&mut *to).chunks_mut(chunk_size))
			{
				dst.store::<usize>(src.load::<usize>());
			}
		}
	}

	/// Specialized equality checker.
	pub(crate) fn sp_eq(&self, other: &Self) -> bool {
		if self.len() != other.len() {
			return false;
		}

		let chunk_size = <usize as BitMemory>::BITS as usize;
		self.chunks(chunk_size)
			.zip(other.chunks(chunk_size))
			.all(|(a, b)| a.load::<usize>() == b.load::<usize>())
	}
}
