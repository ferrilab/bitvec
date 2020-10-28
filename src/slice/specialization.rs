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

/** Order-specialized function implementations.

These functions use [`BitField`] to provide batched load/store behavior.
Where loads or stores cross a `T` element boundary, they use the `_le`
behavior to ensure that bits stay in the correct order relative to each
other, even as they may change position within an element.

[`BitField`]: crate::field::BitField
**/
impl<T> BitSlice<Lsb0, T>
where T: BitStore
{
	/// Accelerates copies between disjoint slices with batch loads.
	pub(crate) fn sp_copy_from_bitslice(&mut self, src: &Self) {
		assert_eq!(
			self.len(),
			src.len(),
			"Copying between slices requires equal lengths"
		);

		let chunk_size = <usize as BitMemory>::BITS as usize;
		for (to, from) in self
			.chunks_mut(chunk_size)
			.remove_alias()
			.zip(src.chunks(chunk_size))
		{
			to.store_le::<usize>(from.load_le::<usize>())
		}
	}

	/// Accelerates possibly-overlapping copies within a single slice with batch
	/// loads.
	pub(crate) unsafe fn sp_copy_within_unchecked<R>(
		&mut self,
		src: R,
		dest: usize,
	) where
		R: RangeBounds<usize>,
	{
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
			for (src, dst) in (&*from)
				.alias()
				.rchunks(chunk_size)
				.zip((&mut *to).rchunks_mut(chunk_size))
			{
				dst.store_le::<usize>(src.load_le::<usize>());
			}
		}
		else {
			for (src, dst) in (&*from)
				.alias()
				.chunks(chunk_size)
				.zip((&mut *to).chunks_mut(chunk_size))
			{
				dst.store_le::<usize>(src.load_le::<usize>());
			}
		}
	}

	/// Accelerates equality checking with batch loads.
	pub(crate) fn sp_eq(&self, other: &Self) -> bool {
		if self.len() != other.len() {
			return false;
		}
		let chunk_size = <usize as BitMemory>::BITS as usize;
		self.chunks(chunk_size)
			.zip(other.chunks(chunk_size))
			.all(|(a, b)| a.load_le::<usize>() == b.load_le::<usize>())
	}
}

/** Order-specialized function implementations.

These functions use [`BitField`] to provide batched load/store behavior.
Where loads or stores cross a `T` element boundary, they use the `_be`
behavior to ensure that bits stay in the correct order relative to each
other, even as they may change position within an element.

[`BitField`]: crate::field::BitField
**/
impl<T> BitSlice<Msb0, T>
where T: BitStore
{
	/// Accelerates copies between disjoint slices with batch loads.
	pub(crate) fn sp_copy_from_bitslice(&mut self, src: &Self) {
		assert_eq!(
			self.len(),
			src.len(),
			"Copying between slices requires equal lengths"
		);

		let chunk_size = <usize as BitMemory>::BITS as usize;
		for (to, from) in self
			.chunks_mut(chunk_size)
			.remove_alias()
			.zip(src.chunks(chunk_size))
		{
			to.store_be::<usize>(from.load_be::<usize>())
		}
	}

	/// Accelerates possibly-overlapping copies within a single slice with batch
	/// loads.
	pub(crate) unsafe fn sp_copy_within_unchecked<R>(
		&mut self,
		src: R,
		dest: usize,
	) where
		R: RangeBounds<usize>,
	{
		let source = dvl::normalize_range(src, self.len());
		let rev = source.contains(&dest);
		let dest = dest .. dest + source.len();

		let from: *const Self = self.get_unchecked(source) as *const _;
		let to: *mut Self = self.get_unchecked_mut(dest) as *mut _;
		let chunk_size = <usize as BitMemory>::BITS as usize;
		if rev {
			for (src, dst) in (&*from)
				.alias()
				.rchunks(chunk_size)
				.zip((&mut *to).rchunks_mut(chunk_size))
			{
				dst.store_be::<usize>(src.load_be::<usize>());
			}
		}
		else {
			for (src, dst) in (&*from)
				.alias()
				.chunks(chunk_size)
				.zip((&mut *to).chunks_mut(chunk_size))
			{
				dst.store_be::<usize>(src.load_be::<usize>());
			}
		}
	}

	/// Accelerates equality checking with batch loads.
	pub(crate) fn sp_eq(&self, other: &Self) -> bool {
		if self.len() != other.len() {
			return false;
		}
		let chunk_size = <usize as BitMemory>::BITS as usize;
		self.chunks(chunk_size)
			.zip(other.chunks(chunk_size))
			.all(|(a, b)| a.load_be::<usize>() == b.load_be::<usize>())
	}
}
