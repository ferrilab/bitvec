/*! Specialization overrides.

This module contains override functions used when generic bit-by-bit iteration
can be accelerated for specific type parameters.

Call sites that wish to take advantage of specialization methods must first
inspect their type arguments to determine if specialization is even possible,
and transmute generic slices into slices with concrete type arguments applied.
!*/

use crate::{
	field::BitField,
	mem::BitMemory,
	order::{
		Lsb0,
		Msb0,
	},
	slice::BitSlice,
	store::BitStore,
};

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
	/// Specialized bit mover.
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
