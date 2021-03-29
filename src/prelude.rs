/*! [`bitvec`] symbol export.

This module collects the general public API into a single spot for inclusion, as
`use bitvec::prelude::*;`, without polluting the root namespace of the crate.

[`bitvec`]: crate
!*/

pub use crate::{
	array::BitArray,
	bitarr,
	bits,
	field::BitField as _,
	order::{
		BitOrder,
		LocalBits,
		Lsb0,
		Msb0,
	},
	ptr::{
		BitPtr,
		BitPtrRange,
		BitRef,
	},
	slice::BitSlice,
	store::BitStore,
	view::BitView as _,
	BitArr,
};
#[cfg(feature = "alloc")]
pub use crate::{
	bitbox,
	bitvec,
	boxed::BitBox,
	vec::BitVec,
};
