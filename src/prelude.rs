/*! `bitvec` Prelude

This collects the general public API into a single spot for inclusion, as
`use bitvec::prelude::*;`, without polluting the root namespace of the crate.
!*/

pub use crate::{
	bits::Bits,
	cursor::{
		Cursor,
		BigEndian,
		LittleEndian,
	},
	slice::BitSlice,
};

#[cfg(any(feature = "alloc", feature = "std"))]
pub use crate::{
	bitbox,
	bitvec,
	boxed::BitBox,
	vec::BitVec,
};
