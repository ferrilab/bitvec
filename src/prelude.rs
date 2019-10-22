/*! `bitvec` Prelude

This collects the general public API into a single spot for inclusion, as
`use bitvec::prelude::*;`, without polluting the root namespace of the crate.
!*/

pub use crate::{
	access::BitAccess,
	bits::{
		Bits,
		BitsMut,
	},
	cursor::{
		Cursor,
		BigEndian,
		LittleEndian,
		Local,
	},
	fields::BitField,
	slice::{
		BitGuard,
		BitSlice,
	},
	store::{
		BitStore,
		Word,
	},
};

#[cfg(feature = "alloc")]
pub use crate::{
	bitbox,
	bitvec,
	boxed::BitBox,
	vec::BitVec,
};
