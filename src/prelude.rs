/*! `bitvec` Prelude

This collects the general public API into a single spot for inclusion, as
`use bitvec::prelude::*;`, without polluting the root namespace of the crate.
!*/

pub use crate::{
	access::BitAccess,
	bits::Bits,
	fields::BitField,
	order::{
		BitOrder,
		Local,
		Lsb0,
		Msb0,
	},
	slice::{
		BitMut,
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
