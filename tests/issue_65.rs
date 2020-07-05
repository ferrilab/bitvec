use bitvec::prelude::*;

#[test]
#[cfg(feature = "alloc")]
fn issue_65() {
	let mut v = BitVec::<Msb0, u8>::default();

	v.extend_from_bitslice(&bitvec![Msb0, u8; 0, 1]);

	assert_eq!(v.into_vec(), [0b0100_0000]);
}
