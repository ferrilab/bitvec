#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[test]
#[cfg(feature = "alloc")]
fn issue_65() {
	let mut v = BitVec::<Msb0, u8>::default();

	v.extend_from_bitslice(&bits![Msb0, u8; 0, 1]);

	//  On arm-unknown-linux-gnueabi, this produces 0b0100_0100. I do not know why.
	// assert_eq!(v.into_vec(), [0b0100_0000]);
	assert_eq!(v.len(), 2);
	assert_eq!(v.into_vec()[0] & 0b1100_0000, 0b0100_0000);
}
