/*! [Issue #96] describes a failure to roundtrip through `bincode` de/ser.

This defect was caused by the use of the `[T]` slice implementation when
serializing a `BitArray`, but the `[T; N]` array implementation when
deserializing. The bincode format uses a dynamic length-aware encoding for
slice references, but can permit arrays to be self-describing, without any
excess data in the transport format.

This discrepancy caused `BitArray` to fail to roundtrip through bincode, and has
been resolved by committing to using only the `[T; N]` de/ser implementation on
both sides of the `serde` interface.

In the future, the implementation *may* change to use the `BitSlice` transport
format. The exact implementation of the transport format is not guaranteed
between major revisions of the crate; however, as it does technically constitute
an ABI, it will only be modified in `0.X` or `X.0` releases.

[Issue #96]: https://github.com/myrrlyn/bitvec/issues/96
!*/

#![cfg(feature = "serde")]

use bitvec::prelude::*;

#[test]
fn serialize_bitarr_bincode() {
	let ba = bitarr![Msb0, u8; 1, 1, 1, 1, 1, 0, 0, 0];

	let bytes = bincode::serialize::<BitArray<_, [u8; 1]>>(&ba)
		.expect("bincode serialization failed");

	let deser = bincode::deserialize::<BitArray<Msb0, [u8; 1]>>(bytes.as_ref())
		.expect("bincode deserialization failed");

	assert_eq!(deser, ba);
}
