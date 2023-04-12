/*! [Issue #96] describes a failure to roundtrip through `bincode` de/ser.

This defect was caused by the use of the `[T]` slice implementation when
serializing a `BitArray`, but the `[T; N]` array implementation when
deserializing. The bincode format uses a dynamic length-aware encoding for
slices, but does not encode the length of arrays, rendering their transport
formats non-interchangeable.

This discrepancy caused `BitArray` to fail to roundtrip through bincode, and is
resolved by separating `BitArray` into its own `serde` implementation that
uses arrays consistently rather than slices.

In the future, the implementation *may* change to use the `BitSlice` transport
format, but only if its data buffer can be reconstituted from the slice model.

`bitvec` does not guarantee cross-version serialization format compatibility.

[Issue #96]: https://github.com/ferrilab/bitvec/issues/96
!*/

#![cfg(feature = "serde")]

use bitvec::prelude::*;

#[test]
fn serialize_bitarr_bincode() {
	type BA = BitArr!(for 8, in u8, Msb0);
	let ba: BA = bitarr![u8, Msb0; 1, 1, 1, 1, 1, 0, 0, 0];

	let bytes = bincode::serialize::<BA>(&ba).unwrap();

	let deserialized: BA = bincode::deserialize::<BA>(bytes.as_ref()).unwrap();

	assert_eq!(deserialized, ba);
}
