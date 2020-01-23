/*! This example shows off de/serializing a bit sequence using serde.

The example uses JSON for simplicity of demonstration; it should work with all
serde-compatible de/ser protocols.
!*/

extern crate bitvec;
extern crate serde;
extern crate serde_json;

#[cfg(all(feature = "alloc", feature = "serde"))]
use bitvec::prelude::*;

#[cfg(all(feature = "alloc", feature = "serde"))]
#[test]
fn serdes() {
	let bv = bitvec![Msb0, u8; 1, 0, 1, 1, 0, 0, 1, 0];
	let json = serde_json::to_string(&bv).expect("cannot fail to serialize");
	assert_eq!(json.trim(), r#"{"head":0,"bits":8,"data":[178]}"#);

	let bb: BitBox<Msb0, u8> =
		serde_json::from_str(&json).expect("cannot fail to deserialize");

	assert!(bb[0]);
	assert_eq!(bb.as_slice()[0], 178);
}
