/*! This example shows off de/serializing a bit sequence using serde.

The example uses JSON for simplicity of demonstration; it should work with all
serde-compatible de/ser protocols.
!*/

#[cfg(all(feature = "alloc", feature = "serde"))]
use bitvec::prelude::*;

#[test]
#[cfg(all(feature = "alloc", feature = "serde"))]
fn serdes_array() {
	let ba = bitarr![Msb0, u8; 1, 0, 1, 1, 0, 0, 1, 0];
	let json = serde_json::to_string(&ba).expect("cannot fail to serialize");
	assert_eq!(json.trim(), r#"[178]"#);

	let ba: BitArray<Msb0, [u8; 1]> =
		serde_json::from_str(&json).expect("cannot fail to deserialize");
	assert!(ba[0]);
	assert_eq!(ba.as_slice()[0], 178);

	//  Note: Scalar arrays do not (yet) serialize as a sequence of one element.
	let ba_bare: BitArray<Msb0, u8> =
		serde_json::from_str(&"178").expect("cannot fail to deserialize");
	assert_eq!(ba.as_bitslice(), ba_bare.as_bitslice());
}

#[test]
#[cfg(all(feature = "alloc", feature = "serde"))]
fn serdes_bitvec() {
	let bv = bitvec![Msb0, u8; 1, 0, 1, 1, 0, 0, 1, 0];
	let json = serde_json::to_string(&bv).expect("cannot fail to serialize");
	assert_eq!(json.trim(), r#"{"head":0,"bits":8,"data":[178]}"#);

	let bb: BitBox<Msb0, u8> =
		serde_json::from_str(&json).expect("cannot fail to deserialize");

	assert!(bb[0]);
	assert_eq!(bb.as_slice()[0], 178);
}
