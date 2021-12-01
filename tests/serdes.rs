#![cfg(all(feature = "alloc", feature = "serde"))]

use bitvec::prelude::*;

#[test]
fn serdes_slice() {
	let bits = bits![u8, Msb0; 1, 0, 1, 1, 0, 0, 1, 0, 1];
	let json = serde_json::to_string(bits).unwrap();
	assert_eq!(
		json.trim(),
		r#"{"order":"bitvec::order::Msb0","head":{"width":8,"index":0},"bits":9,"data":[178,128]}"#,
	);
}

#[test]
fn serdes_array() {
	let bits = [0x07u8, 0x15].into_bitarray::<Lsb0>();
	let json = serde_json::to_string(&bits).unwrap();
	assert_eq!(
		json.trim(),
		r#"{"order":"bitvec::order::Lsb0","head":{"width":8,"index":0},"bits":16,"data":[7,21]}"#,
	);
	let deser: BitArr![for 16, in u8, Lsb0] =
		serde_json::from_str(&json).unwrap();
	assert_eq!(bits, deser);
}

#[test]
fn serdes_box() {
	let bits = bitbox![u32, Lsb0; 0, 1, 0, 0, 1];
	let json = serde_json::to_string(&bits).unwrap();
	assert_eq!(
		json.trim(),
		r#"{"order":"bitvec::order::Lsb0","head":{"width":32,"index":0},"bits":5,"data":[18]}"#,
	);
	let deser: BitBox<u32, Lsb0> = serde_json::from_str(&json).unwrap();
	assert_eq!(bits, deser);
}

#[test]
#[cfg(target_endian = "little")]
fn serdes_vec() {
	let bits = bitvec![u16, LocalBits; 1, 0, 1, 1, 0];
	let json = serde_json::to_string(&bits).unwrap();
	assert_eq!(
		json.trim(),
		r#"{"order":"bitvec::order::Lsb0","head":{"width":16,"index":0},"bits":5,"data":[13]}"#,
	);
	let deser: BitVec<u16, Lsb0> = serde_json::from_str(&json).unwrap();
	assert_eq!(bits, deser);
}
