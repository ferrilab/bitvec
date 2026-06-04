//! Deserialization hardening tests for the dynamic `BitSeq` transport format
//! (`BitVec` / `BitBox`).
//!
//! A malicious or corrupt buffer can carry a `head` / `bits` pair that does not
//! fit the supplied `data` buffer. Such input must produce a deserialization
//! `Err`, never a panic or memory-unsafety abort.
//!
//! Acceptance invariant: a buffer is valid iff `head + bits <= data.len() *
//! bits_of::<T>()`.
//!
//! The `head + bits` overflow cases previously aborted the process (`set_len`
//! assertion followed by a `Vec::from_raw_parts` UB precondition violation in
//! `Drop`); the deserializer now validates `head + bits` against the buffer
//! length and returns `Err`.

#![cfg(all(feature = "std", feature = "serde"))]

use bitvec::prelude::*;
use proptest::prelude::*;

const BITS_PER_ELEM: u64 = 64; // `usize` on the 64-bit test targets

/// Builds a bincode buffer for `BitVec<usize, Lsb0>` with the `head` and `bits`
/// wire fields overwritten.
///
/// Wire layout (bincode, fixint LE): `order: &str` (u64 len + utf8) | `head:
/// BitIdx` (u8 width, u8 index) | `bits: u64` | `data: Vec<usize>` (u64 len +
/// len*8).
fn tampered(data_len: usize, head: u8, bits: u64) -> Vec<u8> {
	let original: BitVec<usize, Lsb0> =
		BitVec::repeat(false, data_len * BITS_PER_ELEM as usize);
	let mut bytes = bincode::serialize(&original).unwrap();

	let order_len = u64::from_le_bytes(bytes[0..8].try_into().unwrap()) as usize;
	let head_index_offset = 8 + order_len + 1;
	let bits_offset = 8 + order_len + 2;

	bytes[head_index_offset] = head;
	bytes[bits_offset..bits_offset + 8].copy_from_slice(&bits.to_le_bytes());
	bytes
}

fn deser(bytes: &[u8]) -> Result<BitVec<usize, Lsb0>, ()> {
	bincode::deserialize::<BitVec<usize, Lsb0>>(bytes).map_err(|_| ())
}

#[test]
fn huge_bits_is_rejected() {
	// Original report: `bits` far above capacity. Fixed; guards the regression.
	assert!(deser(&tampered(1, 0, 1_000_000)).is_err());
}

#[test]
fn bits_one_past_capacity_is_rejected() {
	assert!(deser(&tampered(1, 0, BITS_PER_ELEM + 1)).is_err());
}

#[test]
fn head_plus_bits_within_capacity_roundtrips() {
	let bv = deser(&tampered(1, 32, 32)).expect("32 + 32 == 64 fits");
	assert_eq!(bv.len(), 32);
}

#[test]
fn head_plus_bits_past_capacity_is_rejected() {
	// head=32, bits=64 => needs 96 bits, only 64 available.
	assert!(deser(&tampered(1, 32, BITS_PER_ELEM)).is_err());
}

#[test]
fn head_plus_bits_one_past_capacity_is_rejected() {
	assert!(deser(&tampered(2, 32, 2 * BITS_PER_ELEM - 31)).is_err());
}

#[test]
fn empty_data_nonzero_head_is_rejected() {
	// Zero-length output, empty buffer, but head != 0 => head + bits > 0.
	assert!(deser(&tampered(0, 1, 0)).is_err());
}

proptest! {
	#![proptest_config(ProptestConfig::with_cases(2048))]

	/// Deserialization never panics, and accepts a buffer iff `head + bits`
	/// fits the data capacity.
	#[test]
	fn deserialize_matches_capacity_invariant(
		data_len in 0usize ..= 4,
		head in 0u8 ..= 63,
		bits in 0u64 ..= 320,
	) {
		let fits = head as u64 + bits <= data_len as u64 * BITS_PER_ELEM;
		prop_assert_eq!(deser(&tampered(data_len, head, bits)).is_ok(), fits);
	}

	/// A valid buffer with arbitrary bytes overwritten must never panic on
	/// deserialization; any result is acceptable.
	#[test]
	fn fuzz_mutated_valid_buffer(
		len in 0usize ..= 300,
		muts in prop::collection::vec((any::<usize>(), any::<u8>()), 0 ..= 16),
	) {
		let original: BitVec<usize, Lsb0> = BitVec::repeat(false, len);
		let mut bytes = bincode::serialize(&original).unwrap();
		for (idx, val) in muts {
			if !bytes.is_empty() {
				let i = idx % bytes.len();
				bytes[i] = val;
			}
		}
		let _ = deser(&bytes);
	}

	/// Arbitrary input must never panic on deserialization; any result is
	/// acceptable.
	#[test]
	fn fuzz_arbitrary_bytes(bytes in prop::collection::vec(any::<u8>(), 0 ..= 512)) {
		let _ = deser(&bytes);
	}
}
