//! This test must be run under `cargo +nightly miri test` in order to prove
//! correct handling of the allocation pointer during drop.

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[test]
#[cfg(feature = "alloc")]
fn main() {
	let _ = bitbox![0];
}
