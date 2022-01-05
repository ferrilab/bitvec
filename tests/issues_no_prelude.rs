//! Tests that require **not** importing the `bitvec` prelude at top of scope.

/// The `bitarr!` macro must refer to all of its names directly, without relying
/// on external `use` statements.
#[test]
fn issue_149() {
	let _ = bitvec::bitarr![0; 256];
}
