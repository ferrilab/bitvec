#[test]
#[cfg(feature = "alloc")]
fn main() {
	let _: bitvec::boxed::BitBox = bitvec::bitbox![0];
}
