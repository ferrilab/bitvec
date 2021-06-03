#![cfg(test)]

use super::*;
use crate::prelude::*;

#[test]
fn allocation() {
	let buf = BitRc::from_bitslice(bits![Msb0, u8; 1, 0, 1, 1]);
	assert_eq!(*buf, bits![1, 0, 1, 1]);
}
