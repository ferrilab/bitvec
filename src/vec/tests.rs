#![cfg(test)]

use crate::prelude::*;

#[test]
fn push() {
	let mut bvm08 = BitVec::<Msb0, u8>::new();
	assert!(bvm08.is_empty());

	bvm08.push(false);
	assert_eq!(bvm08.len(), 1);
	assert!(!bvm08[0]);

	bvm08.push(true);
	assert_eq!(bvm08.len(), 2);
	assert!(bvm08[1]);

	bvm08.extend(&[true; 3]);
	bvm08.extend(&[false; 3]);
	assert_eq!(bvm08, bits![0, 1, 1, 1, 1, 0, 0, 0]);
}
