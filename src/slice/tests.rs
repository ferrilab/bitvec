/*! Unit tests for the `slice` module.

The module is so large already that separating local tests out into a discrete
submodule was less ungainly.
!*/

#![cfg(test)]

use super::*;
use crate::cursor::LittleEndian;

#[test]
fn empty() {
	assert!(BitSlice::<BigEndian, u8>::empty().is_empty());
	assert!(BitSlice::<BigEndian, u16>::empty().is_empty());
	assert!(BitSlice::<BigEndian, u32>::empty().is_empty());

	#[cfg(target_pointer_width = "64")]
	assert!(BitSlice::<BigEndian, u64>::empty().is_empty());

	assert!(BitSlice::<BigEndian, u8>::empty_mut().is_empty());
	assert!(BitSlice::<BigEndian, u16>::empty_mut().is_empty());
	assert!(BitSlice::<BigEndian, u32>::empty_mut().is_empty());

	#[cfg(target_pointer_width = "64")]
	assert!(BitSlice::<BigEndian, u64>::empty_mut().is_empty());
}

#[test]
fn from_element() {
	let elt = 1u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.len(), 8);
	assert!(bs[7]);

	let elt = 1u16;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.len(), 16);
	assert!(bs[15]);

	let elt = 1u32;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.len(), 32);
	assert!(bs[31]);

	#[cfg(target_pointer_width = "64")] {

	let elt = 1u64;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.len(), 64);
	assert!(bs[63]);

	}
}

#[test]
fn from_element_mut() {
	let mut elt = 0u8;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	assert_eq!(bs.len(), 8);
	bs.set(7, true);
	assert_eq!(elt, 1);

	let mut elt = 0u16;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	assert_eq!(bs.len(), 16);
	bs.set(15, true);
	assert_eq!(elt, 1);

	let mut elt = 0u32;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	assert_eq!(bs.len(), 32);
	bs.set(31, true);
	assert_eq!(elt, 1);

	#[cfg(target_pointer_width = "64")] {

	let mut elt = 0u64;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	assert_eq!(bs.len(), 64);
	bs.set(63, true);
	assert_eq!(elt, 1);

	}
}

#[test]
fn from_slice() {
	let elts = [0u8, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice(&elts[..]);
	assert_eq!(bs.len(), 16);
	assert!(bs.some());
	assert_eq!(bs.count_ones(), 8);
	assert_eq!(bs.count_zeros(), 8);

	let elts = [0u16, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice(&elts[..]);
	assert_eq!(bs.len(), 32);
	assert!(bs.some());
	assert_eq!(bs.count_ones(), 16);
	assert_eq!(bs.count_zeros(), 16);

	let elts = [0u32, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice(&elts[..]);
	assert_eq!(bs.len(), 64);
	assert!(bs.some());
	assert_eq!(bs.count_ones(), 32);
	assert_eq!(bs.count_zeros(), 32);

	#[cfg(target_pointer_width = "64")] {

	let elts = [0u64, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice(&elts[..]);
	assert_eq!(bs.len(), 128);
	assert!(bs.some());
	assert_eq!(bs.count_ones(), 64);
	assert_eq!(bs.count_zeros(), 64);

	}
}

#[test]
fn from_slice_mut() {
	let mut elts = [0u8, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice_mut(&mut elts[..]);
	assert_eq!(bs.len(), 16);
	assert!(!bs[0]);
	bs.set(0, true);
	assert!(bs[0]);
	assert_ne!(elts[0], 0);

	let mut elts = [0u16, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice_mut(&mut elts[..]);
	assert_eq!(bs.len(), 32);
	assert!(!bs[0]);
	bs.set(0, true);
	assert!(bs[0]);
	assert_ne!(elts[0], 0);

	let mut elts = [0u32, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice_mut(&mut elts[..]);
	assert_eq!(bs.len(), 64);
	assert!(!bs[0]);
	bs.set(0, true);
	assert!(bs[0]);
	assert_ne!(elts[0], 0);

	#[cfg(target_pointer_width = "64")] {

	let mut elts = [0u64, !0];
	let bs = BitSlice::<BigEndian, _>::from_slice_mut(&mut elts[..]);
	assert_eq!(bs.len(), 128);
	assert!(!bs[0]);
	bs.set(0, true);
	assert!(bs[0]);
	assert_ne!(elts[0], 0);

	}
}

#[test]
fn len() {
	let elts = [0u32; 1024];
	let bs = BitSlice::<BigEndian, _>::from_slice(&elts[..]);
	for n in 1 .. (32 * 1024) {
		assert!(!bs.is_empty());
		assert_eq!(bs[.. n].len(), n);
	}
}

#[test]
fn first() {
	let elt = 128u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.first(), Some(true));
	assert!(BitSlice::<BigEndian, u8>::empty().first().is_none());
}

#[test]
fn split_first() {
	assert!(BitSlice::<BigEndian, u8>::empty().split_first().is_none());

	let elt = 129u8;
	let bs = BitSlice::<BigEndian, u8>::from_element(&elt);
	let (head, rest) = bs.split_first().unwrap();
	assert!(head);
	assert!(rest[6]);
	assert_eq!(rest.len(), 7);
}

#[test]
fn split_first_mut() {
	assert!(BitSlice::<BigEndian, u8>::empty_mut().split_first_mut().is_none());

	let mut elt = 0x8001u16;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	let (head, rest) = bs.split_first_mut().unwrap();
	assert!(head);
	assert_eq!(rest.len(), 15);
	rest.set(0, true);
	assert_eq!(elt, 0xC001);

	let bs = BitSlice::<LittleEndian, _>::from_element_mut(&mut elt);
	let (tail, rest) = bs.split_first_mut().unwrap();
	assert!(tail);
	assert_eq!(rest.len(), 15);
	rest.set(0, true);
	assert_eq!(elt, 0xC003);
}
