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

	let good_slice: &[u8] = unsafe {
		core::slice::from_raw_parts(
			core::ptr::NonNull::<u8>::dangling().as_ptr(),
			BitPtr::<u8>::MAX_ELTS,
		)
	};
	let bs = BitSlice::<BigEndian, _>::from_slice(good_slice);
	assert_eq!(bs.len(), BitPtr::<u8>::MAX_INDX);
}

#[cfg(not(miri))]
#[test]
#[should_panic]
fn from_slice_assertions() {
	let evil_slice: &[u8] = unsafe {
		core::slice::from_raw_parts(
			core::ptr::NonNull::<u8>::dangling().as_ptr(),
			BitPtr::<u8>::MAX_ELTS + 1,
		)
	};
	let _ = BitSlice::<BigEndian, _>::from_slice(evil_slice);
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
	assert!(BitSlice::<BigEndian, u16>::empty().first().is_none());
	assert!(BitSlice::<BigEndian, u32>::empty().first().is_none());

	#[cfg(target_pointer_width = "64")]
	assert!(BitSlice::<BigEndian, u64>::empty().first().is_none());
}

#[test]
fn split_first() {
	assert!(BitSlice::<BigEndian, u8>::empty().split_first().is_none());

	let elt = 129u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
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

#[test]
fn split_last() {
	assert!(BitSlice::<BigEndian, u8>::empty().split_last().is_none());

	let elt = 129u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	let (tail, rest) = bs.split_last().unwrap();
	assert!(tail);
	assert!(rest[0]);
	assert_eq!(rest.len(), 7);
}

#[test]
fn split_last_mut() {
	assert!(BitSlice::<BigEndian, u8>::empty_mut().split_first_mut().is_none());

	let mut elt = 0x0001u16;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	let (tail, rest) = bs.split_last_mut().unwrap();
	assert!(tail);
	assert_eq!(rest.len(), 15);
	rest.set(0, true);
	assert_eq!(elt, 0x8001);

	let bs = BitSlice::<LittleEndian, _>::from_element_mut(&mut elt);
	let (tail, rest) = bs.split_last_mut().unwrap();
	assert!(tail); // set in the previous block
	assert_eq!(rest.len(), 15);
	assert!(rest[0]);
	rest.set(0, false);
	assert_eq!(elt, 0x8000);
}

#[test]
fn last() {
	let elt = 1u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	assert_eq!(bs.last(), Some(true));

	assert!(BitSlice::<BigEndian, u8>::empty().last().is_none());
	assert!(BitSlice::<BigEndian, u16>::empty().last().is_none());
	assert!(BitSlice::<BigEndian, u32>::empty().last().is_none());

	#[cfg(target_pointer_width = "64")]
	assert!(BitSlice::<BigEndian, u64>::empty().last().is_none());
}

#[test]
fn set_get_at() {
	let mut elt = 0u8;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);

	assert!(bs.get(8).is_none());
	assert_eq!(bs.get(0), Some(false));
	bs.set(0, true);
	assert_eq!(bs.get(0), Some(true));

	#[cfg(feature = "std")]
	assert!(std::panic::catch_unwind(|| {
		let mut elt = 0u8;
		let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
		bs.set(9, true);
	}).is_err());

	*bs.at(1) = true;
	assert!(bs.get(1).unwrap());
}

#[test]
fn as_ptr() {
	let mut elt = 0u8;
	let eltptr = &mut elt as *mut u8;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);

	assert_eq!(bs.as_ptr(), eltptr as *const u8);
	assert_eq!(bs.as_mut_ptr(), eltptr);
}

#[test]
fn swap_reverse() {
	let mut elt = 0b1111_0000u8;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);

	assert!(bs[3]);
	assert!(!bs[4]);
	bs.swap(3, 4);
	assert!(!bs[3]);
	assert!(bs[4]);

	bs.reverse();
	assert_eq!(elt, 0b0001_0111);

	//  check that `reverse` correctly handles odd-length slices
	let mut elt = 0b101_0_010_1u8;
	let bs = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);
	let bs = bs.split_last_mut().unwrap().1;
	assert_eq!(bs.len(), 7);
	bs.reverse();
	assert_eq!(elt, 0b010_0_101_1);
}

#[test]
fn iter() {}

#[test]
fn windows() {
	let elt = 0x81u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);
	let mut windows = bs.windows(7);

	let one = windows.next().unwrap();
	assert_eq!(one.len(), 7);
	assert_eq!(one, &bs[.. 7]);

	let two = windows.next().unwrap();
	assert_eq!(two.len(), 7);
	assert_eq!(two, &bs[1 ..]);

	assert!(windows.next().is_none());
}

#[test]
fn chunks() {
	let elt = 0b100_010_01u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);

	let mut chunks = bs.chunks(3);
	assert_eq!(chunks.next().unwrap(), &bs[0 .. 3]);
	assert_eq!(chunks.next().unwrap(), &bs[3 .. 6]);
	assert_eq!(chunks.next().unwrap(), &bs[6 .. 8]);
	assert!(chunks.next().is_none());

	let mut chunks = bs.chunks(3);
	assert_eq!(chunks.next_back().unwrap(), &bs[6 .. 8]);
	assert_eq!(chunks.next_back().unwrap(), &bs[3 .. 6]);
	assert_eq!(chunks.next_back().unwrap(), &bs[0 .. 3]);
	assert!(chunks.next_back().is_none());

	//  chunks_exact

	let elt = 0b100_010_01u8;
	let bs = BitSlice::<BigEndian, _>::from_element(&elt);

	let mut chunks = bs.chunks_exact(3);
	assert_eq!(chunks.next().unwrap(), &bs[0 .. 3]);
	assert_eq!(chunks.next().unwrap(), &bs[3 .. 6]);
	assert!(chunks.next().is_none());
	assert_eq!(chunks.remainder(), &bs[6 .. 8]);

	//  chunks_mut

	let mut elt = 0b0100_1011u8;
	let bits = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);

	let mut chunks = bits.chunks_mut(3);
	chunks.next().unwrap().set(2, true);
	chunks.next().unwrap().set(2, true);
	chunks.next().unwrap().set(1, false);
	assert!(chunks.next().is_none());

	assert_eq!(elt, 0b011_011_10);

	//  chunks_exact_mut

	let mut elt = 0b010_010_11u8;
	let bits = BitSlice::<BigEndian, _>::from_element_mut(&mut elt);

	let mut chunks = bits.chunks_exact_mut(3);
	chunks.next().unwrap().set(2, true);
	chunks.next().unwrap().set(2, true);
	assert!(chunks.next().is_none());
}
