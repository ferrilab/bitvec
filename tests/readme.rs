
#[cfg(feature = "std")]
use bitvec::prelude::*;

#[cfg(feature = "std")]
use std::iter::repeat;

#[test]
#[cfg(feature = "std")]
fn main() {
	// You can build a static array,
	let arr = bitarr![Lsb0, u32; 0; 64];
	// a hidden static slice,
	let slice = bits![mut LocalBits, u16; 0; 10];
	// or a boxed slice,
	let boxed = bitbox![0; 20];
	// or a vector, using macros that extend the `vec!` syntax
	let mut bv = bitvec![Msb0, u8; 0, 1, 0, 1];

	// You can also explicitly borrow existing scalars,
	let data = 0u32;
	let bits = BitSlice::<Lsb0, _>::from_element(&data);
	// or arrays,
	let mut data = [0u8; 3];
	let bits = BitSlice::<Msb0, _>::from_slice_mut(&mut data[..]);
	// and these are available as shortcut methods:
	let bits = 0u32.view_bits::<Lsb0>();
	let bits = [0u8; 3].view_bits_mut::<Msb0>();

	// `BitVec` implements the entire `Vec` API
	bv.reserve(8);

	// Like `Vec<bool>`, it can be extended by any iterator of `bool`
	bv.extend([false; 4].into_iter());
	bv.extend([true; 4].into_iter());

	// `BitSlice`-owning buffers can be viewed as their raw memory
	assert_eq!(
		bv.as_slice(),
		&[0b0101_0000, 0b1111_0000],
		//  ^ index 0       ^ index 11
	);
	assert_eq!(bv.len(), 12);
	assert!(bv.capacity() >= 16);

	bv.push(true);
	bv.push(false);
	bv.push(true);

	// `BitSlice` implements indexing
	assert!(bv[12]);
	assert!(!bv[13]);
	assert!(bv[14]);
	assert!(bv.get(15).is_none());

	// but not in place position
	// bv[12] = false;
	// because it cannot produce `&mut bool`.
	// instead, use `.get_mut()`:
	*bv.get_mut(12).unwrap() = false;
	// or `.set()`:
	bv.set(12, false);

	// range indexing produces subslices
	let last = &bv[12 ..];
	assert_eq!(last.len(), 3);
	assert!(last.any());

	for _ in 0 .. 3 {
		assert!(bv.pop().is_some());
	}

	//  `BitSlice` implements set arithmetic against any `bool` iterator
	bv &= repeat(true);
	bv |= repeat(false);
	bv ^= repeat(true);
	bv = !bv;
	// the crate no longer implements integer arithmetic, but `BitSlice`
	// can be used to represent varints in a downstream library.

	// `BitSlice`s are iterators:
	assert_eq!(bv.iter().filter(|b| **b).count(), 6,);

	// including mutable iteration, though this requires explicit binding:
	for (idx, mut bit) in bv.iter_mut().enumerate() {
		//      ^^^ not optional
		*bit ^= idx % 2 == 0;
	}

	// `BitSlice` can also implement bitfield memory behavior:
	bv[1 .. 7].store(0x2Eu8);
	assert_eq!(bv[1 .. 7].load::<u8>(), 0x2E);
}
