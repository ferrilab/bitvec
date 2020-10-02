//! Test cases for defect reports.

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

/** Test case for [Issue #10], opened by [@overminder].

Issue #10 is a bug in the implementation of `<BitSlice as ToOwned>::to_owned`.
That trait implementation used `BitVec::from_bitslice`, which had the incorrect
behavior of cloning the underlying `&[T]` slice into a vector. Bit slices are
capable of partial-element heads, while bit vectors are not (at time of issue).
This meant that cloning an intermediate span copied from the start of the first
element, rather than from the first bit.

The fix was to use `<BitVec as FromIterator<bool>>::from_iter` to power both
`BitVec::from_bitslice` and `<BitSlice as ToOwned>::to_owned`.

In the future, it may be possible to revert to the original
`<[T] as ToOwned>::to_owned` implementation, if `BitVec` becomes capable of
partial heads without loss of pointer information.

[Issue #10]: https://github.com/myrrlyn/bitvec/issues/10
[@overminder]: https://github.com/overminder
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_10() {
	let bv = bitvec![LocalBits, u8;
		0, 0, 0, 0,
		0, 0, 0, 1,
		1, 0, 0, 0,
		0, 0, 0, 1,
	];

	let slice = &bv[4 .. 12];
	assert_eq!(slice.len(), 8);
	assert!(!slice[0]);
	assert!(slice[3]);
	assert!(slice[4]);
	assert!(!slice[7]);

	let mut bv2 = slice.to_owned();
	assert_eq!(bv2, slice);
	assert!(!bv2[0]);
	assert!(bv2[3]);
	assert!(bv2[4]);
	assert!(!bv2[7]);

	bv2.force_align();
	//  These may be removed in the future.
	assert_eq!(bv2.as_slice().len(), 1);
	assert_eq!(bv2.as_slice()[0], 0x18);
}

/** Test case for [Issue #33], opened by [@jonas-schievink].

This report discovered an error in the implementation of `BitVec::reserve`,
which caused it to fail to reällocate in certain conditions.

The error was that the `reserve` method was testing the reservation amount
passed in to `Vec::reserve` against the currently-allocated *capacity*, not the
currently-occupied *element length*. `Vec::reserve` expects the difference to be
against the element length, so `BitVec::reserve` was estimating too few elements
and `Vec::reserve` did not see the request amount as requiring a reällocation.

`BitVec::reserve` now tests the reservation amount against the current element
length, which produces the correct reservation request for `Vec::reserve`,
fixing the error.

[Issue #33]: https://github.com/myrrlyn/bitvec/issues/33
[@jonas-schievink]: https://github.com/jonas-schievink
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_33() {
	let mut swdio = BitVec::<Lsb0, u8>::new();

	swdio.resize(64, true);

	let mut seq = 0xE79E; // LSb first
	for _ in 0 .. 16 {
		swdio.push(seq & 0b1 != 0);
		seq >>= 1;
	}

	swdio.reserve(64);
	swdio.resize(swdio.len() + 64, true);

	swdio.resize(swdio.len() + 10, false);
}

/** Test case for [Issue #62], reported by GitHub user [@sharksforarms].

They reported thread-safety violations under TSan. This occurred when running
tests using `BitVec::extend_from_bitslice` to combine buffers.

Removing all code within the tests still causes TSan failures, as of 2020-08-06.
Given that the test code in question does not perform any threading work of its
own, this indicates misbehavior of the test harness, outside of library scope.

However, the memory assertion failures they encountered *do* represent a bug
class in `bitvec`. This is the same bug class that occurred in #65, and has the
same solution: uninitialized memory in the `BitVec` buffer is not required to be
zeroed.

[Issue #62]: https://github.com/myrrlyn/bitvec/issues/62
[@sharksforarms]: https://github.com/sharksforarms
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_62() {
	trait Writer {
		fn write(
			&self,
			output_is_le: bool,
			bit_size: Option<usize>,
		) -> BitVec<Msb0, u8>;
	}

	impl Writer for u32 {
		fn write(
			&self,
			output_is_le: bool,
			bit_size: Option<usize>,
		) -> BitVec<Msb0, u8>
		{
			let input = if output_is_le {
				self.to_le_bytes()
			}
			else {
				self.to_be_bytes()
			};
			let input_bits: BitVec<Msb0, u8> =
				BitSlice::from_slice(&input).unwrap().into();

			let res_bits: BitVec<Msb0, u8> = {
				if let Some(bit_size) = bit_size {
					if bit_size > input_bits.len() {
						todo!() // TODO: return err
					}

					if output_is_le {
						// Example read 10 bits u32 [0xAB, 0b11_000000]
						// => [10101011, 00000011, 00000000, 00000000]
						let mut res_bits = BitVec::<Msb0, u8>::new();
						let mut remaining_bits = bit_size;
						// println!("input_bits: {}", input_bits);
						for chunk in input_bits.chunks(8) {
							println!("chunk: {}", chunk);
							if chunk.len() > remaining_bits {
								res_bits.extend_from_bitslice(
									&chunk[chunk.len() - remaining_bits ..],
								);
								break;
							}
							else {
								res_bits.extend_from_bitslice(chunk)
							}
							remaining_bits -= chunk.len();
						}

						res_bits
					}
					else {
						// Example read 10 bits u32 [0xAB, 0b11_000000]
						// => [00000000, 00000000, 00000010, 10101111]
						input_bits[input_bits.len() - bit_size ..].into()
					}
				}
				else {
					input_bits
				}
			};

			res_bits
		}
	}

	let data = 0x03ABu32;
	let data_bits = data.write(true, Some(10));
	assert_eq!(bitvec![Msb0, u8; 1,0,1,0,1,0,1,1, 1,1], data_bits);
	let data_vec = data_bits.into_vec();
	assert_eq!(vec![0xAB, 0b11_000000], data_vec);

	let data = 0x03ABu32;
	let data_bits = data.write(false, Some(10)).into_vec();
	assert_eq!(vec![0b11, 0xAB], data_bits);

	let data = 0xDDCCBBAA;
	let data_bits = data.write(true, None).into_vec();
	assert_eq!(vec![0xAA, 0xBB, 0xCC, 0xDD], data_bits);

	let data = 0xDDCCBBAA;
	let data_bits = data.write(false, None).into_vec();
	assert_eq!(vec![0xDD, 0xCC, 0xBB, 0xAA], data_bits);
}

/** Test case for [Issue #65], opened by [@inikulin].

This issue found the use of uninitialized memory in
`BitVec::extend_from_bitslice` causing non-deterministic behavior.

[Issue #65]: https://github.com/myrrlyn/bitvec/issues/65
[@inikulin]: https://github.com/inikulin
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_65() {
	let mut v = BitVec::<Msb0, u8>::default();
	v.extend_from_bitslice(bits![Msb0, u8; 0, 1]);
	assert_eq!(v.into_vec(), [0b0100_0000u8]);
}

/** Test case for [Issue #69], opened by [@YoshikiTakashima].

This report shows a dereference after deällocation. This is not *strictly* true:
the destructor only used the value of the pointer, and did not issue a load or
store instruction through it, but even that use was sufficient to trip Miri’s
alarms.

This test is only useful when run under `cargo +nightly miri test`. It asserts
that the allocation pointer is correctly managed during drop.

[Issue #10]: https://github.com/myrrlyn/bitvec/issues/69
[@YoshikiTakashima]: https://github.com/YoshikiTakashima
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_69() {
	let _ = bitbox![0];
}

/** Test case for [Issue #77], opened by [@Cryptjar].

This report describes a segmentation fault found when using the `.rev()`
iterator adaptor. The fault was traced to an incorrect behavior in the
`ExactSizeIterator::len` implementation of `src/slice/iter.rs:iter!`. The
difference between the first and one-past-the-last pointers was incorrectly
scaled by the bit width of the `T` storage parameter, while pointers are
*always* byte-stepped, and should only be scaled by the bit width of a byte, not
the bit width of `T`.

Embarassingly, I made the same mistake in the `ptr_diff` implementation used in
the `nom` compatibility branch. At least I’m consistent.

The overly-large scaling in computation of `.len()` caused `Rev<>`, which relies
on a correct implementation of `.len()`, to attempt to access memory out of
bounds inside `Iter::nth`.

[Issue #77]: https://github.com/myrrlyn/bitvec/issues/77
[@Cryptjar]: https://github.com/Cryptjar
**/
#[test]
#[cfg(feature = "alloc")]
fn issue_77() {
	// The argument of `take`. If above "SOME" threshold, it will panic!
	// If below "the" threshold, the assert will fail instead.
	//
	// It appears that the threshold for normal execution is 4,
	// but when executing the binary via `gdb` it is 6.
	const N: usize = 6;

	let mut bv: BitVec = BitVec::new();
	// Must be at least the 'register size', but may be much larger
	bv.resize(64, true);

	// Here the complete iter-rev-take-rev-sequence is mandatory to reproduce the
	// error, just the `collect` is here for convenience.
	let last_few: Vec<_> = bv.iter().rev().take(N).rev().collect();

	// Also notice, `bv` only contains `true`, but with `N` < 4, the `last_few`
	// are all `false`!!!
	assert_eq!(&[&true; N], last_few.as_slice());
}
