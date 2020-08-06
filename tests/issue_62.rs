/*! GitHub user [@sharksforarms] [reported] thread-safety violations under TSan.
This occurred when running tests using `BitVec::extend_from_bitslice` to combine
buffers.

Removing all code within the tests still causes TSan failures, as of 2020-08-06.
Given that the test code in question does not perform any threading work of its
own, this indicates misbehavior of the test harness, outside of library scope.

However, the memory assertion failures they encountered *do* represent a bug
class in `bitvec`. This is the same bug class that occurred in #65, and has the
same solution: uninitialized memory in the `BitVec` buffer is not required to be
zeroed.

[@sharksforarms]: https://github.com/sharksforarms
[reported]: https://github.com/myrrlyn/bitvec/issues/62
!*/

#![cfg(feature = "alloc")]

use bitvec::prelude::*;

trait Writer {
	fn write(
		&self,
		output_is_le: bool,
		bitsize: Option<usize>,
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

#[test]
fn test_bitvec1() {
	let data = 0x03ABu32;
	let mut data_bits = data.write(true, Some(10));

	assert_eq!(bitvec![Msb0, u8; 1,0,1,0,1,0,1,1, 1,1], data_bits);
	data_bits.zero_padding();
	let data_vec = data_bits.into_vec();

	assert_eq!(vec![0xAB, 0b11_000000], data_vec);
}

#[test]
fn test_bitvec2() {
	let data = 0x03ABu32;
	let data_bits = data.write(false, Some(10)).into_vec();

	assert_eq!(vec![0b11, 0xAB], data_bits);
}

#[test]
fn test_bitvec3() {
	let data = 0xDDCCBBAA;
	let data_bits = data.write(true, None).into_vec();

	assert_eq!(vec![0xAA, 0xBB, 0xCC, 0xDD], data_bits);
}

#[test]
fn test_bitvec4() {
	let data = 0xDDCCBBAA;
	let data_bits = data.write(false, None).into_vec();

	assert_eq!(vec![0xDD, 0xCC, 0xBB, 0xAA], data_bits);
}
