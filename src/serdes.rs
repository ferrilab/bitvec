/*! `serde`-powered de/serialization

This module implements the Serde traits for the `bitvec` types.

Without an allocator, only `BitSlice` exists, and can only implement
`Serialize`. With an allocator, the `BitBox` and `BitVec` types exist, and are
able to implement `Deserialize` as well.
!*/

#![cfg(feature = "serde")]

use crate::{
	domain::Domain,
	mem::BitMemory,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

#[cfg(feature = "alloc")]
use crate::{
	boxed::BitBox,
	pointer::BitPtr,
	vec::BitVec,
};

#[cfg(feature = "alloc")]
use core::{
	cmp,
	convert::TryInto,
	fmt::{
		self,
		Formatter,
	},
	marker::PhantomData,
	mem,
};

use serde::{
	ser::{
		SerializeSeq,
		SerializeStruct,
		Serializer,
	},
	Serialize,
};

use wyz::{
	conv::Conv,
	pipe::Pipe,
	tap::Tap,
};

#[cfg(feature = "alloc")]
use serde::{
	de::{
		self,
		Deserializer,
		MapAccess,
		SeqAccess,
		Unexpected,
		Visitor,
	},
	Deserialize,
};

impl<O, T> Serialize for BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
	T::Mem: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		let head = self.bitptr().head();
		let mut state = serializer.serialize_struct("BitSet", 3)?;

		state.serialize_field("head", &head.value())?;
		state.serialize_field("bits", &(self.len() as u64))?;
		state.serialize_field("data", &self.domain())?;

		state.end()
	}
}

impl<T> Serialize for Domain<'_, T>
where
	T: BitStore,
	T::Mem: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		let iter = self.into_iter();
		let mut state = serializer.serialize_seq(Some(iter.len()))?;

		for elem in iter {
			state.serialize_element(&elem)?;
		}

		state.end()
	}
}

#[cfg(feature = "alloc")]
impl<O, T> Serialize for BitBox<O, T>
where
	O: BitOrder,
	T: BitStore + Serialize,
	T::Mem: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(self.as_bitslice(), serializer)
	}
}

#[cfg(feature = "alloc")]
impl<O, T> Serialize for BitVec<O, T>
where
	O: BitOrder,
	T: BitStore + Serialize,
	T::Mem: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(self.as_bitslice(), serializer)
	}
}

#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug)]
struct BitBoxVisitor<'de, O, T>
where
	O: BitOrder,
	T: 'de + BitStore,
{
	_src: PhantomData<&'de BitSlice<O, T>>,
}

#[cfg(feature = "alloc")]
impl<'de, O, T> BitBoxVisitor<'de, O, T>
where
	O: 'de + BitOrder,
	T: 'de + BitStore,
{
	fn new() -> Self {
		Self { _src: PhantomData }
	}

	/// Constructs a `BitBox` from deserialized components.
	///
	/// # Parameters
	///
	/// - `&self`: A visitor, only needed for access to an error message.
	/// - `head`: The deserialized head-bit index.
	/// - `bits`: The deserialized length counter.
	/// - `data`: A sequence of data elements containing the bitslice.
	///
	/// # Returns
	///
	/// The result of assembling the deserialized components into a `BitBox`.
	/// This can fail if the `head` is invalid, or if the deserialized data
	/// cannot be encoded into a `BitPtr`.
	fn assemble<E>(
		&self,
		head: u8,
		bits: usize,
		data: Box<[T::Mem]>,
	) -> Result<<Self as Visitor<'de>>::Value, E>
	where
		T::Mem: Deserialize<'de>,
		E: de::Error,
	{
		//  Assemble a region pointer
		BitPtr::new(
			data.as_ptr() as *mut T,
			//  Attempt to read the `head` index as a `BitIdx` bounded by the
			//  destination type.
			head.try_into().map_err(|_| {
				de::Error::invalid_value(
					head.conv::<u64>().pipe(Unexpected::Unsigned),
					&"a head-bit index less than the deserialized element \
					  type’s bit width",
				)
			})?,
			//  Ensure that the `bits` counter is not lying about the data size.
			cmp::min(bits, data.len() * T::Mem::BITS as usize),
		)
		//  Fail if the source cannot be encoded into a bit pointer.
		.ok_or_else(|| {
			de::Error::invalid_value(
				Unexpected::Other("invalid bit-region source data"),
				self,
			)
		})?
		//  No more branches remain, only typesystem manipulation,
		.pipe(BitPtr::to_bitslice_ptr_mut)
		.pipe(|bp| unsafe { BitBox::from_raw(bp) })
		.pipe(Ok)
		//  And destructor disarming (the returned `BitBox` now owns the `data`
		//  memory).
		.tap(|_| mem::forget(data))
	}
}

#[cfg(feature = "alloc")]
impl<'de, O, T> Visitor<'de> for BitBoxVisitor<'de, O, T>
where
	O: BitOrder,
	T: 'de + BitStore,
	T::Mem: Deserialize<'de>,
{
	type Value = BitBox<O, T>;

	fn expecting(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("a BitSet data series")
	}

	/// Visit a sequence of anonymous data elements. These must be in the order
	/// `u8` (head-bit index), `u64` (length counter), `[T]` (data contents).
	fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
	where V: SeqAccess<'de> {
		let head = seq
			.next_element::<u8>()?
			.ok_or_else(|| de::Error::invalid_length(0, &self))?;
		let bits = seq
			.next_element::<u64>()?
			.ok_or_else(|| de::Error::invalid_length(1, &self))?;
		let data = seq
			.next_element::<Box<[T::Mem]>>()?
			.ok_or_else(|| de::Error::invalid_length(2, &self))?;

		self.assemble(head, bits as usize, data)
	}

	/// Visit a map of named data elements. These may be in any order, and must
	/// be the pairs `head: u8`, `bits: u64`, and `data: [T]`.
	fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
	where V: MapAccess<'de> {
		let mut head: Option<u8> = None;
		let mut bits: Option<u64> = None;
		let mut data: Option<Box<[T::Mem]>> = None;

		while let Some(key) = map.next_key()? {
			match key {
				"head" => {
					if head.replace(map.next_value()?).is_some() {
						return Err(de::Error::duplicate_field("head"));
					}
				},
				"bits" => {
					if bits.replace(map.next_value()?).is_some() {
						return Err(de::Error::duplicate_field("bits"));
					}
				},
				"data" => {
					if data.replace(map.next_value()?).is_some() {
						return Err(de::Error::duplicate_field("data"));
					}
				},
				f => {
					return Err(de::Error::unknown_field(f, &[
						"head", "bits", "data",
					]));
				},
			}
		}
		let head = head.ok_or_else(|| de::Error::missing_field("head"))?;
		let bits = bits.ok_or_else(|| de::Error::missing_field("bits"))?;
		let data = data.ok_or_else(|| de::Error::missing_field("data"))?;

		self.assemble(head, bits as usize, data)
	}
}

#[cfg(feature = "alloc")]
impl<'de, O, T> Deserialize<'de> for BitBox<O, T>
where
	O: 'de + BitOrder,
	T: 'de + BitStore,
	T::Mem: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		deserializer.deserialize_struct(
			"BitSet",
			&["head", "bits", "data"],
			BitBoxVisitor::new(),
		)
	}
}

#[cfg(feature = "alloc")]
impl<'de, O, T> Deserialize<'de> for BitVec<O, T>
where
	O: 'de + BitOrder,
	T: 'de + BitStore,
	T::Mem: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		BitBox::deserialize(deserializer).map(BitBox::into_bitvec)
	}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;

	use serde_test::{
		assert_ser_tokens,
		Token,
	};

	#[cfg(feature = "alloc")]
	use serde_test::assert_de_tokens;

	macro_rules! bvtok {
		( s $elts:expr, $head:expr, $bits:expr, $ty:ident $( , $data:expr )* ) => {
			&[
				Token::Struct { name: "BitSet", len: 3, },
				Token::Str("head"), Token::U8( $head ),
				Token::Str("bits"), Token::U64( $bits ),
				Token::Str("data"), Token::Seq { len: Some( $elts ) },
				$( Token:: $ty ( $data ), )*
				Token::SeqEnd,
				Token::StructEnd,
			]
		};
		( d $elts:expr, $head:expr, $bits:expr, $ty:ident $( , $data:expr )* ) => {
			&[
				Token::Struct { name: "BitSet", len: 3, },
				Token::BorrowedStr("head"), Token::U8( $head ),
				Token::BorrowedStr("bits"), Token::U64( $bits ),
				Token::BorrowedStr("data"), Token::Seq { len: Some( $elts ) },
				$( Token:: $ty ( $data ), )*
				Token::SeqEnd,
				Token::StructEnd,
			]
		};
	}

	#[test]
	fn empty() {
		let slice = BitSlice::<Msb0, u8>::empty();

		assert_ser_tokens(&slice, bvtok![s 0, 0, 0, U8]);

		#[cfg(feature = "alloc")]
		assert_de_tokens(&bitvec![], bvtok![ d 0, 0, 0, U8 ]);
	}

	#[test]
	fn small() {
		let bits = 0b1111_1000u8.view_bits::<Msb0>();
		let bits = &bits[1 .. 5];
		assert_ser_tokens(&bits, bvtok![s 1, 1, 4, U8, 0b1111_1000]);

		let bits = 0b00001111_11111111u16.view_bits::<Lsb0>();
		let bits = &bits[.. 12];
		assert_ser_tokens(&bits, bvtok![s 1, 0, 12, U16, 0b00001111_11111111]);

		let bits = 0b11_11111111u32.view_bits::<Local>();
		let bits = &bits[.. 10];
		assert_ser_tokens(&bits, bvtok![s 1, 0, 10, U32, 0x00_00_03_FF]);
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn wide() {
		let src: &[u8] = &[0, !0];
		let bs = src.view_bits::<Local>();
		assert_ser_tokens(&(&bs[1 .. 15]), bvtok![s 2, 1, 14, U8, 0, !0]);
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn deser() {
		let bv = bitvec![Msb0, u8; 0, 1, 1, 0, 1, 0];
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1000]);
		//  test that the bits outside the bits domain don't matter in deser
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1001]);
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1010]);
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1011]);
	}
}
