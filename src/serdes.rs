/*! `serde`-powered de/serialization

This module implements the Serde traits for the `bitvec` types, as possible.

Without an allocator, only `BitSlice` exists, and can only implement
`Serialize`. With an allocator, the `BitBox` and `BitVec` types exist, and are
able to implement `Deserialize` as well.
!*/

#![cfg(all(feature = "serde"))]

use crate::{
	cursor::Cursor,
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
	Serialize,
	ser::{
		Serializer,
		SerializeStruct,
	},
};

#[cfg(feature = "alloc")]
use serde::{
	Deserialize,
	de::{
		self,
		Deserializer,
		Error,
		MapAccess,
		SeqAccess,
		Unexpected,
		Visitor,
	},
};

/// A Serde visitor to pull `BitBox` data out of a serialized stream
#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Default, Debug)]
pub struct BitBoxVisitor<'de, C, T>
where C: Cursor, T: BitStore + Deserialize<'de> {
	_cursor: PhantomData<C>,
	_storage: PhantomData<&'de T>,
}

#[cfg(feature = "alloc")]
impl<'de, C, T> BitBoxVisitor<'de, C, T>
where C: Cursor, T: BitStore + Deserialize<'de> {
	fn new() -> Self {
		BitBoxVisitor { _cursor: PhantomData, _storage: PhantomData }
	}
}

#[cfg(feature = "alloc")]
impl<'de, C, T> Visitor<'de> for BitBoxVisitor<'de, C, T>
where C: Cursor, T: BitStore + Deserialize<'de> {
	type Value = BitBox<C, T>;

	fn expecting(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("A BitSet data series")
	}

	/// Visit a sequence of anonymous data elements. These must be in the order
	/// `usize', `u8`, `u8`, `[T]`.
	fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
	where V: SeqAccess<'de> {
		let head: u8 = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(0, &self))?;
		let bits: usize = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(1, &self))?;
		let data: Box<[T]> = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(2, &self))?;

		let bitptr = BitPtr::new(
			data.as_ptr(),
			head.try_into().map_err(|_| Error::invalid_value(
				Unexpected::Unsigned(head as u64),
				&self,
			))?,
			bits,
		);
		mem::forget(data);
		Ok(unsafe { BitBox::from_raw(bitptr) })
	}

	/// Visit a map of named data elements. These may be in any order, and must
	/// be the pairs `head: u8`, `bits: usize`, and `data: [T]`.
	fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
	where V: MapAccess<'de> {
		let mut head: Option<u8> = None;
		let mut bits: Option<usize> = None;
		let mut data: Option<Box<[T]>> = None;

		while let Some(key) = map.next_key()? {
			match key {
				"head" => if head.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("head"));
				},
				"bits" => if bits.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("bits"));
				},
				"data" => if data.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("data"));
				},
				f => return Err(de::Error::unknown_field(
					f, &["head", "bits", "data"]
				)),
			}
		}
		let head = head.ok_or_else(|| de::Error::missing_field("head"))?;
		let bits = bits.ok_or_else(|| de::Error::missing_field("bits"))?;
		let data = data.ok_or_else(|| de::Error::missing_field("data"))?;

		let bitptr = BitPtr::new(
			data.as_ptr(),
			head.try_into().map_err(|_| Error::invalid_value(
				Unexpected::Unsigned(head as u64),
				&self,
			))?,
			cmp::min(bits, data.len() * T::BITS as usize),
		);
		mem::forget(data);
		Ok(unsafe { BitBox::from_raw(bitptr) })
	}
}

#[cfg(feature = "alloc")]
impl<'de, C, T> Deserialize<'de> for BitBox<C, T>
where C: Cursor, T: 'de + BitStore + Deserialize<'de> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		deserializer
			.deserialize_struct(
				"BitSet",
				&["head", "bits", "data"],
				BitBoxVisitor::new(),
			)
	}
}

#[cfg(feature = "alloc")]
impl<'de, C, T> Deserialize<'de> for BitVec<C, T>
where C: Cursor, T: 'de + BitStore + Deserialize<'de> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		BitBox::deserialize(deserializer).map(Into::into)
	}
}

impl<C, T> Serialize for BitSlice<C, T>
where C: Cursor, T: BitStore + Serialize, T::Access: Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		let head = self.bitptr().head();
		let mut state = serializer.serialize_struct("BitSet", 3)?;

		state.serialize_field("head", &*head)?;
		state.serialize_field("bits", &(self.len() as u64))?;
		state.serialize_field("data", self.as_total_slice())?;

		state.end()
	}
}

#[cfg(feature = "alloc")]
impl<C, T> Serialize for BitBox<C, T>
where C: Cursor, T: BitStore + Serialize, T::Access: Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(&*self, serializer)
	}
}

#[cfg(feature = "alloc")]
impl<C, T> Serialize for BitVec<C, T>
where C: Cursor, T: BitStore + Serialize, T::Access: Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(&*self, serializer)
	}
}

#[cfg(test)]
mod tests {
	use crate::prelude::*;
	use serde_test::{
		Token,
		assert_ser_tokens,
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
		let slice = BitSlice::<BigEndian, u8>::empty();

		assert_ser_tokens(&slice, bvtok![s 0, 0, 0, U8]);

		#[cfg(feature = "alloc")]
		assert_de_tokens(&bitvec![], bvtok![ d 0, 0, 0, U8 ]);
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn small() {
		let bv = bitvec![BigEndian, u8; 1; 5];
		let bs = &bv[1 ..];
		assert_ser_tokens(&bs, bvtok![s 1, 1, 4, U8, 0b1111_1000]);

		let bv = bitvec![LittleEndian, u16; 1; 12];
		assert_ser_tokens(&bv, bvtok![s 1, 0, 12, U16, 0b00001111_11111111]);

		let bb: BitBox<_, _> = bitvec![LittleEndian, u32; 1; 10].into();
		assert_ser_tokens(&bb, bvtok![s 1, 0, 10, U32, 0x00_00_03_FF]);
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn wide() {
		let src: &[u8] = &[0, !0];
		let bs = src.bits::<Local>();
		assert_ser_tokens(&(&bs[1 .. 15]), bvtok![s 2, 1, 14, U8, 0, !0]);
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn deser() {
		let bv = bitvec![BigEndian, u8; 0, 1, 1, 0, 1, 0];
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1000]);
		//  test that the bits outside the bits domain don't matter in deser
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1001]);
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1010]);
		assert_de_tokens(&bv, bvtok![d 1, 0, 6, U8, 0b0110_1011]);
	}
}
