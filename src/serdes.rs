/*! `serde`-powered de/serialization

!*/

#![cfg(all(feature = "alloc", feature = "serdes"))]

use super::{
	BitBox,
	BitPtr,
	BitSlice,
	BitVec,
	Bits,
	Cursor,
};
use core::{
	cmp,
	mem,
};
use serde::{
	Deserialize,
	Serialize,
	de::{
		self,
		Deserializer,
		MapAccess,
		SeqAccess,
		Visitor,
	},
	ser::{
		Serializer,
		SerializeStruct,
	},
};
use std::{
	fmt::{
		self,
		Formatter,
	},
	marker::PhantomData,
};

/// Markers for the four fields of a bit slice handle and data.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
#[repr(u8)]
enum Field {
	/// Element count
	Elts = 0,
	/// Head cursor
	Head = 1,
	//// Tail cursor
	Tail = 2,
	/// The data making up the slice.
	Data = 3,
}

/// A Serde visitor to pull `BitBox` data out of a serialized stream
#[derive(Clone, Copy, Default, Debug)]
pub struct BitBoxVisitor<'de, C, T>
where C: Cursor, T: Bits + Deserialize<'de> {
	_cursor: PhantomData<C>,
	_storage: PhantomData<&'de T>,
}

impl<'de, C, T> BitBoxVisitor<'de, C, T>
where C: Cursor, T: Bits + Deserialize<'de> {
	fn new() -> Self {
		BitBoxVisitor { _cursor: PhantomData, _storage: PhantomData }
	}
}

impl<'de, C, T> Visitor<'de> for BitBoxVisitor<'de, C, T>
where C: Cursor, T: Bits + Deserialize<'de> {
	type Value = BitBox<C, T>;

	fn expecting(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.write_str("A BitSet data series")
	}

	/// Visit a sequence of anonymous data elements. These must be in the order
	/// `usize', `u8`, `u8`, `[T]`.
	fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
	where V: SeqAccess<'de> {
		let elts: usize = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(0, &self))?;
		let head: u8 = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(1, &self))?;
		let tail: u8 = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(2, &self))?;
		let data: Box<[T]> = seq.next_element()?
			.ok_or_else(|| de::Error::invalid_length(3, &self))?;

		let bitptr = BitPtr::new(data.as_ptr(), cmp::min(elts, data.len()), head, tail);
		mem::forget(data);
		Ok(unsafe { BitBox::from_raw(bitptr) })
	}

	/// Visit a map of named data elements. These may be in any order, and must
	/// be the pairs `elts: usize`, `head: u8`, `tail: u8`, and `data: [T]`.
	fn visit_map<V>(self, mut map: V) -> Result<Self::Value, V::Error>
	where V: MapAccess<'de> {
		let mut elts: Option<usize> = None;
		let mut head: Option<u8> = None;
		let mut tail: Option<u8> = None;
		let mut data: Option<Box<[T]>> = None;

		while let Some(key) = map.next_key()? {
			match key {
				Field::Elts => if elts.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("elts"));
				}
				Field::Head => if head.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("head"));
				}
				Field::Tail => if tail.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("tail"));
				}
				Field::Data => if data.replace(map.next_value()?).is_some() {
					return Err(de::Error::duplicate_field("data"));
				}
			}
		}
		let elts = elts.ok_or_else(|| de::Error::missing_field("elts"))?;
		let head = head.ok_or_else(|| de::Error::missing_field("head"))?;
		let tail = tail.ok_or_else(|| de::Error::missing_field("tail"))?;
		let data = data.ok_or_else(|| de::Error::missing_field("data"))?;

		let bitptr = BitPtr::new(data.as_ptr(), cmp::min(elts, data.len()), head, tail);
		mem::forget(data);
		Ok(unsafe { BitBox::from_raw(bitptr) })
	}
}

impl<'de, C, T> Deserialize<'de> for BitBox<C, T>
where C: Cursor, T: 'de + Bits + Deserialize<'de> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		deserializer.deserialize_struct("BitSet", &["elts", "head", "tail", "data"], BitBoxVisitor::new())
	}
}

impl<'de, C, T> Deserialize<'de> for BitVec<C, T>
where C: Cursor, T: 'de + Bits + Deserialize<'de> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where D: Deserializer<'de> {
		BitBox::deserialize(deserializer).map(Into::into)
	}
}

impl<C, T> Serialize for BitSlice<C, T>
where C: Cursor, T: Bits + Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		let (e, h, t) = self.bitptr().region_data();
		let mut state = serializer.serialize_struct("BitSet", 4)?;

		state.serialize_field("elts", &e)?;
		state.serialize_field("head", &*h)?;
		state.serialize_field("tail", &*t)?;
		state.serialize_field("data", self.as_ref())?;

		state.end()
	}
}

impl<C, T> Serialize for BitBox<C, T>
where C: Cursor, T: Bits + Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(&*self, serializer)
	}
}

impl<C, T> Serialize for BitVec<C, T>
where C: Cursor, T: Bits + Serialize {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where S: Serializer {
		BitSlice::serialize(&*self, serializer)
	}
}
