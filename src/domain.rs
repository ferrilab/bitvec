/*! Data Model for Bit Sequence Domains

The domains governed by `BitSlice` and owned-variant handles have different
representative states depending on the span of governed elements and live bits.

This module provides representations of the domain states for ease of use by
handle operations.
!*/

use crate::{
	indices::{
		BitIdx,
		BitTail,
	},
	pointer::BitPtr,
	store::BitStore,
};

use either::Either;

/** Alias for the region components produced by the `BitDomain::splat` method.

Splatting a domain will produce either a `(head, element, tail)` tuple when the
region is contained entirely within a single element, or a much more complex
tuple of the head partial element, the body whole elements, and the tail partial
element.

# Types

- `T`: The backing storage the splat is describing.

# Lifetimes

- `'a`: The backing storage the splat is describing.
**/
//  Type bounds in `type` aliases are disallowed, so `T::Access` is not writable
//  here.
pub(crate) type Splat<'a, T, A> = Either<(
	Option<(BitIdx<T>, &'a A)>,
	Option<&'a [A]>,
	Option<(&'a A, BitTail<T>)>,
), (BitIdx<T>, &'a A, BitTail<T>)>;

/** Representations of the state of the bit domain in its containing elements.

# Lifetimes

- `'a`: Lifetime of the containing storage

# Type Parameters

- `T: BitStore` The type of the elements the domain inhabits.
**/
#[derive(Debug)]
pub(crate) enum BitDomain<'a, T>
where T: 'a + BitStore {
	/// Empty domain.
	Empty,
	/// Single element domain which does not reach either edge.
	///
	/// # Members
	///
	/// - `.0`: index of the first live domain bit in the element
	/// - `.1`: mutable reference to the element contatining the domain
	/// - `.2`: index of the first dead bit after the domain
	///
	/// # Behavior
	///
	/// This variant is produced when the domain is contained entirely inside
	/// one element, and does not reach to either edge.
	Minor(BitIdx<T>, &'a T::Access, BitTail<T>),
	/// Multpile element domain which does not reach the edge of its edge
	/// elements.
	///
	/// # Members
	///
	/// - `.0`: index of the first live domain bit in the first element
	/// - `.1`: mutable reference to the partial head edge element
	/// - `.2`: mutable slice handle to the fully-live elements in the interior.
	///   This may be empty.
	/// - `.3`: mutable reference to the partial tail edge element
	/// - `.4`: index of the first dead bit after the domain
	///
	/// # Behavior
	///
	/// This variant is produced when the domain uses at least two elements, and
	/// reaches neither the head edge of the head element nor the tail edge of
	/// the tail element.
	Major(BitIdx<T>, &'a T::Access, &'a [T::Access], &'a T::Access, BitTail<T>),
	/// Domain with a partial head cursor and fully extended tail cursor.
	///
	/// # Members
	///
	/// - `.0`: index of the first live bit in the head element
	/// - `.1`: mutable reference to the partial head element
	/// - `.2`: mutable reference to the full elements of the domain. This may
	///   be empty.
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is past `0`, and
	/// its tail cursor is exactly `T::BITS`.
	PartialHead(BitIdx<T>, &'a T::Access, &'a [T::Access]),
	/// Domain with a fully extended head cursor and partial tail cursor.
	///
	/// # Members
	///
	/// - `.0`: mutable reference to the full elements of the domain. This may
	///   be empty.
	/// - `.1`: mutable reference to the partial tail element
	/// - `.2`: index of the first dead bit after the live bits in the tail
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is exactly `0`,
	/// and its tail cursor is less than `T::BITS`.
	PartialTail(&'a [T::Access], &'a T::Access, BitTail<T>),
	/// Domain which fully spans its containing elements.
	///
	/// # Members
	///
	/// - `.0`: mutable slice handle to the elements containing the domain
	///
	/// # Behavior
	///
	/// This variant is produced when the all elements in the domain are fully
	/// populated.
	Spanning(&'a [T::Access]),
}

impl<'a, T> BitDomain<'a, T>
where T: BitStore {
	/// Unpacks a domain into components.
	///
	/// This is useful for deduplicating code that uses each region component
	/// but does not otherwise branch on region kind.
	///
	/// # Returns
	///
	/// The `Minor` case returns a tuple of the head index, the element, and the
	/// tail index; all other cases return a tuple of optional:
	///
	/// - head element, and start index in that element
	/// - body slice
	/// - tail element, and end index in that element
	pub(crate) fn splat(self) -> Splat<'a, T, T::Access> {
		match self {
			BitDomain::Empty => Either::Left((None, None, None)),
			BitDomain::Minor(h, e, t) => Either::Right((h, e, t)),
			BitDomain::Major(h, head, body, tail, t) => Either::Left((
				Some((h, head)),
				Some(body),
				Some((tail, t)),
			)),
			BitDomain::PartialHead(h, head, body) => Either::Left((
				Some((h, head)),
				Some(body),
				None,
			)),
			BitDomain::PartialTail(body, tail, t) => Either::Left((
				None,
				Some(body),
				Some((tail, t)),
			)),
			BitDomain::Spanning(body) => Either::Left((None, Some(body), None)),
		}
	}

	/// Tests if the variant is `Minor`.
	#[cfg(test)]
	pub(crate) fn is_minor(&self) -> bool {
		match self {
			BitDomain::Minor(..) => true,
			_ => false,
		}
	}

	/// Tests if the variant is `Major`.
	#[cfg(test)]
	pub(crate) fn is_major(&self) -> bool {
		match self {
			BitDomain::Major(..) => true,
			_ => false,
		}
	}

	/// Tests if the variant is `PartialHead`.
	#[cfg(test)]
	pub(crate) fn is_partial_head(&self) -> bool {
		match self {
			BitDomain::PartialHead(..) => true,
			_ => false,
		}
	}

	/// Tests if the variant is `PartialTail`.
	#[cfg(test)]
	pub(crate) fn is_partial_tail(&self) -> bool {
		match self {
			BitDomain::PartialTail(..) => true,
			_ => false,
		}
	}

	/// Tests if the variant is `Spanning`.
	pub(crate) fn is_spanning(&self) -> bool {
		match self {
			BitDomain::Spanning(..) => true,
			_ => false,
		}
	}
}

impl<'a, T> From<BitPtr<T>> for BitDomain<'a, T>
where T: 'a + BitStore {
	fn from(bitptr: BitPtr<T>) -> Self {
		let h = bitptr.head();
		let (e, t) = h.span(bitptr.len());
		let w = T::BITS;
		let data = bitptr.as_access_slice();

		match (*h, e, *t) {
			//  Empty.
			(_, 0, _)           => BitDomain::Empty,
			//  Reaches both edges, for any number of elements.
			(0, _, t) if t == w =>
				BitDomain::Spanning(data),
			//  Reaches only the tail edge, for any number of elements.
			(_, _, t) if t == w => {
				let (head, rest) = data
					.split_first()
					.expect("PartialHead cannot fail to split");
				BitDomain::PartialHead(h, head, rest)
			},
			//  Reaches only the head edge, for any number of elements.
			(0, _, _)           => {
				let (tail, rest) = data
					.split_last()
					.expect("PartialTail cannot fail to split");
				BitDomain::PartialTail(rest, tail, t)
			},
			//  Reaches neither edge, for only one element.
			(_, 1, _)           => BitDomain::Minor(h, &data[0], t),
			//  Reaches neither edge, for multiple elements.
			(_, _, _)           => {
				let (head, body) = data
					.split_first()
					.expect("Major cannot fail to split the head element");
				let (tail, body) = body
					.split_last()
					.expect("Major cannot fail to split the tail element");
				BitDomain::Major(h, head, body, tail, t)
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::indices::Indexable;

	#[test]
	fn minor() {
		let data: u8 = 0u8;
		let bp = BitPtr::new(&data, 1u8.idx(), 6);

		assert!(bp.domain().is_minor());
	}

	#[test]
	fn major() {
		let data: &[u16] = &[0u16, !0u16];
		let bp = BitPtr::new(&data[0], 1u8.idx(), 28);

		assert!(bp.domain().is_major());
	}

	#[test]
	fn partial_head() {
		let data: u32 = 0u32;
		let bp = BitPtr::new(&data, 4u8.idx(), 28);

		assert!(bp.domain().is_partial_head());

		let data: &[u32] = &[0u32, !0u32];
		let bp = BitPtr::new(&data[0], 4u8.idx(), 60);

		assert!(bp.domain().is_partial_head());
	}

	#[test]
	fn partial_tail() {
		let data: u32 = 0u32;
		let bp = BitPtr::new(&data, 0u8.idx(), 60);

		assert!(bp.domain().is_partial_tail());

		let data: &[u32] = &[0u32, !0u32];
		let bp = BitPtr::new(&data[0], 0u8.idx(), 60);

		assert!(bp.domain().is_partial_tail());
	}

	#[test]
	fn spanning() {
		let data: u8 = 0u8;
		let bp = BitPtr::new(&data, 0u8.idx(), 8);

		assert!(bp.domain().is_spanning());

		let data: &[u16] = &[0u16, !0u16];
		let bp = BitPtr::new(&data[0], 0u8.idx(), 32);

		assert!(bp.domain().is_spanning());
	}
}
