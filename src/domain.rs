/*! Data Model for Bit Sequence Domains

The domains governed by `BitSlice` and owned-variant handles have different
representative states depending on the span of governed elements and live bits.

This module provides representations of the domain states for ease of use by
handle operations.
!*/

use crate::{
	pointer::BitPtr,
	store::{
		BitAccess,
		BitIdx,
		BitStore,
		TailIdx,
	},
};

/// Variant markers for the kinds of domains.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum BitDomainKind {
	/// Zero elements
	Empty,
	/// Single element, partial on both edges
	Minor,
	/// Multiple elements, partial on both edges
	Major,
	/// Partial on head only
	PartialHead,
	/// Partial on tail only
	PartialTail,
	/// Fully spans elements
	Spanning,
}

impl<T> From<&BitPtr<T>> for BitDomainKind
where T: BitStore {
	fn from(bitptr: &BitPtr<T>) -> Self {
		let h = bitptr.head();
		let (e, t) = h.span(bitptr.len());
		let w = T::BITS;

		match (*h, e, *t) {
			//  Empty
			(_, 0, _)           => BitDomainKind::Empty,
			//  Reaches both edges, for any number of elements
			(0, _, t) if t == w => BitDomainKind::Spanning,
			//  Reaches only the tail edge, for any number of elements
			(_, _, t) if t == w => BitDomainKind::PartialHead,
			//  Reaches only the head edge, for any number of elements
			(0, _, _)           => BitDomainKind::PartialTail,
			//  Reaches neither edge, for one element
			(_, 1, _)           => BitDomainKind::Minor,
			//  Reaches neither edge, for multiple elements
			(_, _, _ )          => BitDomainKind::Major,
		}
	}
}

/** Representations of the state of the bit domain in its containing elements.

# Lifetimes

- `'a`: Lifetime of the containing storage

# Type Parameters

- `T` The type of the elements the domain inhabits.
**/
#[derive(Clone, Debug)]
pub enum BitDomain<'a, T>
where T: 'a + BitStore {
	/// Empty domain.
	Empty,
	/// Single element domain which does not reach either edge.
	///
	/// # Members
	///
	/// - `.0`: index of the first live domain bit in the element
	/// - `.1`: reference to the element contatining the domain
	/// - `.2`: index of the first dead bit after the domain
	///
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	/// - `.2` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain is contained entirely inside
	/// one element, and does not reach to either edge.
	Minor(BitIdx<T>, &'a T, TailIdx<T>),
	/// Multpile element domain which does not reach the edge of its edge
	/// elements.
	///
	/// # Members
	///
	/// - `.0`: index of the first live domain bit in the first element
	/// - `.1`: reference to the partial head edge element
	/// - `.2`: slice handle to the fully-live elements in the interior. This
	///   may be empty.
	/// - `.3`: reference to the partial tail edge element
	/// - `.4`: index of the first dead bit after the domain
	///
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	/// - `.4` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain uses at least two elements, and
	/// reaches neither the head edge of the head element nor the tail edge of
	/// the tail element.
	Major(BitIdx<T>, &'a T, &'a [T], &'a T, TailIdx<T>),
	/// Domain with a partial head cursor and fully extended tail cursor.
	///
	/// # Members
	///
	/// - `.0`: index of the first live bit in the head element
	/// - `.1`: reference to the partial head element
	/// - `.2`: reference to the full elements of the domain. This may be empty.
	///
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is past `0`, and
	/// its tail cursor is exactly `T::BITS`.
	PartialHead(BitIdx<T>, &'a T, &'a [T]),
	/// Domain with a fully extended head cursor and partial tail cursor.
	///
	/// # Members
	///
	/// - `.0`: reference to the full elements of the domain. This may be empty.
	/// - `.1`: reference to the partial tail element
	/// - `.2`: index of the first dead bit after the live bits in the tail
	///
	/// # Invariants
	///
	/// - `.2` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is exactly `0`,
	/// and its tail cursor is less than `T::BITS`.
	PartialTail(&'a [T], &'a T, TailIdx<T>),
	/// Domain which fully spans its containing elements.
	///
	/// # Members
	///
	/// - `.0`: slice handle to the elements containing the domain
	///
	/// # Behavior
	///
	/// This variant is produced when the all elements in the domain are fully
	/// populated.
	Spanning(&'a [T]),
}

impl<'a, T> BitDomain<'a, T>
where T: 'a + BitStore {
	/// Tests if a domain fully spans its underlying memory slab.
	///
	/// Certain slice operations can be optimized to use element operations, but
	/// this requires that there are no partial edges. As such, detection of a
	/// `Spanning` domain is needed to take the fast path.
	///
	/// # Parameters
	///
	/// - `&self`: Some domain descriptor produced from a `BitPtr`.
	///
	/// # Returns
	///
	/// `true` if `self` is the `Spanning` variant; `false` otherwise.
	pub fn is_spanning(&self) -> bool {
		match self {
			BitDomain::Spanning(_) => true,
			_ => false,
		}
	}
}

impl<'a, T> From<BitDomainMut<'a, T>> for BitDomain<'a, T>
where T: 'a + BitStore {
	fn from(source: BitDomainMut<'a, T>) -> Self {
		use BitDomainMut as Bdm;
		use BitDomain as Bd;
		match source {
			Bdm::Empty => Bd::Empty,
			Bdm::Minor(hc, e, tc) => Bd::Minor(hc, e.base(), tc),
			Bdm::Major(hc, h, b, t, tc) => Bd::Major(
				hc,
				h.base(),
				&b[..],
				t.base(),
				tc,
			),
			Bdm::PartialHead(hc, h, t) => Bd::PartialHead(hc, h.base(), &t[..]),
			Bdm::PartialTail(h, t, tc) => Bd::PartialTail(&h[..], t.base(), tc),
			Bdm::Spanning(b) => Bd::Spanning(&b[..]),
		}
	}
}

impl<'a, T> From<BitPtr<T>> for BitDomain<'a, T>
where T: 'a + BitStore {
	fn from(bitptr: BitPtr<T>) -> Self {
		BitDomainMut::from(bitptr).into()
	}
}

/** Representations of the state of the bit domain in its containing elements.

# Lifetimes

- `'a`: Lifetime of the containing storage

# Type Parameters

- `T` The type of the elements the domain inhabits.
**/
#[derive(Debug)]
pub enum BitDomainMut<'a, T>
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
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	/// - `.2` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain is contained entirely inside
	/// one element, and does not reach to either edge.
	Minor(BitIdx<T>, &'a T::Nucleus, TailIdx<T>),
	/// Multpile element domain which does not reach the edge of its edge
	/// elements.
	///
	/// # Members
	///
	/// - `.0`: index of the first live domain bit in the first element
	/// - `.1`: immutable reference to the partial head edge element
	/// - `.2`: mutable slice handle to the fully-live elements in the interior.
	///   This may be empty.
	/// - `.3`: immutable reference to the partial tail edge element
	/// - `.4`: index of the first dead bit after the domain
	///
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	/// - `.4` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain uses at least two elements, and
	/// reaches neither the head edge of the head element nor the tail edge of
	/// the tail element.
	Major(
		BitIdx<T>,
		&'a T::Nucleus,
		&'a mut [T],
		&'a T::Nucleus,
		TailIdx<T>,
	),
	/// Domain with a partial head cursor and fully extended tail cursor.
	///
	/// # Members
	///
	/// - `.0`: index of the first live bit in the head element
	/// - `.1`: immutable reference to the partial head element
	/// - `.2`: mutable reference to the full elements of the domain. This may
	///   be empty.
	///
	/// # Invariants
	///
	/// - `.0` must be a valid index for `T` (`0 .. T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is past `0`, and
	/// its tail cursor is exactly `T::BITS`.
	PartialHead(BitIdx<T>, &'a T::Nucleus, &'a mut [T]),
	/// Domain with a fully extended head cursor and partial tail cursor.
	///
	/// # Members
	///
	/// - `.0`: mutable reference to the full elements of the domain. This may
	///   be empty.
	/// - `.1`: immutable reference to the partial tail element
	/// - `.2`: index of the first dead bit after the live bits in the tail
	///
	/// # Invariants
	///
	/// - `.2` must be a valid tail index for `T` (`1 ..= T::BITS`)
	///
	/// # Behavior
	///
	/// This variant is produced when the domain’s head cursor is exactly `0`,
	/// and its tail cursor is less than `T::BITS`.
	PartialTail(&'a mut [T], &'a T::Nucleus, TailIdx<T>),
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
	Spanning(&'a mut [T]),
}

impl<'a, T> From<BitPtr<T>> for BitDomainMut<'a, T>
where T: 'a + BitStore {
	fn from(bitptr: BitPtr<T>) -> Self {
		use BitDomainKind as Bdk;
		let (h, t) = (bitptr.head(), bitptr.tail());
		let data = bitptr.as_cell_slice();

		match bitptr.domain_kind() {
			Bdk::Empty => BitDomainMut::Empty,
			Bdk::Minor => BitDomainMut::Minor(h, &data[0], t),
			Bdk::Major => {
				let (head, body) = data
					.split_first()
					.expect("Major cannot fail to split head");
				let (tail, body) = body
					.split_last()
					.expect("Major cannot fail to split tail");
				let body = unsafe { BitAccess::base_slice_mut(body) };
				BitDomainMut::Major(h, head, body, tail, t)
			},
			Bdk::PartialHead => {
				let (head, tail) = data
					.split_first()
					.expect("PartialHead cannot fail to split");
				let tail = unsafe { BitAccess::base_slice_mut(tail) };
				BitDomainMut::PartialHead(h, head, tail)
			},
			Bdk::PartialTail => {
				let (tail, head) = data
					.split_last()
					.expect("PartialTail cannot fail to split");
				let head = unsafe { BitAccess::base_slice_mut(head) };
				BitDomainMut::PartialTail(head, tail, t)
			},
			Bdk::Spanning => BitDomainMut::Spanning(bitptr.as_mut_slice()),
		}
	}
}

#[cfg(all(test, feature = "testing"))]
mod tests {
	use super::*;
	use crate::store::IntoBitIdx;

	#[test]
	fn minor() {
		let data: u8 = 0u8;
		let bp = BitPtr::new(&data, 1.idx(), 6);

		assert_eq!(bp.domain_kind(), BitDomainKind::Minor);
	}

	#[test]
	fn major() {
		let data: &[u16] = &[0u16, !0u16];
		let bp = BitPtr::new(&data[0], 1.idx(), 28);

		assert_eq!(bp.domain_kind(), BitDomainKind::Major);
	}

	#[test]
	fn partial_head() {
		let data: u32 = 0u32;
		let bp = BitPtr::new(&data, 4.idx(), 28);

		assert_eq!(bp.domain_kind(), BitDomainKind::PartialHead);

		let data: &[u32] = &[0u32, !0u32];
		let bp = BitPtr::new(&data[0], 4.idx(), 60);

		assert_eq!(bp.domain_kind(), BitDomainKind::PartialHead);
	}

	#[test]
	fn partial_tail() {
		let data: u64 = 0u64;
		let bp = BitPtr::new(&data, 0.idx(), 60);

		assert_eq!(bp.domain_kind(), BitDomainKind::PartialTail);

		let data: &[u64] = &[0u64, !0u64];
		let bp = BitPtr::new(&data[0], 0.idx(), 124);

		assert_eq!(bp.domain_kind(), BitDomainKind::PartialTail);
	}

	#[test]
	fn spanning() {
		let data: u8 = 0u8;
		let bp = BitPtr::new(&data, 0.idx(), 8);

		assert_eq!(bp.domain_kind(), BitDomainKind::Spanning);

		let data: &[u16] = &[0u16, !0u16];
		let bp = BitPtr::new(&data[0], 0.idx(), 32);

		assert_eq!(bp.domain_kind(), BitDomainKind::Spanning);
	}
}
