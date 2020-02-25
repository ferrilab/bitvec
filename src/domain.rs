/*! Data Model for Bit Sequence Domains

The domains governed by `BitSlice` and owned-variant handles have different
representative states depending on the span of governed elements and live bits.

This module provides representations of the domain states for ease of use by
handle operations.
!*/

use crate::{
	access::BitAccess,
	index::{
		BitIdx,
		BitTail,
	},
	mem::BitMemory,
	order::BitOrder,
	slice::BitSlice,
	store::BitStore,
};

use core::{
	fmt::{
		self,
		Binary,
		Debug,
		Formatter,
		LowerHex,
		Octal,
		UpperHex,
	},
	iter::FusedIterator,
};

/** Representations of the state of the bit domain in its containing elements.

`BitSlice` regions can be described in terms of maybe-aliased and
known-unaliased sub-regions. This type produces correctly-marked subslices of a
source slice, according to information contained in its pointer.

# Lifetimes

- `'a`: Lifetime of the containing storage

# Type Parameters

- `O`: The ordering type of the parent `BitSlice`.
- `T`: The storage type of the parent `BitSlice`.
**/
#[derive(Debug)]
pub enum BitDomain<'a, O, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	/// A `BitSlice` region contained entirely within the interior of one
	/// element.
	Enclave {
		/// The index at which the slice region begins.
		head: BitIdx<T::Mem>,
		/// The original slice, marked as aliased.
		body: &'a BitSlice<O, T::Alias>,
		/// The index at which the slice region ends.
		tail: BitTail<T::Mem>,
	},
	/// A `BitSlice` region that touches at least one element edge.
	Region {
		/// The subslice that partially-fills the lowest element in the region.
		head: &'a BitSlice<O, T::Alias>,
		/// The subslice that wholly-fills elements, precluding any other handle
		/// from aliasing them.
		body: &'a BitSlice<O, T::NoAlias>,
		/// The subslice that partially-fills the highest element in the region.
		tail: &'a BitSlice<O, T::Alias>,
	},
}

impl<'a, O, T> BitDomain<'a, O, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	/// Constructs a domain over an empty slice.
	///
	/// # Returns
	///
	/// A `BitDomain::Region` with all subslices set to the empty slice.
	fn empty() -> Self {
		BitDomain::Region {
			head: BitSlice::empty(),
			body: BitSlice::empty(),
			tail: BitSlice::empty(),
		}
	}

	/// Constructs a domain with partial elements on both edges.
	///
	/// # Parameters
	///
	/// - `head`: The element index at which the slice begins.
	/// - `slice`: The original `BitSlice` being split.
	/// - `tail`: The element index at which the slice ends.
	///
	/// # Returns
	///
	/// A `BitDomain::Region` with its `head` section set to the live bits in
	/// the low element, its `body` section set to the live bits in the
	/// wholly-filled interior elements, and its `tail` section set to the live
	/// bits in the high element.
	fn major(
		head: BitIdx<T::Mem>,
		slice: &BitSlice<O, T>,
		tail: BitTail<T::Mem>,
	) -> Self
	{
		unsafe {
			let (head, rest) =
				slice.split_at_unchecked((T::Mem::BITS - *head) as usize);
			let (body, tail) =
				rest.split_at_unchecked(rest.len() - (*tail as usize));
			BitDomain::Region {
				head: &*(head as *const BitSlice<O, T>
					as *const BitSlice<O, T::Alias>),
				body: &*(body as *const BitSlice<O, T>
					as *const BitSlice<O, T::NoAlias>),
				tail: &*(tail as *const BitSlice<O, T>
					as *const BitSlice<O, T::Alias>),
			}
		}
	}

	/// Constructs a domain wholly within a single element.
	///
	/// # Parameters
	///
	/// - `head`: The element index at which the slice begins.
	/// - `slice`: The source slice.
	/// - `tail`: The element index at which the slice ends.
	///
	/// # Returns
	///
	/// A `BitDomain::Enclave` that marks the source slice as aliased, and
	/// carries the `head` and `tail` indices for mask construction.
	fn minor(
		head: BitIdx<T::Mem>,
		slice: &BitSlice<O, T>,
		tail: BitTail<T::Mem>,
	) -> Self
	{
		BitDomain::Enclave {
			head,
			body: unsafe {
				&*(slice as *const BitSlice<O, T>
					as *const BitSlice<O, T::Alias>)
			},
			tail,
		}
	}

	fn partial_head(head: BitIdx<T::Mem>, slice: &BitSlice<O, T>) -> Self {
		unsafe {
			let (head, rest) =
				slice.split_at_unchecked((T::Mem::BITS - *head) as usize);
			BitDomain::Region {
				head: &*(head as *const BitSlice<O, T>
					as *const BitSlice<O, T::Alias>),
				body: &*(rest as *const BitSlice<O, T>
					as *const BitSlice<O, T::NoAlias>),
				tail: BitSlice::empty(),
			}
		}
	}

	fn partial_tail(slice: &BitSlice<O, T>, tail: BitTail<T::Mem>) -> Self {
		unsafe {
			let (rest, tail) =
				slice.split_at_unchecked(slice.len() - (*tail as usize));
			BitDomain::Region {
				head: BitSlice::empty(),
				body: &*(rest as *const BitSlice<O, T>
					as *const BitSlice<O, T::NoAlias>),
				tail: &*(tail as *const BitSlice<O, T>
					as *const BitSlice<O, T::Alias>),
			}
		}
	}

	fn spanning(slice: &'a BitSlice<O, T>) -> Self {
		BitDomain::Region {
			head: BitSlice::empty(),
			body: unsafe {
				&*(slice as *const BitSlice<O, T>
					as *const BitSlice<O, T::NoAlias>)
			},
			tail: BitSlice::empty(),
		}
	}
}

impl<'a, O, T> From<&'a BitSlice<O, T>> for BitDomain<'a, O, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	fn from(this: &'a BitSlice<O, T>) -> Self {
		let bitptr = this.bitptr();
		let h = bitptr.head();
		let (e, t) = h.span(bitptr.len());
		let w = T::Mem::BITS;

		match (*h, e, *t) {
			//  Empty.
			(_, 0, _) => Self::empty(),
			//  Reaches both edges, for any number of elements.
			(0, _, t) if t == w => Self::spanning(this),
			//  Reaches only the tail edge, for any number of elements.
			(_, _, t) if t == w => Self::partial_head(h, this),
			//  Reaches only the head edge, for any number of elements.
			(0, ..) => Self::partial_tail(this, t),
			//  Reaches neither edge, for only one element.
			(_, 1, _) => Self::minor(h, this, t),
			//  Reaches neither edge, for multiple elements.
			(..) => Self::major(h, this, t),
		}
	}
}

pub enum BitDomainMut<'a, O, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	Enclave {
		head: BitIdx<T::Mem>,
		body: &'a mut BitSlice<O, T::Alias>,
		tail: BitTail<T::Mem>,
	},
	Region {
		head: &'a mut BitSlice<O, T::Alias>,
		body: &'a mut BitSlice<O, T::NoAlias>,
		tail: &'a mut BitSlice<O, T::Alias>,
	},
}

impl<'a, O, T> From<&'a mut BitSlice<O, T>> for BitDomainMut<'a, O, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	fn from(this: &'a mut BitSlice<O, T>) -> Self {
		match (&*this).into() {
			BitDomain::Enclave { head, body, tail } => BitDomainMut::Enclave {
				head,
				body: body.bitptr().into_bitslice_mut(),
				tail,
			},
			BitDomain::Region { head, body, tail } => BitDomainMut::Region {
				head: head.bitptr().into_bitslice_mut(),
				body: body.bitptr().into_bitslice_mut(),
				tail: tail.bitptr().into_bitslice_mut(),
			},
		}
	}
}

/** Representations of the raw memory domain for a `BitSlice`.

This structure is produced by [`BitSlice::domain`], and describes the region of
memory the `BitSlice` covers in terms of its raw memory elements, rather than
its bits.

The aliased references contained in this structure permit the mutation of memory
observed by other immutable `&BitSlice` handles. You are responsible for
maintaining memory correctness by not using mutating methods on these
references.

# `[T::Mem]` replacement

As it is unsafe to produce a reference to raw memory, due to runtime alias
conditions, this type also functions as a replacement for a slice view of the
backing memory. It is capable of iterating over the values of the memory store,
and implements the [`core::fmt`] traits to render the backing store.

[`BitSlice::domain`]: ../slice/struct.BitSlice.html#method.domain
[`core::fmt`]: //doc.rust-lang.org/corce/fmt
**/
pub enum Domain<'a, T>
where T: 'a + BitStore
{
	/// The source `BitSlice` region is in the interior of one element.
	Enclave {
		/// Index, according to the `BitSlice`’s `BitOrder` parameter, at which
		/// the slice begins.
		head: BitIdx<T::Mem>,
		/// The memory address of the element containing the `BitSlice`.
		elem: &'a T::Alias,
		/// Index, according to the `BitSlice`’s `BitOrder` parameter, at which
		/// the slice ends.
		tail: BitTail<T::Mem>,
	},
	/// The source `BitSlice` region touches at least one edge of an element.
	Region {
		/// If the first element is partially-filled, its address and starting
		/// bit index according to the `BitOrder` parameter.
		head: Option<(BitIdx<T::Mem>, &'a T::Alias)>,
		/// Any fully-spanned elements in the source `BitSlice`.
		body: &'a [T::NoAlias],
		/// If the last element is partially-filled, its address and ending bit
		/// index according to the `BitOrder` parameter.
		tail: Option<(&'a T::Alias, BitTail<T::Mem>)>,
	},
}

impl<'a, T> Domain<'a, T>
where T: 'a + BitStore
{
	/// Produces an iterator over each memory value referenced by the domain.
	///
	/// This iterator will perform the appropriate load on each reference
	/// element, yielding the value of the referenced memory.
	///
	/// # Parameters
	///
	/// - `&self`
	///
	/// # Returns
	///
	/// An iterator yielding each referent value.
	pub fn iter(&self) -> DomainIter<'a, T> {
		DomainIter { domain: *self }
	}

	pub(crate) fn is_spanning(&self) -> bool {
		match self {
			Domain::Region {
				head: None,
				tail: None,
				..
			} => true,
			_ => false,
		}
	}

	fn empty() -> Self {
		Domain::Region {
			head: None,
			body: &[],
			tail: None,
		}
	}

	fn major(
		head: BitIdx<T::Mem>,
		elts: &'a [T::Alias],
		tail: BitTail<T::Mem>,
	) -> Self
	{
		let (first, rest) = elts
			.split_first()
			.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
		let (last, body) = rest
			.split_last()
			.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
		Domain::Region {
			head: Some((head, first)),
			body: unsafe {
				&*(body as *const [T::Alias] as *const [T::NoAlias])
			},
			tail: Some((last, tail)),
		}
	}

	fn minor(
		head: BitIdx<T::Mem>,
		elts: &'a [T::Alias],
		tail: BitTail<T::Mem>,
	) -> Self
	{
		Domain::Enclave {
			head,
			elem: unsafe { elts.get_unchecked(0) },
			tail,
		}
	}

	fn partial_head(head: BitIdx<T::Mem>, elts: &'a [T::Alias]) -> Self {
		let (first, rest) = elts
			.split_first()
			.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
		Domain::Region {
			head: Some((head, first)),
			body: unsafe {
				&*(rest as *const [T::Alias] as *const [T::NoAlias])
			},
			tail: None,
		}
	}

	fn partial_tail(elts: &'a [T::Alias], tail: BitTail<T::Mem>) -> Self {
		let (last, rest) = elts
			.split_last()
			.unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
		Domain::Region {
			head: None,
			body: unsafe {
				&*(rest as *const [T::Alias] as *const [T::NoAlias])
			},
			tail: Some((last, tail)),
		}
	}

	fn spanning(elts: &[T::Alias]) -> Self {
		Domain::Region {
			head: None,
			body: unsafe {
				&*(elts as *const [T::Alias] as *const [T::NoAlias])
			},
			tail: None,
		}
	}
}

impl<T> Clone for Domain<'_, T>
where T: BitStore
{
	fn clone(&self) -> Self {
		match self {
			Domain::Enclave { head, elem, tail } => Domain::Enclave {
				head: *head,
				elem,
				tail: *tail,
			},
			Domain::Region { head, body, tail } => Domain::Region {
				head: *head,
				body,
				tail: *tail,
			},
		}
	}
}

impl<'a, O, T> From<&'a BitSlice<O, T::Alias>> for Domain<'a, T>
where
	O: BitOrder,
	T: 'a + BitStore,
{
	fn from(this: &'a BitSlice<O, T::Alias>) -> Self {
		let bitptr = unsafe { BitSlice::<O, T>::unalias(this) }.bitptr();
		let h = bitptr.head();
		let (e, t) = h.span(bitptr.len());
		let w = T::Mem::BITS;
		let elts = bitptr.aliased_slice();

		match (*h, e, *t) {
			//  Empty.
			(_, 0, _) => Self::empty(),
			//  Reaches both edges, for any number of elements.
			(0, _, t) if t == w => Self::spanning(elts),
			//  Reaches only the tail edge, for any number of elements.
			(_, _, t) if t == w => Self::partial_head(h, elts),
			//  Reaches only the head edge, for any number of elements.
			(0, ..) => Self::partial_tail(elts, t),
			//  Reaches neither edge, for only one element.
			(_, 1, _) => Self::minor(h, elts, t),
			//  Reaches neither edge, for multiple elements.
			(..) => Self::major(h, elts, t),
		}
	}
}

impl<T> Default for Domain<'_, T>
where T: BitStore
{
	fn default() -> Self {
		Self::empty()
	}
}

impl<T> Binary for Domain<'_, T>
where
	T: BitStore,
	T::Mem: Binary,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		struct BinVal<M: BitMemory>(M);
		impl<M: BitMemory> Debug for BinVal<M> {
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				Binary::fmt(&self.0, fmt)
			}
		}

		fmt.debug_list().entries(self.iter().map(BinVal)).finish()
	}
}

impl<T> Debug for Domain<'_, T>
where
	T: BitStore,
	T::Mem: Debug,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		fmt.debug_list().entries(self.iter()).finish()
	}
}

impl<T> LowerHex for Domain<'_, T>
where
	T: BitStore,
	T::Mem: LowerHex,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		struct HexVal<M: BitMemory>(M);
		impl<M: BitMemory> Debug for HexVal<M> {
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				LowerHex::fmt(&self.0, fmt)
			}
		}

		fmt.debug_list().entries(self.iter().map(HexVal)).finish()
	}
}

impl<T> Octal for Domain<'_, T>
where
	T: BitStore,
	T::Mem: Octal,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		struct OctVal<M: BitMemory>(M);
		impl<M: BitMemory> Debug for OctVal<M> {
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				Octal::fmt(&self.0, fmt)
			}
		}

		fmt.debug_list().entries(self.iter().map(OctVal)).finish()
	}
}

impl<T> UpperHex for Domain<'_, T>
where
	T: BitStore,
	T::Mem: UpperHex,
{
	fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
		struct HexVal<M: BitMemory>(M);
		impl<M: BitMemory> Debug for HexVal<M> {
			fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
				UpperHex::fmt(&self.0, fmt)
			}
		}

		fmt.debug_list().entries(self.iter().map(HexVal)).finish()
	}
}

impl<'a, T> IntoIterator for Domain<'a, T>
where T: 'a + BitStore
{
	type IntoIter = DomainIter<'a, T>;
	type Item = <Self::IntoIter as Iterator>::Item;

	fn into_iter(self) -> Self::IntoIter {
		DomainIter { domain: self }
	}
}

impl<T> Copy for Domain<'_, T> where T: BitStore
{
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DomainIter<'a, T>
where T: 'a + BitStore
{
	domain: Domain<'a, T>,
}

impl<'a, T> Iterator for DomainIter<'a, T>
where T: 'a + BitStore
{
	type Item = T::Mem;

	fn next(&mut self) -> Option<Self::Item> {
		match self.domain {
			Domain::Enclave { elem, .. } => {
				let out = elem.load();
				self.domain = Domain::empty();
				Some(out)
			},
			Domain::Region {
				ref mut head,
				ref mut body,
				ref mut tail,
			} => {
				if let Some((_, h)) = head {
					let out = h.load();
					*head = None;
					return Some(out);
				}
				if let Some((out, rest)) = body.split_first() {
					*body = rest;
					return Some(out.load());
				}
				if let Some((t, _)) = tail {
					let out = t.load();
					*tail = None;
					return Some(out);
				}
				None
			},
		}
	}
}

impl<T> ExactSizeIterator for DomainIter<'_, T>
where T: BitStore
{
	fn len(&self) -> usize {
		match self.domain {
			Domain::Enclave { .. } => 1,
			Domain::Region { head, body, tail } => {
				head.is_some() as usize + body.len() + tail.is_some() as usize
			},
		}
	}
}

impl<T> FusedIterator for DomainIter<'_, T> where T: BitStore
{
}

impl<'a, T> DoubleEndedIterator for DomainIter<'a, T>
where T: 'a + BitStore
{
	fn next_back(&mut self) -> Option<Self::Item> {
		match self.domain {
			Domain::Enclave { elem, .. } => {
				let out = elem.load();
				self.domain = Domain::empty();
				Some(out)
			},
			Domain::Region {
				ref mut head,
				ref mut body,
				ref mut tail,
			} => {
				if let Some((t, _)) = tail {
					let out = t.load();
					*tail = None;
					return Some(out);
				}
				if let Some((out, rest)) = body.split_last() {
					*body = rest;
					return Some(out.load());
				}
				if let Some((_, h)) = head {
					let out = h.load();
					*head = None;
					return Some(out);
				}
				None
			},
		}
	}
}
