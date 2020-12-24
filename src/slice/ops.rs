//! Port of the `[T]` operator implementations.

use crate::{
	access::BitAccess,
	devel as dvl,
	domain::DomainMut,
	field::BitField,
	iter::BitIter,
	mem::BitMemory,
	order::{
		BitOrder,
		Lsb0,
		Msb0,
	},
	slice::{
		BitSlice,
		BitSliceIndex,
	},
	store::BitStore,
};

use core::{
	iter,
	ops::{
		BitAnd,
		BitAndAssign,
		BitOr,
		BitOrAssign,
		BitXor,
		BitXorAssign,
		Index,
		IndexMut,
		Not,
		Range,
		RangeFrom,
		RangeFull,
		RangeInclusive,
		RangeTo,
		RangeToInclusive,
	},
};

const WORD: usize = <usize as BitMemory>::BITS as usize;

macro_rules! bitop {
	( $(
		$trait_assign:ident :: $func_assign:ident, $trait:ident :: $func:ident;
	)+ ) => { $(
		impl<'a, O1, O2, T1, T2> $trait_assign <&'a BitSlice<O2, T2>>
		for BitSlice<O1, T1>
		where
			O1: BitOrder,
			O2: BitOrder,
			T1: BitStore,
			T2: BitStore,
		{
			fn $func_assign (&mut self, mut rhs: &'a BitSlice<O2, T2>) {
				let mut lhs = self;
				if dvl::match_types::<O1, T1::Mem, O2, T2::Mem>() {
					if dvl::match_order::<O1, Lsb0>() {
						unsafe {
							let this = &mut *cast_order_mut::<O1, Lsb0, T1>(lhs);
							let that = &*cast_order::<O2, Lsb0, T2>(rhs);
							let (this, that) = sp_binop(this, that, $trait :: $func);
							lhs = &mut *cast_order_mut::<Lsb0, O1, T1>(this);
							rhs = &*cast_order::<Lsb0, O2, T2>(that);
						}
					}
					if dvl::match_order::<O1, Msb0>() {
						unsafe {
							let this = &mut *cast_order_mut::<O1, Msb0, T1>(lhs);
							let that = &*cast_order::<O2, Msb0, T2>(rhs);
							let (this, that) = sp_binop(this, that, $trait :: $func);
							lhs = &mut *cast_order_mut::<Msb0, O1, T1>(this);
							rhs = &*cast_order::<Msb0, O2, T2>(that);
						}
					}
				}
				for (ptr, bit) in lhs.as_mut_bitptr_range().zip(
					rhs.into_iter().by_val().chain(iter::repeat(false))
				) {
					unsafe { ptr.write($trait :: $func(ptr.read(), bit)); }
				}
			}
		}

		impl<O, T, I> $trait_assign <BitIter<I>> for BitSlice<O, T>
		where
			O: BitOrder,
			T: BitStore,
			I: Iterator<Item = bool>,
		{
			#[inline]
			fn $func_assign (&mut self, mut rhs: BitIter<I>) {
				self.for_each(|_, bit|
					$trait :: $func (bit, rhs.next().unwrap_or(false))
				);
			}
		}
	)+ };
}

bitop! {
	BitAndAssign::bitand_assign, BitAnd::bitand;
	BitOrAssign::bitor_assign, BitOr::bitor;
	BitXorAssign::bitxor_assign, BitXor::bitxor;
}

impl<O, T> Index<usize> for BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Output = bool;

	/// Looks up a single bit by semantic index.
	///
	/// # Examples
	///
	/// ```rust
	/// use bitvec::prelude::*;
	///
	/// let bits = bits![Msb0, u8; 0, 1, 0];
	/// assert!(!bits[0]); // -----^  |  |
	/// assert!( bits[1]); // --------^  |
	/// assert!(!bits[2]); // -----------^
	/// ```
	///
	/// If the index is greater than or equal to the length, indexing will
	/// panic.
	///
	/// The below test will panic when accessing index 1, as only index 0 is
	/// valid.
	///
	/// ```rust,should_panic
	/// use bitvec::prelude::*;
	///
	/// let bits = bits![0,  ];
	/// bits[1]; // --------^
	/// ```
	fn index(&self, index: usize) -> &Self::Output {
		//  Convert the `BitRef` to `&'static bool`
		match *index.index(self) {
			true => &true,
			false => &false,
		}
	}
}

/// Generate `Index`/`Mut` implementations for subslicing.
macro_rules! index {
	($($t:ty),+ $(,)?) => { $(
		impl<O, T> Index<$t> for BitSlice<O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			type Output = Self;

			fn index(&self, index: $t) -> &Self::Output {
				index.index(self)
			}
		}

		impl<O, T> IndexMut<$t> for BitSlice<O, T>
		where
			O: BitOrder,
			T: BitStore,
		{
			fn index_mut(&mut self, index: $t) -> &mut Self::Output {
				index.index_mut(self)
			}
		}
	)+ };
}

//  Implement `Index`/`Mut` subslicing with all the ranges.
index!(
	Range<usize>,
	RangeFrom<usize>,
	RangeFull,
	RangeInclusive<usize>,
	RangeTo<usize>,
	RangeToInclusive<usize>,
);

impl<'a, O, T> Not for &'a mut BitSlice<O, T>
where
	O: BitOrder,
	T: BitStore,
{
	type Output = Self;

	fn not(self) -> Self::Output {
		match self.domain_mut() {
			DomainMut::Enclave { head, elem, tail } => {
				elem.invert_bits(O::mask(head, tail));
			},
			DomainMut::Region { head, body, tail } => {
				if let Some((head, elem)) = head {
					elem.invert_bits(O::mask(head, None));
				}
				for elem in body {
					elem.store_value(!elem.load_value());
				}
				if let Some((elem, tail)) = tail {
					elem.invert_bits(O::mask(None, tail));
				}
			},
		}
		self
	}
}

unsafe fn cast_order<O1, O2, T>(
	this: *const BitSlice<O1, T>,
) -> *const BitSlice<O2, T>
where
	O1: BitOrder,
	O2: BitOrder,
	T: BitStore,
{
	this as *const _
}

unsafe fn cast_order_mut<O1, O2, T>(
	this: *mut BitSlice<O1, T>,
) -> *mut BitSlice<O2, T>
where
	O1: BitOrder,
	O2: BitOrder,
	T: BitStore,
{
	this as *mut _
}

/** Applies a bit-wise operator to slice contents in batch operations.

This uses `BitField` to load from and store into memory. The slices must have
compatible integer type parameters in order for this to be correct.

# Type Parameters

- `O`: The two slices must have a common bit-ordering.
- `T1`: Any storage parameter.
- `T2`: Any storage parameter. `T1::Mem` must be the same type as `T2::Mem`.

# Parameters

- `this`: A mutable slice handle, used as a source and destination of the
  arithmetic.
- `that`: An immutable slice handle, used as the other source of the arithmetic.
- `func`: A bulk operation to be performed on the contents of `*this` and
  `*that`, in processor-word batches.

# Effects

`func` is applied to each processor-word batch of slice contents, then written
back into `*this`.

# Returns

The returned values are subslices of `this` and `that`, describing only the
leftover memory regions not used by this function. Any bits remaining in these
regions will need to be processed individually.
**/
fn sp_binop<'a, O, T1, T2, F>(
	mut this: &'a mut BitSlice<O, T1>,
	mut that: &'a BitSlice<O, T2>,
	func: F,
) -> (&'a mut BitSlice<O, T1>, &'a BitSlice<O, T2>)
where
	O: BitOrder,
	T1: BitStore,
	T2: BitStore,
	F: Fn(usize, usize) -> usize,
	BitSlice<O, T1>: BitField,
	BitSlice<O, T2>: BitField,
{
	assert!(
		dvl::match_types::<O, T1::Mem, O, T2::Mem>(),
		"Cannot use `BitField` to accelerate bit-wise arithmetic between \
		 bit-slices of differing integer types",
	);
	while this.len() >= WORD && that.len() >= WORD {
		let (a, b) = unsafe { this.split_at_unchecked_mut_noalias(WORD) };
		let (c, d) = unsafe { that.split_at_unchecked(WORD) };
		let (e, f) = (a.load(), c.load());
		a.store(func(e, f));
		this = b;
		that = d;
	}
	(this, that)
}
