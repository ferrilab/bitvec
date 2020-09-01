/*! Ordering of bits within register elements.

`bitvec` structures are parametric over any ordering of bits within an element.
The `BitOrder` trait maps a cursor position (indicated by the `BitIdx` type) to an
electrical position (indicated by the `BitPos` type) within that element, and
also defines the order of traversal over an element.

The only requirement on implementors of `BitOrder` is that the transform function
from cursor (`BitIdx`) to position (`BitPos`) is *total* (every integer in the
domain `0 .. T::BITS` is used) and *unique* (each cursor maps to one and only
one position, and each position is mapped by one and only one cursor).
Contiguity is not required.

`BitOrder` is a stateless trait, and implementors should be zero-sized types.
!*/

use crate::{
	index::{
		BitIdx,
		BitMask,
		BitPos,
		BitSel,
		BitTail,
	},
	mem::BitMemory,
};

/** An ordering over an element.

# Usage

`bitvec` structures store and operate on semantic counts, not bit positions. The
`BitOrder::at` function takes a semantic ordering, `BitIdx`, and produces an
electrical position, `BitPos`.

# Safety

If your implementation violates any of the requirements on these functions, then
the program will become incorrect and have unspecified behavior. The best-case
scenario is that operations relying on your implementation will crash the
program; the worst-case is that memory access will silently become corrupt.

You are responsible for adhering to the requirements of these functions. In the
future, a verification function may be provided for your test suite; however, it
is not yet possible to verify your implementation at compile-time.

This is an `unsafe trait` to implement, because you are responsible for
upholding the state requirements. The types you manipulate have `unsafe fn`
constructors, because they require you to maintain correct and consistent
processes in order for the rest of the library to use them.

The implementations of `BitOrder` are trusted to drive safe code, and once data
leaves a `BitOrder` implementation, it is considered safe to use as the basis
for interaction with memory.

# Verification

Rust currently lacks Zig’s compile-time computation capability. This means that
`bitvec` cannot fail a compile if it detects that a `BitOrder` implementation is
invalid and breaks the stated requirements. `bitvec` does offer a function,
[`verify`], which ensures the correctness of an implementation. When Rust gains
the capability to run this function in generic `const` contexts, `bitvec` will
use it to prevent at compile-time the construction of data structures that use
incorrect ordering implementations.

The verifier function panics when it detects invalid behavior, with an error
message intended to clearly indicate the broken requirement.

```rust
use bitvec::{
  index::{BitIdx, BitPos},
  mem::BitMemory,
  order::{self, BitOrder},
};
# use bitvec::{index::*, order::Lsb0};

pub struct Custom;
unsafe impl BitOrder for Custom {
  fn at<M: BitMemory>(idx: BitIdx<M>) -> BitPos<M> {
  // impl
  # return Lsb0::at::<M>(idx);
  }
}

#[test]
#[cfg(test)]
fn prove_custom() {
  order::verify::<Custom>();
}
```

[`verify`]: fn.verify.html
**/
pub unsafe trait BitOrder {
	/// Converts a semantic bit index into an electrical bit position.
	///
	/// This function is the basis of the trait, and must adhere to a number of
	/// requirements in order for an implementation to be considered correct.
	///
	/// # Parameters
	///
	/// - `index`: The semantic index of a bit within an element `M`.
	///
	/// # Returns
	///
	/// The electrical position of the indexed bit within an element `M`. See
	/// the `BitPos` documentation for what electrical positions are considered
	/// to mean.
	///
	/// # Type Parameters
	///
	/// - `M`: The element type which the index and position describe.
	///
	/// # Requirements
	///
	/// This function must satisfy the following requirements for all possible
	/// input and output values for all possible type parameters:
	///
	/// ## Totality
	///
	/// This function must be able to accept every input in the `BitIdx<M>`
	/// value range, and produce a corresponding `BitPos<M>`. It must not abort
	/// the program or return an invalid `BitPos<M>` for any input value in the
	/// `BitIdx<M>` range.
	///
	/// ## Bijection
	///
	/// There must be an exactly one-to-one correspondence between input value
	/// and output value. No input index may select from a set of more than one
	/// output position, and no output position may be produced by more than one
	/// input index.
	///
	/// ## Purity
	///
	/// The translation from index to position must be consistent for the
	/// lifetime of the program. This function *may* refer to global state, but
	/// that state **must** be immutable for the program lifetime, and must not
	/// be used to violate the totality or bijection requirements.
	///
	/// ## Output Validity
	///
	/// The produced `BitPos<M>` must be within the valid range of that type.
	/// Call sites of this function will not take any steps to constrain the
	/// output value. If you use `unsafe` code to produce an invalid
	/// `BitPos<M>`, the program is permanently incorrect, and will likely
	/// crash.
	///
	/// # Usage
	///
	/// This function will only ever be called with input values in the valid
	/// `BitIdx<M>` range. Implementors are not required to consider any values
	/// outside this range in their function body.
	fn at<M>(index: BitIdx<M>) -> BitPos<M>
	where M: BitMemory;

	/// Converts a semantic bit index into a one-hot selector mask.
	///
	/// This is an optional function; a default implementation is provided for
	/// you.
	///
	/// The default implementation of this function calls `Self::at` to produce
	/// an electrical position, then turns that into a selector mask by setting
	/// the `n`th bit more significant than the least significant bit of the
	/// element. `BitOrder` implementations may choose to provide a faster mask
	/// production here, but they must satisfy the requirements listed below.
	///
	/// # Parameters
	///
	/// - `index`: The semantic index of a bit within an element `M`.
	///
	/// # Returns
	///
	/// A one-hot selector mask for the bit indicated by the index value.
	///
	/// # Type Parameters
	///
	/// - `M`: The storage type for which the mask will be calculated. The mask
	///   must also be this type, as it will be applied to an element of `M` in
	///   order to set, clear, or test a single bit.
	///
	/// # Requirements
	///
	/// A one-hot encoding means that there is exactly one bit set in the
	/// produced value. It must be equivalent to `1 << Self::at::<M>(place)`.
	///
	/// As with `at`, this function must produce a unique mapping from each
	/// legal index in the `M` domain to a one-hot value of `M`.
	#[inline]
	fn select<M>(index: BitIdx<M>) -> BitSel<M>
	where M: BitMemory {
		Self::at::<M>(index).select()
	}

	/// Constructs a multi-bit selector mask for batch operations on a single
	/// memory element `M`.
	///
	/// The default implementation of this function traverses the index range,
	/// converting each index into a single-bit selector with `Self::select` and
	/// accumulating into a combined register value.
	///
	/// # Parameters
	///
	/// - `from`: The inclusive starting index for the mask.
	/// - `upto`: The exclusive ending index for the mask.
	///
	/// # Returns
	///
	/// A bit-mask with all bits corresponding to the input index range set high
	/// and all others set low.
	///
	/// # Type Parameters
	///
	/// - `M`: The storage type for which the mask will be calculated. The mask
	///   must also be this type, as it will be applied to an element of `M` in
	///   order to set, clear, or test all the selected bits.
	///
	/// # Requirements
	///
	/// This function must always be equivalent to
	///
	/// ```rust,ignore
	/// (from .. upto)
	///   .map(1 << Self::at::<M>)
	///   .fold(0, |mask, sel| mask | sel)
	/// ```
	#[inline]
	fn mask<M>(
		from: impl Into<Option<BitIdx<M>>>,
		upto: impl Into<Option<BitTail<M>>>,
	) -> BitMask<M>
	where
		M: BitMemory,
	{
		let (from, upto) = match (from.into(), upto.into()) {
			(None, None) => return BitMask::ALL,
			(Some(from), None) => (from, BitTail::<M>::END),
			(None, Some(upto)) => (BitIdx::<M>::ZERO, upto),
			(Some(from), Some(upto)) => (from, upto),
		};
		BitIdx::<M>::range(from, upto).map(Self::select::<M>).sum()
	}
}

/// Traverses an element from `MSbit` to `LSbit`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Msb0;

unsafe impl BitOrder for Msb0 {
	#[cfg_attr(not(tarpaulin_include), inline(always))]
	fn at<M>(index: BitIdx<M>) -> BitPos<M>
	where M: BitMemory {
		unsafe { BitPos::new_unchecked(M::MASK - index.value()) }
	}

	#[cfg_attr(not(tarpaulin_include), inline(always))]
	fn select<M>(index: BitIdx<M>) -> BitSel<M>
	where M: BitMemory {
		/* Set the MSbit, then shift it down. The left expr is const-folded.
		Note: this is not equivalent to `1 << (mask - index)`, because that
		requires a runtime subtraction, but the expression below is only a
		single right-shift.
		*/
		unsafe { BitSel::new_unchecked((M::ONE << M::MASK) >> index.value()) }
	}

	#[inline]
	fn mask<M>(
		from: impl Into<Option<BitIdx<M>>>,
		upto: impl Into<Option<BitTail<M>>>,
	) -> BitMask<M>
	where
		M: BitMemory,
	{
		let from = from.into().unwrap_or(BitIdx::ZERO).value();
		let upto = upto.into().unwrap_or(BitTail::END).value();
		debug_assert!(upto >= from, "Ranges must run from low index to high");
		let ct = upto - from;
		if ct == M::BITS {
			return BitMask::ALL;
		}
		//  1. Set all bits high.
		//  2. Shift right by the number of bits in the mask. These are now low.
		//  3. Invert. The mask bits (at MSedge) are high; the rest are low.
		//  4. Shift right by the distance from MSedge.
		unsafe { BitMask::new(!(M::ALL >> ct) >> from) }
	}
}

/// Traverses an element from `LSbit` to `MSbit`.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lsb0;

unsafe impl BitOrder for Lsb0 {
	#[cfg_attr(not(tarpaulin), inline(always))]
	fn at<M>(index: BitIdx<M>) -> BitPos<M>
	where M: BitMemory {
		unsafe { BitPos::new_unchecked(index.value()) }
	}

	#[cfg_attr(not(tarpaulin), inline(always))]
	fn select<M>(index: BitIdx<M>) -> BitSel<M>
	where M: BitMemory {
		unsafe { BitSel::new_unchecked(M::ONE << index.value()) }
	}

	#[inline]
	fn mask<M>(
		from: impl Into<Option<BitIdx<M>>>,
		upto: impl Into<Option<BitTail<M>>>,
	) -> BitMask<M>
	where
		M: BitMemory,
	{
		let from = from.into().unwrap_or(BitIdx::ZERO).value();
		let upto = upto.into().unwrap_or(BitTail::END).value();
		debug_assert!(upto >= from, "Ranges must run from low index to high");
		let ct = upto - from;
		if ct == M::BITS {
			return BitMask::ALL;
		}
		//  1. Set all bits high.
		//  2. Shift left by the number of bits in the mask. These are now low.
		//  3. Invert. The mask bits at LSedge are high; the rest are low.
		//  4. Shift left by the distance from LSedge.
		unsafe { BitMask::new(!(M::ALL << ct) << from) }
	}
}

/** A default bit ordering.

Typically, your platform’s C compiler uses most-significant-bit-first ordering
for bitfields. The Msb0 bit ordering and big-endian byte ordering are otherwise
completely unrelated.
**/
#[cfg(target_endian = "big")]
pub type LocalBits = Msb0;

/** A default bit ordering.

Typically, your platform’s C compiler uses least-significant-bit-first ordering
for bitfields. The Lsb0 bit ordering and little-endian byte ordering are
otherwise completely unrelated.
**/
#[cfg(target_endian = "little")]
pub type LocalBits = Lsb0;

#[cfg(not(any(target_endian = "big", target_endian = "little")))]
compile_fail!(concat!(
	"This architecture is currently not supported. File an issue at ",
	env!(CARGO_PKG_REPOSITORY)
));

/** Verifies a `BitOrder` implementation’s adherence to the stated rules.

This function checks some `BitOrder` implementation’s behavior on each of the
`BitMemory` types it must handle, and reports any violation of the rules that it
detects.

# Type Parameters

- `O`: The `BitOrder` implementation to test.

# Parameters

- `verbose`: Sets whether the test should print diagnostic information to
  `stdout`.

# Panics

This panics if it detects any violation of the `BitOrder` implementation rules
for `O`.
**/
#[cfg(test)]
pub fn verify<O>(verbose: bool)
where O: BitOrder {
	verify_for_type::<O, u8>(verbose);
	verify_for_type::<O, u16>(verbose);
	verify_for_type::<O, u32>(verbose);
	verify_for_type::<O, usize>(verbose);

	#[cfg(target_pointer_width = "64")]
	verify_for_type::<O, u64>(verbose);
}

/** Verifies a `BitOrder` implementation’s adherence to the stated rules, for
one register type.

This function checks some `BitOrder` implementation against only one of the
`BitMemory` types that it will encounter. This is useful if you are implementing
an ordering that only needs to be concerned with a subset of the types, and you
know that you will never use it with the types it does not support.

# Type Parameters

- `O`: The `BitOrder` implementation to test.
- `M`: The `BitMemory` type  for which to test `O`.

# Parameters

- `verbose`: Sets whether the test should print diagnostic information to
  `stdout`.

# Panics

This panics if it detects any violation of the `BitOrder` implementation rules
for the combination of input types and index values.
**/
#[cfg(test)]
pub fn verify_for_type<O, M>(verbose: bool)
where
	O: BitOrder,
	M: BitMemory,
{
	use core::any::type_name;
	let mut accum = BitMask::<M>::ZERO;

	let oname = type_name::<O>();
	let mname = type_name::<M>();

	for n in 0 .. M::BITS {
		//  Wrap the counter as an index.
		let idx = unsafe { BitIdx::<M>::new_unchecked(n) };

		//  Compute the bit position for the index.
		let pos = O::at::<M>(idx);
		if verbose {
			#[cfg(feature = "std")]
			println!(
				"`<{} as BitOrder>::at::<{}>({})` produces {}",
				oname,
				mname,
				n,
				pos.value(),
			);
		}

		//  If the computed position exceeds the valid range, fail.
		assert!(
			pos.value() < M::BITS,
			"Error when verifying the implementation of `BitOrder` for `{}`: \
			 Index {} produces a bit position ({}) that exceeds the type width \
			 {}",
			oname,
			n,
			pos.value(),
			M::BITS,
		);

		//  Check `O`’s implementation of `select`
		let sel = O::select::<M>(idx);
		if verbose {
			#[cfg(feature = "std")]
			println!(
				"`<{} as BitOrder>::select::<{}>({})` produces {}",
				oname, mname, n, sel,
			);
		}

		//  If the selector bit is not one-hot, fail.
		assert_eq!(
			sel.value().count_ones(),
			1,
			"Error when verifying the implementation of `BitOrder` for `{}`: \
			 Index {} produces a bit selector ({}) that is not a one-hot mask",
			oname,
			n,
			sel,
		);

		//  Check that the selection computed from the index matches the
		//  selection computed from the position.
		let shl = pos.select();
		//  If `O::select(idx)` does not produce `1 << pos`, fail.
		assert_eq!(
			sel,
			shl,
			"Error when verifying the implementation of `BitOrder` for `{}`: \
			 Index {} produces a bit selector ({}) that is not equal to `1 << \
			 {}` ({})",
			oname,
			n,
			sel,
			pos.value(),
			shl,
		);

		//  Check that the produced selector bit has not already been added to
		//  the accumulator.
		assert!(
			!accum.test(sel),
			"Error when verifying the implementation of `BitOrder` for `{}`: \
			 Index {} produces a bit position ({}) that has already been \
			 produced by a prior index",
			oname,
			n,
			pos.value(),
		);
		accum.insert(sel);
		if verbose {
			#[cfg(feature = "std")]
			println!(
				"`<{} as BitOrder>::at::<{}>({})` accumulates  {}",
				oname, mname, n, accum,
			);
		}
	}

	//  Check that all indices produced all positions.
	assert_eq!(
		accum,
		BitMask::ALL,
		"Error when verifying the implementation of `BitOrder` for `{}`: The \
		 bit positions marked with a `0` here were never produced from an \
		 index, despite all possible indices being passed in for translation: \
		 {}",
		oname,
		accum,
	);

	//  Check that `O::mask` is correct for all range combinations.
	for from in BitIdx::<M>::range_all() {
		for upto in BitTail::<M>::range_from(from) {
			let mask = O::mask(from, upto);
			let check = BitIdx::<M>::range(from, upto)
				.map(O::at::<M>)
				.map(BitPos::<M>::select)
				.sum::<BitMask<M>>();
			assert_eq!(
				mask,
				check,
				"Error when verifying the implementation of `BitOrder` for \
				 `{o}`: `{o}::mask::<{m}>({f}, {u})` produced {bad}, but \
				 expected {good}",
				o = oname,
				m = mname,
				f = from,
				u = upto,
				bad = mask,
				good = check,
			);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn verify_impls() {
		verify::<Lsb0>(cfg!(feature = "testing"));
		verify::<Msb0>(cfg!(feature = "testing"));

		struct DefaultImpl;
		unsafe impl BitOrder for DefaultImpl {
			fn at<M>(index: BitIdx<M>) -> BitPos<M>
			where M: BitMemory {
				unsafe { BitPos::new_unchecked(index.value()) }
			}
		}

		verify::<DefaultImpl>(cfg!(feature = "testing"));
	}
}
