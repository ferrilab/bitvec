/*! Utility macros for constructing data structures and implementing bulk types.

The only public macro is `bitvec`; this module also provides convenience macros
for code generation.
!*/

/** Construct a `&BitSlice` out of a literal array in source code, like `vec!`.

`bits!` can be invoked in a number of ways. It takes the name of a `BitOrder`
implementation, the name of a `BitStore`-implementing fundamental (which must be
one of `u8`, `u16`, `u32`, or `u64`), and zero or more fundamentals (integer,
floating-point) which are used to build the bits. Each fundamental literal
corresponds to one bit, and is considered to represent `1` if it is any other
value than exactly zero.

`bits!` can be invoked with no specifiers, a `BitOrder` specifier, or a
`BitOrder` and a `BitStore` specifier. It cannot be invoked with a `BitStore`
specifier but no `BitOrder` specifier, due to overlap in how those tokens are
matched by the macro system.

Like `vec!`, `bits!` supports bit lists `[0, 1, …]` and repetition markers
`[1; n]`.

# Examples

```rust
use bitvec::prelude::*;

bits![Msb0, u8; 0, 1];
bits![Lsb0, u8; 0, 1,];
bits![Msb0; 0, 1];
bits![Lsb0; 0, 1,];
bits![0, 1];
bits![0, 1,];
bits![0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0];
bits![Msb0, u8; 1; 5];
bits![Lsb0; 0; 5];
bits![1; 5];
bits![bitvec::order::Local; 0, 1,];
```
*/
#[macro_export]
macro_rules! bits {
	($order:ident, $bits:ident; $($val:expr),* $(,)?) => {
		$crate::__bits_from_slice!(
			$order, $bits, $crate::__bits_count!($($val),*),
			&$crate::__bits_store_array!($order, $bits; $($val),*)
		)
	};
	($order:path, $bits:ident; $($val:expr),* $(,)?) => {
		// Wrap multi-tt `order` into a single opaque tt.
		$crate::__bits_from_slice!(
			$order, $bits, $crate::__bits_count!($($val),*),
			&$crate::__bits_store_array!($order, $bits; $($val),*)
		)
	};
	($order:ident; $($val:expr),* $(,)?) => {
		$crate::bits!($order, u64; $($val),*)
	};
	($order:path; $($val:expr),* $(,)?) => {
		$crate::bits!($order, u64; $($val),*)
	};
	($($val:expr),* $(,)?) => {
		$crate::bits!(Local, u64; $($val),*)
	};

	// NOTE: `len` must be `const`, as this is a non-allocating macro.
	($order:ident, $bits:ident; $val:expr; $len:expr) => {
		$crate::__bits_from_slice!($order, $bits, $len, &[
			(0 as $bits).wrapping_sub(($val != 0) as $bits);
			$crate::store::elts::<$bits>($len)
		])
	};
	($order:path, $bits:ident; $val:expr; $len:expr) => {
		// Wrap multi-tt `order` into a single opaque tt.
		$crate::__bits_from_slice!($order, $bits, $len, &[
			(0 as $bits).wrapping_sub(($val != 0) as $bits);
			$crate::store::elts::<$bits>($len)
		])
	};
	($order:ident; $val:expr; $len:expr) => {
		$crate::__bits_from_slice!($order, Word, $len, &[
			(0 as $crate::store::Word).wrapping_sub(
				($val != 0) as $crate::store::Word,
			);
			$crate::store::elts::<$crate::store::Word>($len)
		])
	};
	($order:path; $val:expr; $len:expr) => {
		$crate::__bits_from_slice!($order, Word, $len, &[
			(0 as $crate::store::Word).wrapping_sub(
				($val != 0) as $crate::store::Word,
			);
			$crate::store::elts::<$crate::store::Word>($len)
		])
	};
	($val:expr; $len:expr) => {
		$crate::__bits_from_slice!(Local, Word, $len, &[
			(0 as $crate::store::Word).wrapping_sub(
				($val != 0) as $crate::store::Word,
			);
			$crate::store::elts::<$crate::store::Word>($len)
		])
	};
}

// Not public API
#[doc(hidden)]
#[macro_export]
macro_rules! __bits_count {
	(@ $val:expr) => {
		1
	};
	($($val:expr),*) => {
		0usize $(+ $crate::__bits_count!(@ $val))*
	};
}

// Not public API
#[doc(hidden)]
#[macro_export]
macro_rules! __bits_from_slice {
	// Ensure literal `Msb0`, `Lsb0`, and `Local` always map to our internal
	// definitions of the type, as we've been structurally matching them.
	(Lsb0, $bits:ident, $len:expr, $slice:expr) => {
		&$crate::slice::BitSlice::<
			$crate::order::Lsb0,
			$bits,
		>::from_slice($slice)[.. $len]
	};
	(Msb0, $bits:ident, $len:expr, $slice:expr) => {
		&$crate::slice::BitSlice::<
			$crate::order::Msb0,
			$bits,
		>::from_slice($slice)[.. $len]
	};
	(Local, $bits:ident, $len:expr, $slice:expr) => {
		&$crate::slice::BitSlice::<
			$crate::order::Local,
			$bits,
		>::from_slice($slice)[.. $len]
	};

	// For other types, look it up in the caller's scope.
	($order:tt, $bits:tt, $len:expr, $slice:expr) => {
		&$crate::slice::BitSlice::<$order, $bits>::from_slice($slice)[.. $len]
	};
}

// Not public API
#[doc(hidden)]
#[macro_export]
macro_rules! __elt_from_bits {
	// Optimized Orders
	(
		Lsb0, $bits:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$bits::from_le_bytes([$($crate::private::u8_from_le_bits(
			$a != 0, $b != 0, $c != 0, $d != 0,
			$e != 0, $f != 0, $g != 0, $h != 0,
		)),*])
	};
	(
		Msb0, $bits:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$bits::from_be_bytes([$($crate::private::u8_from_be_bits(
			$a != 0, $b != 0, $c != 0, $d != 0,
			$e != 0, $f != 0, $g != 0, $h != 0,
		)),*])
	};
	(
		Local, $bits:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$bits::from_ne_bytes([$($crate::private::u8_from_local_bits(
			$a != 0, $b != 0, $c != 0, $d != 0,
			$e != 0, $f != 0, $g != 0, $h != 0,
		)),*])
	};

	// Arbitrary Order
	($order:tt, $bits:ident; $($a:tt),*) => {
		{
			let mut value: $bits = 0;
			let _idx = 0u8;
			$(
				$crate::store::BitStore::set::<$order>(
					&mut value,
					unsafe { $crate::indices::BitIdx::new_unchecked(_idx) },
					$a != 0,
				);
				let _idx = _idx + 1;
			)*
			value
		}
	};
}

// Not public API
#[doc(hidden)]
#[macro_export]
macro_rules! __bits_store_array {
	// Entry point.
	($order:tt, $bits:ident; $($val:expr),*) => {
		$crate::__bits_store_array!(
			$order, $bits, []; $($val,)*
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 16
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 32
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 48
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0  // 64
		);
	};

	// NOTE: This has to be first. Abuses quirk of `macro_rules!` where :expr
	// captures are considered a single tt after being matched. Even if the
	// :expr matcher was a literal `0`, after being wrapped by the :expr NT, it
	// no longer is considered to match a literal `0`, so this pattern will only
	// match the extra `0`s added at the end.
	($order:tt, $bits:ident, [$( ($($elt:tt),*) )*]; $(0),*) => {
		[$(
			$crate::__elt_from_bits!($order, $bits; $($elt),*)
		),*]
	};

	// Matchers for each size of word. The end of the word may be padded out
	// with `0`s.
	(
		$order:tt, u8, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u8, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0
			)];
			$($($t)*)?
		);
	};
	(
		$order:tt, u16, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt,
		$a1:tt, $b1:tt, $c1:tt, $d1:tt, $e1:tt, $f1:tt, $g1:tt, $h1:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u16, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0,
				$a1, $b1, $c1, $d1, $e1, $f1, $g1, $h1
			)];
			$($($t)*)?
		);
	};
	(
		$order:tt, u32, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt,
		$a1:tt, $b1:tt, $c1:tt, $d1:tt, $e1:tt, $f1:tt, $g1:tt, $h1:tt,
		$a2:tt, $b2:tt, $c2:tt, $d2:tt, $e2:tt, $f2:tt, $g2:tt, $h2:tt,
		$a3:tt, $b3:tt, $c3:tt, $d3:tt, $e3:tt, $f3:tt, $g3:tt, $h3:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u32, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0,
				$a1, $b1, $c1, $d1, $e1, $f1, $g1, $h1,
				$a2, $b2, $c2, $d2, $e2, $f2, $g2, $h2,
				$a3, $b3, $c3, $d3, $e3, $f3, $g3, $h3
			)];
			$($($t)*)?
		);
	};
	(
		$order:tt, u64, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt,
		$a1:tt, $b1:tt, $c1:tt, $d1:tt, $e1:tt, $f1:tt, $g1:tt, $h1:tt,
		$a2:tt, $b2:tt, $c2:tt, $d2:tt, $e2:tt, $f2:tt, $g2:tt, $h2:tt,
		$a3:tt, $b3:tt, $c3:tt, $d3:tt, $e3:tt, $f3:tt, $g3:tt, $h3:tt,
		$a4:tt, $b4:tt, $c4:tt, $d4:tt, $e4:tt, $f4:tt, $g4:tt, $h4:tt,
		$a5:tt, $b5:tt, $c5:tt, $d5:tt, $e5:tt, $f5:tt, $g5:tt, $h5:tt,
		$a6:tt, $b6:tt, $c6:tt, $d6:tt, $e6:tt, $f6:tt, $g6:tt, $h6:tt,
		$a7:tt, $b7:tt, $c7:tt, $d7:tt, $e7:tt, $f7:tt, $g7:tt, $h7:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u64, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0,
				$a1, $b1, $c1, $d1, $e1, $f1, $g1, $h1,
				$a2, $b2, $c2, $d2, $e2, $f2, $g2, $h2,
				$a3, $b3, $c3, $d3, $e3, $f3, $g3, $h3,
				$a4, $b4, $c4, $d4, $e4, $f4, $g4, $h4,
				$a5, $b5, $c5, $d5, $e5, $f5, $g5, $h5,
				$a6, $b6, $c6, $d6, $e6, $f6, $g6, $h6,
				$a7, $b7, $c7, $d7, $e7, $f7, $g7, $h7
			)];
			$($($t)*)?
		);
	};
}

/** Construct a `BitVec` out of a literal array in source code, like `vec!`.

`bitvec!` can be invoked in a number of ways. It takes the name of a `BitOrder`
implementation, the name of a `BitStore`-implementing fundamental, and zero or
more fundamentals (integer, floating-point, or boolean) which are used to build
the bits. Each fundamental literal corresponds to one bit, and is considered to
represent `1` if it is any other value than exactly zero.

`bitvec!` can be invoked with no specifiers, a `BitOrder` specifier, or a
`BitOrder` and a `BitStore` specifier. It cannot be invoked with a `BitStore`
specifier but no `BitOrder` specifier, due to overlap in how those tokens are
matched by the macro system.

Like `vec!`, `bitvec!` supports bit lists `[0, 1, …]` and repetition markers
`[1; n]`.

# Notes

The bit list syntax `bitvec![expr, expr, expr...]` currently produces an
`&[bool]` slice of the initial pattern, which is written into the final
artifact’s static memory and may consume excessive space.

The repetition syntax `bitec![expr; count]` currently zeros its allocated buffer
before setting the first `count` bits to `expr`. This may result in a
performance penalty when using `bitvec![1; N]`, as the allocation will be zeroed
and then a subset will be set high.

This behavior is currently required to maintain compatibility with `serde`
expectations that dead bits are zero. As the `serdes` module removes those
expectations, the repetition syntax implementation may speed up.

# Examples

```rust
use bitvec::prelude::*;

bitvec![Msb0, u8; 0, 1];
bitvec![Lsb0, u8; 0, 1,];
bitvec![Msb0; 0, 1];
bitvec![Lsb0; 0, 1,];
bitvec![0, 1];
bitvec![0, 1,];
bitvec![Msb0, u8; 1; 5];
bitvec![Lsb0; 0; 5];
bitvec![1; 5];
```
**/
#[cfg(feature = "alloc")]
#[macro_export]
macro_rules! bitvec {
	($order:ident, $bits:ident; $($val:expr),* $(,)?) => {
		{
			let mut bitvec = $crate::__bitvec_from_slice!(
				$order,
				$bits,
				$crate::__bits_store_array!($order, $bits; $($val),*)
			);
			bitvec.truncate($crate::__bits_count!($($val),*));
			bitvec
		}
	};
	($order:path, $bits:ident; $($val:expr),* $(,)?) => {
		// Wrap multi-tt `order` into a single opaque tt.
		{
			let mut bitvec = $crate::__bitvec_from_slice!(
				$order,
				$bits,
				$crate::__bits_store_array!($order, $bits; $($val),*)
			);
			bitvec.truncate($crate::__bits_count!($($val),*));
			bitvec
		}
	};
	($order:ident; $($val:expr),* $(,)?) => {
		$crate::bitvec!($order, u64; $($val),*);
	};
	($order:path; $($val:expr),* $(,)?) => {
		$crate::bitvec!($order, u64; $($val),*);
	};
	($($val:expr),* $(,)?) => {
		$crate::bitvec!(Local, u64; $($val),*);
	};

	($order:ident, $bits:ident; $val:expr; $len:expr) => {
		$crate::vec::BitVec::<$order, $bits>::repeat($val != 0, $len)
	};
	($order:path, $bits:ident; $val:expr; $len:expr) => {
		$crate::vec::BitVec::<$order, $bits>::repeat($val != 0, $len)
	};
	($order:ident; $val:expr; $len:expr) => {
		$crate::vec::BitVec::<
			$order,
			$crate::store::Word,
		>::repeat($val != 0, $len)
	};
	($order:path; $val:expr; $len:expr) => {
		$crate::vec::BitVec::<
			$order,
			$crate::store::Word,
		>::repeat($val != 0, $len)
	};
	($val:expr; $len:expr) => {
		$crate::vec::BitVec::<
			$crate::order::Local,
			$crate::store::Word,
		>::repeat($val != 0, $len)
	};
}

// Not public API
#[cfg(feature = "alloc")]
#[doc(hidden)]
#[macro_export]
macro_rules! __bitvec_from_slice {
	// Ensure literal `Msb0`, `Lsb0`, and `Local` always map to our internal
	// definitions of the type, as we've been structurally matching them.
	(Lsb0, $bits:ident, $slice:expr) => {
		$crate::vec::BitVec::<
			$crate::order::Lsb0,
			$bits,
		>::from_slice(&$slice[..])
	};
	(Msb0, $bits:ident, $slice:expr) => {
		$crate::vec::BitVec::<
			$crate::order::Msb0,
			$bits,
		>::from_slice(&$slice[..])
	};
	(Local, $bits:ident, $slice:expr) => {
		$crate::vec::BitVec::<
			$crate::order::Local,
			$bits,
		>::from_slice(&$slice[..])
	};

	// For other types, look it up in the caller's scope.
	($order:tt, $bits:tt, $slice:expr) => {
		$crate::vec::BitVec::<$order, $bits>::from_slice(&$slice[..])
	};
}

/** Construct a `BitBox` out of a literal array in source code, like `bitvec!`.

This has exactly the same syntax as [`bitvec!`], and in fact is a thin wrapper
around `bitvec!` that calls `.into_boxed_slice()` on the produced `BitVec` to
freeze it.

[`bitvec!`]: #macro.bitvec
**/
#[cfg(feature = "alloc")]
#[macro_export]
macro_rules! bitbox {
	($($t:tt)*) => {
		$crate::bitvec![$($t)*].into_boxed_bitslice()
	};
}

#[doc(hidden)]
macro_rules! __bitslice_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<C, T >core::ops::ShlAssign<$t>
		for $crate::prelude::BitSlice<C,T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shl_assign(&mut self, shamt: $t) {
				core::ops::ShlAssign::<usize>::shl_assign(
					self,
					shamt as usize,
				)
			}
		}

		#[doc(hidden)]
		impl<C, T> core::ops::ShrAssign<$t>
		for $crate::prelude::BitSlice<C,T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shr_assign(&mut self,shamt: $t){
				core::ops::ShrAssign::<usize>::shr_assign(
					self,
					shamt as usize,
				)
			}
		}
	)+ };
}

#[cfg(feature = "alloc")]
#[doc(hidden)]
macro_rules! __bitvec_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<C, T> core::ops::Shl<$t>
		for $crate::vec::BitVec<C, T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			type Output = <Self as core::ops::Shl<usize>>::Output;

			fn shl(self, shamt: $t) -> Self::Output {
				core::ops::Shl::<usize>::shl(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<C, T> core::ops::ShlAssign<$t>
		for $crate::vec::BitVec<C, T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shl_assign(&mut self, shamt: $t) {
				core::ops::ShlAssign::<usize>::shl_assign(
					self,
					shamt as usize,
				)
			}
		}

		#[doc(hidden)]
		impl<C, T> core::ops::Shr<$t>
		for $crate::vec::BitVec<C, T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			type Output = <Self as core::ops::Shr<usize>>::Output;

			fn shr(self, shamt: $t) -> Self::Output {
				core::ops::Shr::<usize>::shr(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<C, T> core::ops::ShrAssign<$t>
		for $crate::vec::BitVec<C, T>
		where C: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shr_assign(&mut self, shamt: $t) {
				core::ops::ShrAssign::<usize>::shr_assign(
					self,
					shamt as usize,
				)
			}
		}
	)+ };
}

#[cfg(test)]
mod tests {
	#[allow(unused_imports)]
	use crate::order::{
		Msb0,
		Lsb0,
	};

	#[test]
	#[cfg(feature = "alloc")]
	fn compile_bits_macros() {
		bits![0, 1];
		bits![Msb0; 0, 1];
		bits![Lsb0; 0, 1];
		bits![Msb0, u8; 0, 1];
		bits![Lsb0, u8; 0, 1];
		bits![Msb0, u16; 0, 1];
		bits![Lsb0, u16; 0, 1];
		bits![Msb0, u32; 0, 1];
		bits![Lsb0, u32; 0, 1];

		#[cfg(target_pointer_width = "64")] {

		bits![Msb0, u64; 0, 1];
		bits![Lsb0, u64; 0, 1];

		}

		bits![1; 70];
		bits![Msb0; 0; 70];
		bits![Lsb0; 1; 70];
		bits![Msb0, u8; 0; 70];
		bits![Lsb0, u8; 1; 70];
		bits![Msb0, u16; 0; 70];
		bits![Lsb0, u16; 1; 70];
		bits![Msb0, u32; 0; 70];
		bits![Lsb0, u32; 1; 70];

		#[cfg(target_pointer_width = "64")] {

		bits![Msb0, u64; 0; 70];
		bits![Lsb0, u64; 1; 70];

		}
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn compile_bitvec_macros() {
		bitvec![0, 1];
		bitvec![Msb0; 0, 1];
		bitvec![Lsb0; 0, 1];
		bitvec![Msb0, u8; 0, 1];
		bitvec![Lsb0, u8; 0, 1];
		bitvec![Msb0, u16; 0, 1];
		bitvec![Lsb0, u16; 0, 1];
		bitvec![Msb0, u32; 0, 1];
		bitvec![Lsb0, u32; 0, 1];

		#[cfg(target_pointer_width = "64")] {

		bitvec![Msb0, u64; 0, 1];
		bitvec![Lsb0, u64; 0, 1];

		}

		bitvec![1; 70];
		bitvec![Msb0; 0; 70];
		bitvec![Lsb0; 1; 70];
		bitvec![Msb0, u8; 0; 70];
		bitvec![Lsb0, u8; 1; 70];
		bitvec![Msb0, u16; 0; 70];
		bitvec![Lsb0, u16; 1; 70];
		bitvec![Msb0, u32; 0; 70];
		bitvec![Lsb0, u32; 1; 70];

		#[cfg(target_pointer_width = "64")] {

		bitvec![Msb0, u64; 0; 70];
		bitvec![Lsb0, u64; 1; 70];

		}
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn compile_bitbox_macros() {
		bitbox![0, 1];
		bitbox![Msb0; 0, 1];
		bitbox![Lsb0; 0, 1];
		bitbox![Msb0, u8; 0, 1];
		bitbox![Lsb0, u8; 0, 1];
		bitbox![Msb0, u16; 0, 1];
		bitbox![Lsb0, u16; 0, 1];
		bitbox![Msb0, u32; 0, 1];
		bitbox![Lsb0, u32; 0, 1];

		#[cfg(target_pointer_width = "64")] {

		bitbox![Msb0, u64; 0, 1];
		bitbox![Lsb0, u64; 0, 1];

		}

		bitbox![1; 70];
		bitbox![Msb0; 0; 70];
		bitbox![Lsb0; 1; 70];
		bitbox![Msb0, u8; 0; 70];
		bitbox![Lsb0, u8; 1; 70];
		bitbox![Msb0, u16; 0; 70];
		bitbox![Lsb0, u16; 1; 70];
		bitbox![Msb0, u32; 0; 70];
		bitbox![Lsb0, u32; 1; 70];

		#[cfg(target_pointer_width = "64")] {

		bitbox![Msb0, u64; 0; 70];
		bitbox![Lsb0, u64; 1; 70];

		}
	}
}
