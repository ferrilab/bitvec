/*! Utility macros for constructing data structures and implementing bulk types.

The public macros are `bits!`, `bitvec!`, and `bitbox!`.
!*/

#[macro_use]
#[doc(hidden)]
pub mod internal;

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
bits![Local; 0, 1,];
```
**/
#[macro_export]
macro_rules! bits {
	//  Sequence syntax `[bit (, bit)*]` or `[(bit ,)*]`

	//  Explicit order and store.
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		static DATA: &[$store] = &$crate::__bits_store_array!(
			$order, $store; $($val),*
		);
		&$crate::__bits_from_slice!(
			$order, $store, $crate::__count!($($val),*), DATA
		)
	}};
	/* Duplicate arms, differing in `$order:ident` and `$order:path`, force the
	matcher to wrap a `:path`, which is `[:tt]`, as a single opaque `:tt` for
	propagation through the macro call. Since the literal `$order` values will
	match as `:ident`, not `:path`, this will only enter for orderings that the
	rest of the macros would not be able to inspect and special-case *anyway*.
	*/
	($order:path, $store:ident; $($val:expr),* $(,)?) => {{
		static DATA: &[$store] = &$crate::__bits_store_array!(
			$order, $store; $($val),*
		);
		&$crate::__bits_from_slice!(
			$order, $store, $crate::__count!($($val),*), DATA
		)
	}};

	//  Explicit order, default store.
	($order:ident; $($val:expr),* $(,)?) => {
		$crate::bits!($order, usize; $($val),*)
	};
	($order:path; $($val:expr),* $(,)?) => {
		$crate::bits!($order, usize; $($val),*)
	};

	//  Default order and store.
	($($val:expr),* $(,)?) => {
		$crate::bits!(Local, usize; $($val),*)
	};

	//  Repetition syntax `[bit ; count]`
	//  NOTE: `count` must be `const`, as this is a non-allocating macro.

	//  Explicit order and store.
	($order:ident, $store:ident; $val:expr; $len:expr) => {{
		static DATA: &[$store] = &[
			$crate::__extend_bool!($val, $store);
			$crate::store::elts::<$store>($len)
		];
		&$crate::__bits_from_slice!($order, $store, $len, DATA)
	}};
	($order:path, $store:ident; $val:expr; $len:expr) => {{
		static DATA: &[$store] = &[
			$crate::__extend_bool!($val, $store);
			$crate::store::elts::<$store>($len)
		];
		&$crate::__bits_from_slice!($order, $store, $len, DATA)
	}};

	//  Explicit order, default store.
	($order:ident; $val:expr; $len:expr) => {
		$crate::bits!($order, usize; $val; $len)
	};
	($order:path; $val:expr; $len:expr) => {
		$crate::bits!($order, usize; $val; $len)
	};

	//  Default order and store.
	($val:expr; $len:expr) => {
		$crate::bits!(Local, usize; $val; $len)
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
	//  First, capture the repetition syntax, as it is permitted to use runtime
	//  values for the repetition count.
	($order:ty, $store:ident; $val:expr; $rep:expr) => {
		$crate::vec::BitVec::<$order, $store>::repeat($val != 0, $rep)
	};
	($order:ty; $val:expr; $rep:expr) => {
		$crate::bitvec!($order, usize; $val; $rep)
	};
	($val:expr; $rep:expr) => {
		$crate::bitvec!($crate::order::Local, usize; $val; $rep)
	};

	//  Delegate all others to the `bits!` macro.
	($($arg:tt)*) => {{
		let bits: &'static $crate::slice::BitSlice::<_, _> = $crate::bits!($($arg)*);
		$crate::vec::BitVec::from_bitslice(bits)
	}};
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
	($($arg:tt)*) => {
		$crate::bitvec![$($arg)*].into_boxed_bitslice()
	};
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
