/*! Utility macros for constructing data structures and implementing bulk types.

The only public macro is `bitvec`; this module also provides convenience macros
for code generation.
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

	//  Explicit order, literal `Word` store.
	($order:ident, Word; $($val:expr),* $(,)?) => {
		$crate::__bits_from_words!($order; $($val),*)
	};
	/* Duplicate arms, differing in `$order:ident` and `$order:path`, force the
	matcher to wrap a `:path`, which is `[:tt]`, as a single opaque `:tt` for
	propagation through the macro call. Since the literal `$order` values will
	match as `:ident`, not `:path`, this will only enter for orderings that the
	rest of the macros would not be able to inspect and special-case *anyway*.
	*/
	($order:path, Word; $($val:expr),* $(,)?) => {
		$crate::__bits_from_words!($order; $($val),*)
	};

	//  Explicit order and store.
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		static DATA: &[$store] = &$crate::__bits_store_array!(
			$order, $store; $($val),*
		);
		&$crate::__bits_from_slice!(
			$order, $store, $crate::__count!($($val),*), DATA
		)
	}};
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
		$crate::__bits_from_words!($order; $($val),*)
	};
	($order:path; $($val:expr),* $(,)?) => {
		$crate::__bits_from_words!($order; $($val),*)
	};

	//  Default order and store.
	($($val:expr),* $(,)?) => {
		$crate::__bits_from_words!(Local; $($val),*)
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
		$crate::__bits_from_words!($order; $val; $len)
	};
	($order:path; $val:expr; $len:expr) => {
		$crate::__bits_from_words!($order; $val; $len)
	};

	//  Default order and store.
	($val:expr; $len:expr) => {
		$crate::bits!(Local; $val; $len)
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
	/* TODO(myrrlyn): Make this arm viable.
	($($arg:tt)) => {
		($crate::bits!($($arg))).to_owned()
	};
	*/

	//  Sequence syntax
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		let data = $crate::__bits_store_array!($order, $store; $($val),*);
		let vec = data[..].to_owned();
		let mut out = $crate::vec::BitVec::<$order, $store>::from_vec(vec);
		out.truncate($crate::__count!($($val),*));
		out
	}};
	($order:path, $store:ident; $($val:expr),* $(,)?) => {{
		let data = $crate::__bits_store_array!($order, $store; $($val),*);
		let vec = data[..].to_owned();
		let mut out = $crate::vec::BitVec::<$order, $store>::from_vec(vec);
		out.truncate($crate::__count!($($val),*));
		out
	}};

	($order:ident; $($val:expr),* $(,)?) => {{
		#[cfg(target_pointer_width = "32")]
		let data = $crate::__bits_store_array!(Local, u32; $($val),*);

		#[cfg(target_pointer_width = "64")]
		let data = $crate::__bits_store_array!(Local, u64; $($val),*);

		let vec = data[..].to_owned();
		let mut out = $crate::vec::BitVec::<
			$order,
			$crate::store::Word,
		>::from_vec(vec);
		out.truncate($crate::__count!($($val),*));
		out
	}};
	($order:path; $($val:expr),* $(,)?) => {{
		#[cfg(target_pointer_width = "32")]
		let data = $crate::__bits_store_array!(Local, u32; $($val),*);

		#[cfg(target_pointer_width = "64")]
		let data = $crate::__bits_store_array!(Local, u64; $($val),*);

		let vec = data[..].to_owned();
		let mut out = $crate::vec::BitVec::<
			$order,
			$crate::store::Word,
		>::from_vec(vec);
		out.truncate($crate::__count!($($val),*));
		out
	}};

	($($val:expr),* $(,)?) => {{
		#[cfg(target_pointer_width = "32")]
		let data = $crate::__bits_store_array!(Local, u32; $($val),*);

		#[cfg(target_pointer_width = "64")]
		let data = $crate::__bits_store_array!(Local, u64; $($val),*);

		let vec = data[..].to_owned();
		let mut out = $crate::vec::BitVec::<
			$crate::order::Local,
			$crate::store::Word,
		>::from_vec(vec);
		out.truncate($crate::__count!($($val),*));
		out
	}};

	//  Repetition syntax

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
