//! Constructor macros for the crate’s collection types.

#![allow(deprecated)]

#[macro_use]
#[doc(hidden)]
pub mod internal;

/** Constructs a type definition for a [`BitArray`].

This macro takes a minimum number of bits, and optionally a set of [`BitOrder`]
and [`BitStore`] implementors, and creates a `BitArray` type definition that
satisfies them. Because this macro is used in type position, it uses
`PascalCase` rather than `snake_case` for its name.

# Grammar

```rust
use bitvec::prelude::*;
use core::cell::Cell;

const CENT: usize = bitvec::mem::elts::<usize>(100);
let a: BitArr!(for 100)
  = BitArray::<Lsb0, [usize; CENT]>::zeroed();

let b: BitArr!(for 100, in u32)
  = BitArray::<Lsb0, [u32; 4]>::zeroed();

let c: BitArr!(for 100, in Msb0, Cell<u16>)
  = BitArray::<Msb0, [Cell<u16>; 7]>::zeroed();
```

The length expression must be a `const`-expression. It may be a literal or a
named `const` expression. The type arguments have no restrictions, so long as
they resolve to valid trait implementors.

[`BitArray`]: crate::array::BitArray
[`BitOrder`]: crate::order::BitOrder
[`BitStore`]: crate::store::BitStore
**/
#[macro_export]
macro_rules! BitArr {
	(for $len:expr, in $order:ty, $store:ty) => {
		$crate::array::BitArray::<
			$order, [$store; $crate::mem::elts::<$store>($len)]
		>
	};

	(for $len:expr, in $store:ty) => {
		$crate::BitArr!(for $len, in $crate::order::Lsb0, $store)
	};

	(for $len:expr) => {
		$crate::BitArr!(for $len, in usize)
	};
}

/** Constructs a new [`BitArray`] from a bit-pattern description.

This macro takes a superset of the [`vec!`] argument syntax: it may be invoked
with either a sequence of bit expressions, or a single bit expression and a
repetition counter. Additionally, you may provide the names of a [`BitOrder`]
and a [`BitStore`] implementor as the `BitArray`’s type arguments.

# Argument Rules

Bit expressions must be integer literals. Ambiguity restrictions in the macro
syntax forbid the use of identifiers to existing variables, even `const` values.
These are converted to `bool` through the expression `$val != 0`. Any non-zero
enteger becomes `true`, and `0` becomes `false`.

You may use any name or path to a [`BitOrder`] implementation. However, the
identifier tokens `Lsb0`, `Msb0`, and `LocalBits` are matched directly and
specialized to have compile-time constructions, whereäs any other name or path
will not be known to the macro, and will execute at runtime.

The [`BitStore`] argument **must** be the name of an unsigned integer
fundamental, an atomic, or a `Cell<>` wrapper of that unsigned integer. These
are matched by token, not by type, and no other identifier is accepted. Using
any other token will cause the macro to fail.

# Examples

```rust
use bitvec::prelude::*;
use core::cell::Cell;

radium::if_atomic! { if atomic(32) {
  use core::sync::atomic::AtomicU32;
} }

let a: BitArray = bitarr![0, 1, 0, 1, 2];
assert_eq!(a.count_ones(), 3);

let b: BitArray = bitarr![2; 5];
assert!(b.all());
assert!(b.len() >= 5);

let c = bitarr![Lsb0, Cell<u16>; 0, 1, 0, 0, 1];
radium::if_atomic! { if atomic(32) {
	let d = bitarr![Msb0, AtomicU32; 0, 0, 1, 0, 1];
} }

let e: BitArr!(for 20, in LocalBits, u8) = bitarr![LocalBits, u8; 0; 20];
```

[`BitArray`]: crate::array::BitArray
[`BitOrder`]: crate::order::BitOrder
[`BitStore`]: crate::store::BitStore
[`vec!`]: macro@alloc::vec
**/
#[macro_export]
macro_rules! bitarr {
	/* The duplicate matchers differing in `:ident` and `:path` exploit a rule
	of macro expansion so that the literal tokens `Lsb0`, `Msb0`, and
	`LocalBits` can be propagated through the entire expansion, thus selecting
	optimized construction sequences. Names of orderings other than these three
	tokens become opaque, and route to a fallback implementation that is less
	likely to be automatically optimized during codegen.

	`:ident` fragments are inspectable as literal tokens by future macros, while
	`:path` fragments become a single opaque object that can only match as
	`:path` or `:tt` bindings when passed along.
	*/

	($order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {
		$crate::array::BitArray::<
			$order, [
				$crate::macros::internal::core::cell::Cell<$store>;
				$crate::__count_elts!($store; $($val),*)
			],
		>::new(
			$crate::__encode_bits!($order, Cell<$store>; $($val),*)
		)
	};
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {
		$crate::array::BitArray::<
			$order,
			[$store; $crate::__count_elts!($store; $($val),*)],
		>::new(
			$crate::__encode_bits!($order, $store; $($val),*)
		)
	};

	($order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {
		$crate::array::BitArray::<
			$order, [
				$crate::macros::internal::core::cell::Cell<$store>;
				$crate::__count_elts!($store; $($val),*)
			],
		>::new(
			$crate::__encode_bits!($order, Cell<$store>; $($val),*)
		)
	};
	($order:path, $store:ident; $($val:expr),* $(,)?) => {
		$crate::array::BitArray::<
			$order,
			[$store; $crate::__count_elts!($store; $($val),*)],
		>::new(
			$crate::__encode_bits!($order, $store; $($val),*)
		)
	};

	($order:ident, Cell<$store:ident>; $val:expr; $len:expr) => {{
		let elem = $crate::__extend_bool!($val, $store);
		let base = [elem; $crate::mem::elts::<$store>($len)];
		let elts = unsafe {
			$crate::macros::internal::core::mem::transmute(base)
		};
		$crate::array::BitArray::<
			$order,
			[Cell<$store>; $crate::mem::elts::<$store>($len)],
		>::new(elts)
	}};
	($order:ident, $store:ident; $val:expr; $len:expr) => {{
		use $crate::macros::internal::core::mem::MaybeUninit;
		use $crate::store::BitStore as _;
		const LEN: usize = $crate::mem::elts::<$store>($len);

		//  Create a local copy of the base element.
		let elem = $crate::__extend_bool!($val, $store);
		//  Create the array.
		let mut elts: MaybeUninit<[$store; LEN]> = MaybeUninit::uninit();
		//  Get the address of the base element in the array
		let mut addr = elts.as_mut_ptr() as *mut $store;
		for _ in 0 .. LEN {
			unsafe {
				//  Copy `elem` into each element of the array.
				addr.write(<$store>::from(elem.load_value()));
				addr = addr.add(1);
			}
		}
		$crate::array::BitArray::<$order, [$store; LEN]>::new(unsafe {
			elts.assume_init()
		})
		//  Constructing an array of non-`Copy` objects is really hard.
	}};

	($order:path, Cell<$store:ident>; $val:expr; $len:expr) => {{
		let elem = $crate::__extend_bool!($val, $store);
		let base = [elem; $crate::mem::elts::<$store>($len)];
		let elts = unsafe {
			$crate::macros::internal::core::mem::transmute(base)
		};
		$crate::array::BitArray::<
			$order,
			[Cell<$store>; $crate::mem::elts::<$store>($len)],
		>::new(elts)
	}};
	($order:path, $store:ident; $val:expr; $len:expr) => {{
		use $crate::macros::internal::core::mem::MaybeUninit;
		use $crate::store::BitStore as _;
		const LEN: usize = $crate::mem::elts::<$store>($len);

		let elem = $crate::__extend_bool!($val, $store);
		let mut elts: MaybeUninit<[$store; LEN]> = MaybeUninit::uninit();
		let mut addr = elts.as_mut_ptr() as *mut $store;
		for _ in 0 .. LEN {
			unsafe {
				addr.write(<$store>::from(elem.load_value()));
				addr = addr.add(1);
			}
		}
		$crate::array::BitArray::<$order, [$store; LEN]>::new(unsafe {
			elts.assume_init()
		})
	}};

	($($val:expr),* $(,)?) => {
		$crate::bitarr!(Lsb0, usize; $($val),*)
	};

	($val:expr; $len:expr) => {
		$crate::bitarr!(Lsb0, usize; $val; $len)
	};
}

/** Creates a borrowed [`BitSlice`] in the local scope.

This macro constructs a [`BitArray`] temporary and then immediately borrows it
as a `BitSlice`. The compiler should extend the lifetime of the underlying
`BitArray` for the duration of the expression’s lifetime.

This macro takes a superset of the [`vec!`] argument syntax: it may be invoked
with either a sequence of bit expressions, or a single bit expression and a
repetiton counter. Additionally, you may provide the names of a [`BitOrder`] and
a [`BitStore`] implementor as the `BitArray`’s type arguments. You may also use
`mut` as the first argument of the macro in order to produce an `&mut BitSlice`
reference rather than a `&BitSlice` immutable reference.

# Argument Rules

Bit expressions must be integer literals. Ambiguity restrictions in the macro
syntax forbid the use of identifiers to existing variables, even `const` values.
These are converted to `bool` through the expression `$val != 0`. Any non-zero
enteger becomes `true`, and `0` becomes `false`.

You may use any name or path to a [`BitOrder`] implementation. However, the
identifier tokens `Lsb0`, `Msb0`, and `LocalBits` are matched directly and
specialized to have compile-time constructions, whereäs any other name or path
will not be known to the macro, and will execute at runtime.

The [`BitStore`] argument **must** be the name of an unsigned integer
fundamental, an atomic, or a `Cell<>` wrapper of that unsigned integer. These
are matched by token, not by type, and no other identifier is accepted. Using
any other token will cause the macro to fail.

# Examples

```rust
use bitvec::prelude::*;
use core::cell::Cell;

radium::if_atomic! { if atomic(16) {
  use core::sync::atomic::AtomicU32;
} }

let a: &BitSlice = bits![0, 1, 0, 1, 2];
assert_eq!(a.count_ones(), 3);

let b: &mut BitSlice = bits![mut 2; 5];
assert!(b.all());
assert_eq!(b.len(), 5);

let c = bits![Lsb0, Cell<u16>; 0, 1, 0, 0, 1];
c.set_aliased(0, true);
let d = bits![Msb0, AtomicU32; 0, 0, 1, 0, 1];
d.set_aliased(0, true);
```

[`BitArray`]: crate::array::BitArray
[`BitOrder`]: crate::order::BitOrder
[`BitSlice`]: crate::slice::BitSlice
[`BitStore`]: crate::store::BitStore
[`vec!`]: macro@alloc::vec
**/
#[macro_export]
macro_rules! bits {
	//  Sequence syntax `[bit (, bit)*]` or `[(bit ,)*]`.

	//  Explicit order and store.

	(mut $order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		&mut $crate::bitarr![$order, Cell<$store>; $($val),*][.. $crate::__count!($($val),*)]
	}};
	(mut $order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		&mut $crate::bitarr![$order, $store; $($val),*][.. $crate::__count!($($val),*)]
	}};

	(mut $order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		&mut $crate::bitarr![$order, Cell<$store>; $($val),*][.. $crate::__count!($($val),*)]
	}};
	(mut $order:path, $store:ident; $($val:expr),* $(,)?) => {{
		&mut $crate::bitarr![$order, $store; $($val),*][.. $crate::__count!($($val),*)]
	}};

	//  Repetition syntax `[bit ; count]`.
	//  NOTE: `count` must be a `const`, as this is a non-allocating macro.

	//  Explicit order and store.

	(mut $order:ident, Cell<$store:ident>; $val:expr; $len:expr) => {{
		&mut $crate::bitarr![$order, Cell<$store>; $val; $len][.. $len]
	}};
	(mut $order:ident, $store:ident; $val:expr; $len:expr) => {{
		&mut $crate::bitarr![$order, $store; $val; $len][.. $len]
	}};

	(mut $order:path, Cell<$store:ident>; $val:expr; $len:expr) => {{
		&mut $crate::bitarr![$order, Cell<$store>; $val; $len][.. $len]
	}};
	(mut $order:path, $store:ident; $val:expr; $len:expr) => {{
		&mut $crate::bitarr![$order, $store; $val; $len][.. $len]
	}};

	//  Default order and store.

	(mut $($val:expr),* $(,)?) => {
		$crate::bits!(mut Lsb0, usize; $($val),*)
	};

	(mut $val:expr; $len:expr) => {
		$crate::bits!(mut Lsb0, usize; $val; $len)
	};

	//  Repeat everything from above, but now immutable.

	($order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		&$crate::bitarr![$order, Cell<$store>; $($val),*][.. $crate::__count!($($val),*)]
	}};
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		&$crate::bitarr![$order, $store; $($val),*][.. $crate::__count!($($val),*)]
	}};

	($order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		&$crate::bitarr![$order, Cell<$store>; $($val),*][.. $crate::__count!($($val),*)]
	}};
	($order:path, $store:ident; $($val:expr),* $(,)?) => {{
		&$crate::bitarr![$order, $store; $($val),*][.. $crate::__count!($($val),*)]
	}};

	($order:ident, Cell<$store:ident>; $val:expr; $len:expr) => {{
		&$crate::bitarr![$order, Cell<$store>; $val; $len][.. $len]
	}};
	($order:ident, $store:ident; $val:expr; $len:expr) => {{
		&$crate::bitarr![$order, $store; $val; $len][.. $len]
	}};

	($order:path, Cell<$store:ident>; $val:expr; $len:expr) => {{
		&$crate::bitarr![$order, Cell<$store>; $val; $len][.. $len]
	}};
	($order:path, $store:ident; $val:expr; $len:expr) => {{
		&$crate::bitarr![$order, $store; $val; $len][.. $len]
	}};

	//  Default order and store.
	//  These must be last to prevent spurious matches on the type arguments.

	($($val:expr),* $(,)?) => {
		$crate::bits!(Lsb0, usize; $($val),*)
	};

	($val:expr; $len:expr) => {
		$crate::bits!(Lsb0, usize; $val; $len)
	};
}

/** Constructs a new [`BitVec`] from a bit-pattern description.

This macro takes a superset of the [`vec!`] argument syntax: it may be invoked
with either a sequence of bit expressions, or a single bit expression and a
repetition counter. Additionally, you may provide the names of a [`BitOrder`]
and a [`BitStore`] implementor as the `BitVec`’s type arguments.

# Argument Rules

Bit expressions must be integer literals. Ambiguity restrictions in the macro
syntax forbid the use of identifiers to existing variables, even `const` values.
These are converted to `bool` through the expression `$val != 0`. Any non-zero
enteger becomes `true`, and `0` becomes `false`.

You may use any name or path to a [`BitOrder`] implementation. However, the
identifier tokens `Lsb0`, `Msb0`, and `LocalBits` are matched directly and
specialized to have compile-time constructions, whereäs any other name or path
will not be known to the macro, and will execute at runtime.

The [`BitStore`] argument **must** be the name of an unsigned integer
fundamental, an atomic, or a `Cell<>` wrapper of that unsigned integer. These
are matched by token, not by type, and no other identifier as accepted. Using
any other token will cause the macro to fail.

# Examples

```rust
use bitvec::prelude::*;
use core::cell::Cell;

radium::if_atomic! { if atomic(32) {
  use core::sync::atomic::AtomicU32;
} }

let a: BitVec = bitvec![0, 1, 0, 1, 2];
assert_eq!(a.count_ones(), 3);

let b: BitVec = bitvec![2; 5];
assert!(b.all());
assert_eq!(b.len(), 5);

let c = bitvec![Lsb0, Cell<u16>; 0, 1, 0, 0, 1];
let d = bitvec![Msb0, AtomicU32; 0, 0, 1, 0, 1];
```

[`BitOrder`]: crate::order::BitOrder
[`BitStore`]: crate::store::BitStore
[`BitVec`]: crate::vec::BitVec
[`vec!`]: macro@alloc::vec
**/
#[macro_export]
#[cfg(feature = "alloc")]
macro_rules! bitvec {
	//  First, capture the repetition syntax, as it is permitted to use runtime
	//  values for the repetition count.
	($order:ty, Cell<$store:ident>; $val:expr; $rep:expr) => {
		$crate::vec::BitVec::<
			$order,
			$crate::macros::internal::core::cell::Cell<$store>
		>::repeat($val != 0, $rep)
	};
	($order:ty, $store:ident; $val:expr; $rep:expr) => {
		$crate::vec::BitVec::<$order, $store>::repeat($val != 0, $rep)
	};

	($val:expr; $rep:expr) => {
		$crate::vec::BitVec::<$crate::order::Lsb0, usize>::repeat($val != 0, $rep)
	};

	//  Delegate all others to the `bits!` macro.
	($($arg:tt)*) => {{
		$crate::vec::BitVec::from_bitslice($crate::bits!($($arg)*))
	}};
}

/** Constructs a new [`BitBox`] from a bit-pattern description.

This forwards all its arguments to [`bitvec!`], and then calls
[`.into_boxed_bitslice()`] on the result to freeze the allocation.

[`BitBox`]: crate::boxed::BitBox
[`bitvec!`]: macro@crate::bitvec
[`.into_boxed_bitslice()`]: crate::vec::BitVec::into_boxed_bitslice
**/
#[macro_export]
#[cfg(feature = "alloc")]
macro_rules! bitbox {
	($($arg:tt)*) => {
		$crate::bitvec!($($arg)*).into_boxed_bitslice()
	};
}

#[cfg(test)]
mod tests;
