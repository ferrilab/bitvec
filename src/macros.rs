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
	(for $len:expr, in $order:ty, $store:ty $(,)?) => {
		$crate::array::BitArray::<
			$order, [$store; $crate::mem::elts::<$store>($len)]
		>
	};

	(for $len:expr, in $store:ty $(,)?) => {
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

## `const` Production

Prepending the argument list with `const` (so `bitarr!(ARGS…)` becomes
`bitarr!(const ARGS…)`) causes the macro to only expand to code that can be used
in `const` contexts. This limits any supplied ordering to be **only** the tokens
`Lsb0`, `Msb0`, and `LocalBits`; no other token is permitted, even if the token
resolves to the same ordering implementation.

The macro expands into code that can be used to initialize a `const` or `static`
binding. This is the **only** way to construct a `BitArray` in `const` contexts,
until the `const` system permits generics and trait methods.

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
	/* `const`-expression constructors.

	These arms expand to expressions which are valid to use in `const` position,
	such as within `const fn` bodies, or as the initializers of `static` or
	`const` bindings.

	They are more restricted than the general variants below, because the trait
	system is not usable in `const` contexts and thus these expansions can only
	use codepaths defined within this module, and not any of the general crate
	systems.

	All valid invocations with a leading `const` token will remain valid if the
	`const` is removed, though their expansion may cease to be valid in `const`
	contexts.
	*/
	(const $order:ty, $store:ty; $val:expr; $len:expr) => {{
		use $crate::macros::internal::core;
		type Mem = <$store as $crate::store::BitStore>::Mem;

		const ELTS: usize = $crate::mem::elts::<$store>($len);
		const ELEM: Mem = $crate::__extend_bool!($val, $store);
		const DATA: [Mem; ELTS] = [ELEM; ELTS];

		type This = $crate::array::BitArray<$order, [$store; ELTS]>;
		unsafe { core::mem::transmute::<_, This>(DATA) }
	}};
	(const $val:expr; $len:expr) => {{
		$crate::bitarr!(const $crate::order::Lsb0, usize; $val; $len)
	}};

	(const $order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;

		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type Data = [$store; ELTS];
		const DATA: Data = $crate::__encode_bits!($order, $store; $($val),*);

		type This = $crate::array::BitArray<$order, [Celled; ELTS]>;
		unsafe { core::mem::transmute::<_, This>(DATA) }
	}};
	(const $order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;

		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type Data = [$store; ELTS];
		const DATA: Data = $crate::__encode_bits!($order, $store; $($val),*);

		type This = $crate::array::BitArray<$order, Data>;
		unsafe { core::mem::transmute::<_, This>(DATA) }
	}};

	(const $($val:expr),* $(,)?) => {{
		$crate::bitarr!(const Lsb0, usize; $($val),*)
	}};

	/* Non-`const` constructors.

	These expansions are allowed to produce that does not run in `const`
	contexts. While it is *likely* that the expansions will be evaluated at
	compile-time, this is done in LLVM, not in Rust MIR.
	*/

	//  Bit-repetition syntax.
	($order:ty, $store:ty; $val:expr; $len:expr) => {{
		$crate::bitarr!(const $order, $store; $val; $len)
	}};
	($val:expr; $len:expr) => {{
		$crate::bitarr!(const $val; $len)
	}};

	//  Bit-sequence syntax.

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

	($order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;

		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type Data = [Celled; ELTS];
		type This = $crate::array::BitArray<$order, Data>;

		This::new($crate::__encode_bits!($order, Cell<$store>; $($val),*))
	}};
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type This = $crate::array::BitArray<$order, [$store; ELTS]>;

		This::new($crate::__encode_bits!($order, $store; $($val),*))
	}};

	($order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;

		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type This = $crate::array::BitArray<$order, [Celled; ELTS]>;

		This::new($crate::__encode_bits!($order, Cell<$store>; $($val),*))
	}};
	($order:path, $store:ident; $($val:expr),* $(,)?) => {{
		const ELTS: usize = $crate::__count_elts!($store; $($val),*);
		type This = $crate::array::BitArray<$order, [$store; ELTS]>;

		This::new($crate::__encode_bits!($order, $store; $($val),*))
	}};

	($($val:expr),* $(,)?) => {
		$crate::bitarr!(Lsb0, usize; $($val),*)
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

## `static` Production

Prepending the argument list with `static` or `static mut` (so `bits!(ARGS…)`
becomes `bits!(static [mut] ARGS…)`) causes the macro to expand to code that
emits a hidden `static` or `static mut` value, initialized with a
`bitarr!(const ARGS…)` expansion and then reborrowed. The name of the hidden
static object does not escape the macro invocation, and so the returned
`BitSlice` handle is the single point of access to it.

Because both indexing and mutable reborrows are forbidden in `const` contexts,
the produced `BitSlice` references can only be bound to `let`, not to `static`.
They have the `&'static` lifetime, but to give the *names* a `static` binding,
you must use `bitarr!(const ARGS…)` and then borrowed as a `BitSlice` at the
point of use.

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
	(static mut $order:ty, Cell<$store:ident>; $val:expr; $len:expr) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;
		static mut DATA: $crate::BitArr!(for $len, in $order, $store) =
			$crate::bitarr!(const $order, $store; $val; $len);
		unsafe {
			&mut *(
				DATA.get_unchecked_mut(.. $len)
					as *mut $crate::slice::BitSlice<$order, $store>
					as *mut $crate::slice::BitSlice<$order, Celled>
			)
		}
	}};
	(static mut $order:ty, $store:ident; $val:expr; $len:expr) => {{
		static mut DATA: $crate::BitArr!(for $len, in $order, $store) =
			$crate::bitarr!(const $order, $store; $val; $len);
		unsafe { DATA.get_unchecked_mut(.. $len) }
	}};
	(static mut $val:expr; $len:expr) => {{
		static mut DATA: $crate::BitArr!(for $len) =
			$crate::bitarr!(const $crate::order::Lsb0, usize; $val; $len);
		unsafe { DATA.get_unchecked_mut(.. $len) }
	}};

	(static mut $order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;
		const BITS: usize = $crate::__count!($($val),*);

		static mut DATA: $crate::BitArr!(for BITS, in $order, $store) =
			$crate::bitarr!(const $order, $store; $($val),*);
		unsafe {
			&mut *(
				DATA.get_unchecked_mut(.. BITS)
					as *mut $crate::slice::BitSlice<$order, $store>
					as *mut $crate::slice::BitSlice<$order, Celled>
			)
		}
	}};
	(static mut $order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		static mut DATA: $crate::BitArr!(for BITS, in $order, $store) =
			$crate::bitarr!(const $order, $store; $($val),*);
		unsafe { DATA.get_unchecked_mut(.. BITS) }
	}};
	(static mut $($val:expr),* $(,)?) => {{
		$crate::bits!(static mut Lsb0, usize; $($val),*)
	}};

	(static $order:ty, Cell<$store:ident>; $val:expr; $len:expr) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;
		static DATA: $crate::BitArr!(for $len, in $order, $store) =
			$crate::bitarr!(const $order, $store; $val; $len);
		unsafe {
			&*(
				DATA.get_unchecked(.. $len)
					as *const $crate::slice::BitSlice<$order, $store>
					as *const $crate::slice::BitSlice<$order, Celled>
			)
		}
	}};
	(static $order:ty, $store:ident; $val:expr; $len:expr) => {{
		static DATA: $crate::BitArr!(for $len, in $order, $store) =
			$crate::bitarr!(const $order, $store; $val; $len);
		unsafe { DATA.get_unchecked(.. $len) }
	}};
	(static $val:expr; $len:expr) => {{
		static DATA: $crate::BitArr!(for $len) =
			$crate::bitarr!(const $crate::order::Lsb0, usize; $val; $len);
		unsafe { DATA.get_unchecked(.. $len) }
	}};

	(static $order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		use $crate::macros::internal::core;
		type Celled = core::cell::Cell<$store>;
		const BITS: usize = $crate::__count!($($val),*);

		static mut DATA: $crate::BitArr!(for BITS, in $order, $store) =
			$crate::bitarr!(const $order, $store; $($val),*);
		unsafe {
			&*(
				DATA.get_unchecked_mut(.. BITS)
					as *const $crate::slice::BitSlice<$order, $store>
					as *const $crate::slice::BitSlice<$order, Celled>
			)
		}
	}};
	(static $order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		static DATA: $crate::BitArr!(for BITS, in $order, $store) =
			$crate::bitarr!(const $order, $store; $($val),*);
		unsafe { DATA.get_unchecked(.. BITS) }
	}};
	(static $($val:expr),* $(,)?) => {{
		$crate::bits!(static Lsb0, usize; $($val),*)
	}};

	//  Repetition syntax `[bit ; count]`.
	//  NOTE: `count` must be a `const`, as this is a non-allocating macro.

	//  Explicit order and store.
	(mut $order:ty, $store:ty; $val:expr; $len:expr) => {{
		&mut $crate::bitarr!($order, $store; $val; $len)[.. $len]
	}};
	//  Default order and store.
	(mut $val:expr; $len:expr) => {
		$crate::bits!(mut $crate::order::Lsb0, usize; $val; $len)
	};

	//  Sequence syntax `[bit (, bit)*]` or `[(bit ,)*]`.

	//  Explicit order and store.

	(mut $order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&mut $crate::bitarr!($order, Cell<$store>; $($val),*)[.. BITS]
	}};
	(mut $order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&mut $crate::bitarr!($order, $store; $($val),*)[.. BITS]
	}};

	(mut $order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&mut $crate::bitarr!($order, Cell<$store>; $($val),*)[.. BITS]
	}};
	(mut $order:path, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&mut $crate::bitarr!($order, $store; $($val),*)[.. BITS]
	}};

	//  Default order and store.
	(mut $($val:expr),* $(,)?) => {
		$crate::bits!(mut Lsb0, usize; $($val),*)
	};

	//  Repeat everything from above, but now immutable.

	($order:ty, $store:ty; $val:expr; $len:expr) => {{
		&$crate::bitarr!($order, $store; $val; $len)[.. $len]
	}};
	($val:expr; $len:expr) => {
		$crate::bits!($crate::order::Lsb0, usize; $val; $len)
	};

	($order:ident, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&$crate::bitarr!($order, Cell<$store>; $($val),*)[.. BITS]
	}};
	($order:ident, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&$crate::bitarr!($order, $store; $($val),*)[.. BITS]
	}};

	($order:path, Cell<$store:ident>; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&$crate::bitarr!($order, Cell<$store>; $($val),*)[.. BITS]
	}};
	($order:path, $store:ident; $($val:expr),* $(,)?) => {{
		const BITS: usize = $crate::__count!($($val),*);
		&$crate::bitarr!($order, $store; $($val),*)[.. BITS]
	}};

	//  Default order and store.
	($($val:expr),* $(,)?) => {
		$crate::bits!(Lsb0, usize; $($val),*)
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
	($order:ty, $store:ty; $val:expr; $len:expr) => {
		$crate::vec::BitVec::<$order, $store>::repeat($val != 0, $len)
	};

	($val:expr; $len:expr) => {
		$crate::bitvec!($crate::order::Lsb0, usize; $val; $len)
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
