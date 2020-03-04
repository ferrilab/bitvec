/*! Internal implementation macros for the public exports.

The macros in this module are required to be exported from the crate, as the
public macros will call them from client contexts (`macro_rules!` expansion
bodies are not in source crate scope, as they are token expansion rather than
symbolic calls). However, they are not part of the public *API* of the crate,
and are not intended for use anywhere but in the expansion bodies of the
public-API constructor macros.
!*/

#![doc(hidden)]

/// Ensures that the ordering tokens map to a known ordering type path.
#[doc(hidden)]
#[macro_export]
macro_rules! __bits_from_slice {
	(Local, $store:ident, $len:expr, $slice:ident) => {
		$crate::slice::BitSlice::<
			$crate::order::Local,
			$store,
		>::from_slice($slice)[.. $len]
	};
	(Lsb0, $store:ident, $len:expr, $slice:ident) => {
		$crate::slice::BitSlice::<
			$crate::order::Lsb0,
			$store,
		>::from_slice($slice)[.. $len]
	};
	(Msb0, $store:ident, $len:expr, $slice:ident) => {
		$crate::slice::BitSlice::<
			$crate::order::Msb0,
			$store,
		>::from_slice($slice)[.. $len]
	};
	($order:tt, $store:ident, $len:expr, $slice:ident) => {
		$crate::slice::BitSlice::<$order, $store>::from_slice($slice)[.. $len]
	};
}

/** Accumulates a stream of bit expressions into a compacted array of elements.

This macro constructs a well-ordered `[T; N]` array expression usable in `const`
contexts. Callers may then use that expression as the source slice over which to
construct `bitvec` types.
**/
#[doc(hidden)]
#[macro_export]
macro_rules! __bits_store_array {
	//  Reroute `usize` to the correct concrete type, and mark the alias.
	//  The `@ usz` causes `as usize` to be appended to exprs as needed.
	($order:tt, usize; $($val:expr),*) => {{
		const LEN: usize = $crate::store::elts::<usize>(
			$crate::__count!($($val),*),
		);

		//  Attributes are not currently allowed on expressions, only items and
		//  statements, so the routing here must bind to a name.
		#[cfg(target_pointer_width = "32")]
		const OUT: [usize; LEN] = $crate::__bits_store_array!(
			$order, u32 @ usz; $($val),*
		);

		#[cfg(target_pointer_width = "64")]
		const OUT: [usize; LEN] = $crate::__bits_store_array!(
			$order, u64 @ usz; $($val),*
		);

		OUT
	}};
	// Entry point.
	($order:tt, $store:ident $(@ $usz:ident )?; $($val:expr),*) => {
		$crate::__bits_store_array!(
			 $order, $store $(@ $usz)?, []; $($val,)*
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 16
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 32
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 48
			0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0  // 64
		);
	};

	/* NOTE: These have to be first. They (ab)use a quirk of `macro_rules!`
	where `:expr` captures are considered a single `:tt` after being matched.
	Even if the `:expr` matcher was a literal `0`, after being wrapped by the
	`:expr` fragment, it is no longer considered to match a literal `0`, so
	these patterns will only match the extra padding `0`s added at the end.

	Once the user-provided `$val` expressions are all consumed, the remaining
	`0` tokens inserted by the arm above are all removed, ensuring that the
	produced array has no wasted elements.
	*/
	($order:tt, $store:ident @ usz, [$( ($($elt:tt),*) )*]; $(0),*) => {
		[$(
			$crate::__elt_from_bits!($order, $store; $($elt),*) as usize
		),*]
	};
	($order:tt, $store:ident, [$( ($($elt:tt),*) )*]; $(0),*) => {
		[$(
			$crate::__elt_from_bits!($order, $store; $($elt),*)
		),*]
	};

	// Matchers for each size of word. The end of the word may be padded out
	// with `0`s.
	(
		$order:tt, u8 $(@ $usz:ident)?, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u8 $(@ $usz)?, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0
			)];
			$($($t)*)?
		)
	};
	(
		$order:tt, u16 $(@ $usz:ident)?, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt,
		$a1:tt, $b1:tt, $c1:tt, $d1:tt, $e1:tt, $f1:tt, $g1:tt, $h1:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u16 $(@ $usz)?, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0,
				$a1, $b1, $c1, $d1, $e1, $f1, $g1, $h1
			)];
			$($($t)*)?
		)
	};
	(
		$order:tt, u32 $(@ $usz:ident)?, [$($w:tt)*];
		$a0:tt, $b0:tt, $c0:tt, $d0:tt, $e0:tt, $f0:tt, $g0:tt, $h0:tt,
		$a1:tt, $b1:tt, $c1:tt, $d1:tt, $e1:tt, $f1:tt, $g1:tt, $h1:tt,
		$a2:tt, $b2:tt, $c2:tt, $d2:tt, $e2:tt, $f2:tt, $g2:tt, $h2:tt,
		$a3:tt, $b3:tt, $c3:tt, $d3:tt, $e3:tt, $f3:tt, $g3:tt, $h3:tt
		$(, $($t:tt)*)?
	) => {
		$crate::__bits_store_array!(
			$order, u32 $(@ $usz)?, [$($w)* (
				$a0, $b0, $c0, $d0, $e0, $f0, $g0, $h0,
				$a1, $b1, $c1, $d1, $e1, $f1, $g1, $h1,
				$a2, $b2, $c2, $d2, $e2, $f2, $g2, $h2,
				$a3, $b3, $c3, $d3, $e3, $f3, $g3, $h3
			)];
			$($($t)*)?
		)
	};
	(
		$order:tt, u64 $(@ $usz:ident)?, [$($w:tt)*];
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
			$order, u64 $(@ $usz)?, [$($w)* (
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
		)
	};
}

/// Counts the number of repetitions inside a `$()*` sequence.
#[doc(hidden)]
#[macro_export]
macro_rules! __count {
	(@ $val:expr) => {
		1
	};
	($($val:expr),*) => {{
		/* Clippy warns that `.. EXPR + 1`, for any value of `EXPR`, should be
		replaced with `..= EXPR`. This means that `.. $crate::__count!` raises
		the lint, causing `bits![(val,)…]` to have an unfixable lint warning.
		By binding to a `const`, then returning the `const`, this syntax
		construction is avoided as macros only expand to `.. LEN` rather than
		`.. 0 (+ 1)…`.
		*/
		const LEN: usize = 0usize $(+ $crate::__count!(@ $val))*;
		LEN
	}};
}

/// Construct a `T` element from an array of `u8`.
#[doc(hidden)]
#[macro_export]
macro_rules! __elt_from_bits {
	//  Known orderings can be performed immediately.
	(
		Lsb0, $store:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$crate::__ty_from_bytes!(
			Lsb0, $store, [$($crate::macros::internal::u8_from_le_bits(
				$a != 0, $b != 0, $c != 0, $d != 0,
				$e != 0, $f != 0, $g != 0, $h != 0,
			)),*]
		)
	};
	(
		Msb0, $store:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$crate::__ty_from_bytes!(
			Msb0, $store, [$($crate::macros::internal::u8_from_be_bits(
				$a != 0, $b != 0, $c != 0, $d != 0,
				$e != 0, $f != 0, $g != 0, $h != 0,
			)),*]
		)
	};
	(
		Local, $store:ident;
		$($a:tt, $b:tt, $c:tt, $d:tt, $e:tt, $f:tt, $g:tt, $h:tt),*
	) => {
		$crate::__ty_from_bytes!(
			Local, $store, [$($crate::macros::internal::u8_from_ne_bits(
				$a != 0, $b != 0, $c != 0, $d != 0,
				$e != 0, $f != 0, $g != 0, $h != 0,
			)),*]
		)
	};

	//  Unknown orders are currently unsupported in `macro_rules!`.
	($order:tt, $store:ident; $($a:tt),*) => {{
		/* Note: they can *become* supported, by adding a `ident <-` argument
		to `bits!` that allows construction of runtime values into a binding
		which outlives the returned reference without necessarily being `static`
		(which requires `const` constructors).

		The call-site syntax

		```rust
		let slab;
		let bits = bits![slab <- args…];
		```

		would construct the array literal into `slab` and then produce a
		`&BitSlice` reference from `&slab`. This works because Rust allows
		delayed initialization if there is exactly one initialization point in
		all program branch pathways. The expansion of `bits!` would be something
		like

		```rust
		let slab;
		let bits = {
			slab = __bits_store_array!($args…);
			&BitSlice::<$o, $t>::from_slice(&slab)[.. $len];
		};
		```

		The `slab` binding outlives the `bits` reference; construction of the
		`slab` value occurs at runtime in non-`const` contexts.

		This is a deferred item.
		*/
		compile_error!("The ordering argument you provided is unrecognized, \
			and as such cannot be used in const contexts.");
		let mut value: $store = 0;
		let mut _idx = 0u8;
		$(
			$crate::store::BitStore::set::<$order>(
				&mut value,
				unsafe { $crate::indices::BitIdx::new_unchecked(_idx) },
				$a != 0,
			);
			_idx += 1;
		)*
		value
	}};
}

/// Extend a single bit to fill an element.
#[doc(hidden)]
#[macro_export]
macro_rules! __extend_bool {
	($val:expr, $typ:ident) => {
		(0 as $typ).wrapping_sub(($val != 0) as $typ)
	};
}

/// Implement the shift operators on `BitSlice` with other types than `usize`.
#[doc(hidden)]
macro_rules! __bitslice_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<O, T> core::ops::ShlAssign<$t>
		for $crate::prelude::BitSlice<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shl_assign(&mut self, shamt: $t) {
				core::ops::ShlAssign::<usize>::shl_assign(
					self,
					shamt as usize,
				)
			}
		}

		#[doc(hidden)]
		impl<O, T> core::ops::ShrAssign<$t>
		for $crate::prelude::BitSlice<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shr_assign(&mut self,shamt: $t){
				core::ops::ShrAssign::<usize>::shr_assign(
					self,
					shamt as usize,
				)
			}
		}
	)+ };
}

/// Implement the shift operators on `BitVec` with other types than `usize`.
#[doc(hidden)]
#[cfg(feature = "alloc")]
macro_rules! __bitvec_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<O, T> core::ops::Shl<$t>
		for $crate::vec::BitVec<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			type Output = <Self as core::ops::Shl<usize>>::Output;

			fn shl(self, shamt: $t) -> Self::Output {
				core::ops::Shl::<usize>::shl(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<O, T> core::ops::ShlAssign<$t>
		for $crate::vec::BitVec<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shl_assign(&mut self, shamt: $t) {
				core::ops::ShlAssign::<usize>::shl_assign(
					self,
					shamt as usize,
				)
			}
		}

		#[doc(hidden)]
		impl<O, T> core::ops::Shr<$t>
		for $crate::vec::BitVec<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			type Output = <Self as core::ops::Shr<usize>>::Output;

			fn shr(self, shamt: $t) -> Self::Output {
				core::ops::Shr::<usize>::shr(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<O, T> core::ops::ShrAssign<$t>
		for $crate::vec::BitVec<O, T>
		where O: $crate::order::BitOrder, T: $crate::store::BitStore {
			fn shr_assign(&mut self, shamt: $t) {
				core::ops::ShrAssign::<usize>::shr_assign(
					self,
					shamt as usize,
				)
			}
		}
	)+ };
}

/// Constructs a fundamental integer from a list of bytes.
#[doc(hidden)]
#[macro_export]
macro_rules! __ty_from_bytes {
	(Msb0, u8, [$($byte:expr),*]) => {
		$crate::macros::internal::u8_from_be_bytes([$($byte),*])
	};
	(Lsb0, u8, [$($byte:expr),*]) => {
		$crate::macros::internal::u8_from_le_bytes([$($byte),*])
	};
	(Local, u8, [$($byte:expr),*]) => {
		$crate::macros::internal::u8_from_ne_bytes([$($byte),*])
	};
	(Msb0, u16, [$($byte:expr),*]) => {
		$crate::macros::internal::u16_from_be_bytes([$($byte),*])
	};
	(Lsb0, u16, [$($byte:expr),*]) => {
		$crate::macros::internal::u16_from_le_bytes([$($byte),*])
	};
	(Local, u16, [$($byte:expr),*]) => {
		$crate::macros::internal::u16_from_ne_bytes([$($byte),*])
	};
	(Msb0, u32, [$($byte:expr),*]) => {
		$crate::macros::internal::u32_from_be_bytes([$($byte),*])
	};
	(Lsb0, u32, [$($byte:expr),*]) => {
		$crate::macros::internal::u32_from_le_bytes([$($byte),*])
	};
	(Local, u32, [$($byte:expr),*]) => {
		$crate::macros::internal::u32_from_ne_bytes([$($byte),*])
	};
	(Msb0, u64, [$($byte:expr),*]) => {
		$crate::macros::internal::u64_from_be_bytes([$($byte),*])
	};
	(Lsb0, u64, [$($byte:expr),*]) => {
		$crate::macros::internal::u64_from_le_bytes([$($byte),*])
	};
	(Local, u64, [$($byte:expr),*]) => {
		$crate::macros::internal::u64_from_ne_bytes([$($byte),*])
	};
	(Msb0, usize, [$($byte:expr),*]) => {
		$crate::macros::internal::usize_from_be_bytes([$($byte),*])
	};
	(Lsb0, usize, [$($byte:expr),*]) => {
		$crate::macros::internal::usize_from_le_bytes([$($byte),*])
	};
	(Local, usize, [$($byte:expr),*]) => {
		$crate::macros::internal::usize_from_ne_bytes([$($byte),*])
	};
}

/// Construct a `u8` from bits applied in Lsb0-order.
#[allow(clippy::many_single_char_names)]
#[allow(clippy::too_many_arguments)]
pub const fn u8_from_le_bits(
	a: bool,
	b: bool,
	c: bool,
	d: bool,
	e: bool,
	f: bool,
	g: bool,
	h: bool,
) -> u8 {
	(a as u8)
		| ((b as u8) << 1)
		| ((c as u8) << 2)
		| ((d as u8) << 3)
		| ((e as u8) << 4)
		| ((f as u8) << 5)
		| ((g as u8) << 6)
		| ((h as u8) << 7)
}

/// Construct a `u8` from bits applied in Msb0-order.
#[allow(clippy::many_single_char_names)]
#[allow(clippy::too_many_arguments)]
pub const fn u8_from_be_bits(
	a: bool,
	b: bool,
	c: bool,
	d: bool,
	e: bool,
	f: bool,
	g: bool,
	h: bool,
) -> u8 {
	(h as u8)
		| ((g as u8) << 1)
		| ((f as u8) << 2)
		| ((e as u8) << 3)
		| ((d as u8) << 4)
		| ((c as u8) << 5)
		| ((b as u8) << 6)
		| ((a as u8) << 7)
}

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use self::u8_from_le_bits as u8_from_ne_bits;

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use self::u8_from_be_bits as u8_from_ne_bits;

#[doc(hidden)]
pub const fn u8_from_be_bytes(bytes: [u8; 1]) -> u8 {
	bytes[0]
}

#[doc(hidden)]
pub const fn u8_from_le_bytes(bytes: [u8; 1]) -> u8 {
	bytes[0]
}

#[doc(hidden)]
pub const fn u16_from_be_bytes(bytes: [u8; 2]) -> u16 {
	((bytes[0] as u16) << 8) | bytes[1] as u16
}

#[doc(hidden)]
pub const fn u16_from_le_bytes(bytes: [u8; 2]) -> u16 {
	((bytes[1] as u16) << 8) | bytes[0] as u16
}

#[doc(hidden)]
pub const fn u32_from_be_bytes(bytes: [u8; 4]) -> u32 {
	(u16_from_be_bytes([bytes[0], bytes[1]]) as u32) << 16
		| u16_from_be_bytes([bytes[2], bytes[3]]) as u32
}

#[doc(hidden)]
pub const fn u32_from_le_bytes(bytes: [u8; 4]) -> u32 {
	(u16_from_le_bytes([bytes[2], bytes[3]]) as u32) << 16
		| u16_from_le_bytes([bytes[0], bytes[1]]) as u32
}

#[doc(hidden)]
pub const fn u64_from_be_bytes(bytes: [u8; 8]) -> u64 {
	(u32_from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64) << 32
		| (u32_from_be_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]) as u64)
}

#[doc(hidden)]
pub const fn u64_from_le_bytes(bytes: [u8; 8]) -> u64 {
	(u32_from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]) as u64) << 32
		| u32_from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as u64
}

#[doc(hidden)]
#[cfg(target_pointer_width = "32")]
pub const fn usize_from_be_bytes(bytes: [u8; 4]) -> usize {
	u32_from_be_bytes(bytes) as usize
}

#[doc(hidden)]
#[cfg(target_pointer_width = "32")]
pub const fn usize_from_le_bytes(bytes: [u8; 4]) -> usize {
	u32_from_le_bytes(bytes) as usize
}

#[doc(hidden)]
#[cfg(target_pointer_width = "64")]
pub const fn usize_from_be_bytes(bytes: [u8; 8]) -> usize {
	u64_from_be_bytes(bytes) as usize
}

#[doc(hidden)]
#[cfg(target_pointer_width = "64")]
pub const fn usize_from_le_bytes(bytes: [u8; 8]) -> usize {
	u64_from_le_bytes(bytes) as usize
}

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use u8_from_be_bytes as u8_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use u16_from_be_bytes as u16_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use u32_from_be_bytes as u32_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use u64_from_be_bytes as u64_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "big")]
pub use usize_from_be_bytes as usize_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use u8_from_le_bytes as u8_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use u16_from_le_bytes as u16_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use u32_from_le_bytes as u32_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use u64_from_le_bytes as u64_from_ne_bytes;

#[doc(hidden)]
#[cfg(target_endian = "little")]
pub use usize_from_le_bytes as usize_from_ne_bytes;
