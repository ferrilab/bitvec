/*! Utility macros for constructing data structures and implementing bulk types.

The only public macro is `bitvec`; this module also provides convenience macros
for code generation.
!*/

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
	//  bitvec![ endian , type ; 0 , 1 , … ]
	( $order:path , $bits:ty ; $( $val:expr ),* ) => {
		bitvec![ __bv_impl__ $order , $bits ; $( $val ),* ]
	};
	//  bitvec![ endian , type ; 0 , 1 , … , ]
	( $order:path , $bits:ty ; $( $val:expr , )* ) => {
		bitvec![ __bv_impl__ $order , $bits ; $( $val ),* ]
	};

	//  bitvec![ endian ; 0 , 1 , … ]
	( $order:path ; $( $val:expr ),* ) => {
		bitvec![ __bv_impl__ $order , $crate::store::Word ; $( $val ),* ]
	};
	//  bitvec![ endian ; 0 , 1 , … , ]
	( $order:path ; $( $val:expr , )* ) => {
		bitvec![ __bv_impl__ $order , $crate::store::Word ; $( $val ),* ]
	};

	//  bitvec![ 0 , 1 , … ]
	( $( $val:expr ),* ) => {
		bitvec![ __bv_impl__ $crate::order::Local , $crate::store::Word ; $( $val ),* ]
	};
	//  bitvec![ 0 , 1 , … , ]
	( $( $val:expr , )* ) => {
		bitvec![ __bv_impl__ $crate::order::Local , $crate::store::Word ; $( $val ),* ]
	};

	//  bitvec![ endian , type ; bit ; rep ]
	( $order:path , $bits:ty ; $val:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $order , $bits ; $val; $rep ]
	};
	//  bitvec![ endian ; bit ; rep ]
	( $order:path ; $val:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $order , $crate::store::Word ; $val ; $rep ]
	};
	//  bitvec![ bit ; rep ]
	( $val:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $crate::order::Local , $crate::store::Word ; $val ; $rep ]
	};

	//  GitHub issue #25 is to make this into a proc-macro that produces the
	//  correct memory slab at compile time.

	( __bv_impl__ $order:path , $bits:ty ; $( $val:expr ),* ) => {{
		let init: &[bool] = &[ $( $val != 0 ),* ];
		let mut bv = $crate::vec::BitVec::<$order, $bits>::with_capacity(
			init.len(),
		);
		bv.extend(init.iter().copied());
		bv
	}};

	//  `[$val; $rep]` can just allocate a slab of at least `$rep` bits and then
	//  use `.set_all` to force them to `$val`. This is much faster than
	//  collecting from a bitstream.

	( __bv_impl__ $order:path , $bits:ty ; $val:expr ; $rep:expr ) => {{
		let mut bv = $crate::vec::BitVec::<$order, $bits>::with_capacity($rep);
		bv.set_elements(0);
		unsafe { bv.set_len($rep); }
		let one = $val != 0;
		if one {
			bv.set_all(one);
		}
		bv
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
	//  bitbox![ endian , type ; 0 , 1 , … ]
	( $order:path , $bits:ty ; $( $val:expr ),* ) => {
		bitvec![ $order , $bits ; $( $val ),* ].into_boxed_bitslice()
	};
	//  bitbox![ endian , type ; 0 , 1 , … , ]
	( $order:path , $bits:ty ; $( $val:expr , )* ) => {
		bitvec![ $order , $bits ; $( $val ),* ].into_boxed_bitslice()
	};

	//  bitbox![ endian ; 0 , 1 , … ]
	( $order:path ; $( $val:expr ),* ) => {
		bitvec![ $order , $crate::store::Word ; $( $val ),* ].into_boxed_bitslice()
	};
	//  bitbox![ endian ; 0 , 1 , … , ]
	( $order:path ; $( $val:expr , )* ) => {
		bitvec![ $order , $crate::store::Word ; $( $val ),* ].into_boxed_bitslice()
	};

	//  bitbox![ 0 , 1 , … ]
	( $( $val:expr ),* ) => {
		bitvec![ $crate::order::Local , $crate::store::Word ; $( $val ),* ].into_boxed_bitslice()
	};
	//  bitbox![ 0 , 1 , … , ]
	( $( $val:expr , )* ) => {
		bitvec![ $crate::order::Local , $crate::store::Word ; $( $val ),* ].into_boxed_bitslice()
	};

	//  bitbox![ endian , type ; bit ; rep ]
	( $order:path , $bits:ty ; $val:expr ; $rep:expr ) => {
		bitvec![ $order , $bits ; $val; $rep ].into_boxed_bitslice()
	};
	//  bitbox![ endian ; bit ; rep ]
	( $order:path ; $val:expr ; $rep:expr ) => {
		bitvec![ $order , $crate::store::Word ; $val ; $rep ].into_boxed_bitslice()
	};
	//  bitbox![ bit ; rep ]
	( $val:expr ; $rep:expr ) => {
		bitvec![ $crate::order::Local , $crate::store::Word ; $val ; $rep ].into_boxed_bitslice()
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

#[cfg(all(test, feature = "alloc"))]
mod tests {
	#[allow(unused_imports)]
	use crate::order::{
		Msb0,
		Lsb0,
	};

	#[test]
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
		bitvec![Msb0, u64; 0, 1];
		bitvec![Lsb0, u64; 0, 1];

		bitvec![1; 70];
		bitvec![Msb0; 0; 70];
		bitvec![Lsb0; 1; 70];
		bitvec![Msb0, u8; 0; 70];
		bitvec![Lsb0, u8; 1; 70];
		bitvec![Msb0, u16; 0; 70];
		bitvec![Lsb0, u16; 1; 70];
		bitvec![Msb0, u32; 0; 70];
		bitvec![Lsb0, u32; 1; 70];
		bitvec![Msb0, u64; 0; 70];
		bitvec![Lsb0, u64; 1; 70];
	}

	#[test]
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
		bitbox![Msb0, u64; 0, 1];
		bitbox![Lsb0, u64; 0, 1];

		bitbox![1; 70];
		bitbox![Msb0; 0; 70];
		bitbox![Lsb0; 1; 70];
		bitbox![Msb0, u8; 0; 70];
		bitbox![Lsb0, u8; 1; 70];
		bitbox![Msb0, u16; 0; 70];
		bitbox![Lsb0, u16; 1; 70];
		bitbox![Msb0, u32; 0; 70];
		bitbox![Lsb0, u32; 1; 70];
		bitbox![Msb0, u64; 0; 70];
		bitbox![Lsb0, u64; 1; 70];
	}
}
