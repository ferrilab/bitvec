/*! Utility macros for constructing data structures and implementing bulk types.

The only public macro is `bitvec`; this module also provides convenience macros
for code generation.
!*/

/** Construct a `BitVec` out of a literal array in source code, like `vec!`.

`bitvec!` can be invoked in a number of ways. It takes the name of a `Cursor`
implementation, the name of a `Bits`-implementing fundamental, and zero or more
fundamentals (integer, floating-point, or boolean) which are used to build the
bits. Each fundamental literal corresponds to one bit, and is considered to
represent `1` if it is any other value than exactly zero.

`bitvec!` can be invoked with no specifiers, a `Cursor` specifier, or a `Cursor`
and a `Bits` specifier. It cannot be invoked with a `Bits` specifier but no
`Cursor` specifier, due to overlap in how those tokens are matched by the macro
system.

Like `vec!`, `bitvec!` supports bit lists `[0, 1, …]` and repetition markers
`[1; n]`.

# Examples

```rust
use bitvec::prelude::*;

bitvec![BigEndian, u8; 0, 1];
bitvec![LittleEndian, u8; 0, 1,];
bitvec![BigEndian; 0, 1];
bitvec![LittleEndian; 0, 1,];
bitvec![0, 1];
bitvec![0, 1,];
bitvec![BigEndian, u8; 1; 5];
bitvec![LittleEndian; 0; 5];
bitvec![1; 5];
```
**/
#[cfg(any(feature = "alloc", feature = "std"))]
#[macro_export]
macro_rules! bitvec {
	//  bitvec![ endian , type ; 0 , 1 , … ]
	( $endian:path , $bits:ty ; $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $( $element ),* ]
	};
	//  bitvec![ endian , type ; 0 , 1 , … , ]
	( $endian:path , $bits:ty ; $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $( $element ),* ]
	};

	//  bitvec![ endian ; 0 , 1 , … ]
	( $endian:path ; $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $( $element ),* ]
	};
	//  bitvec![ endian ; 0 , 1 , … , ]
	( $endian:path ; $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $( $element ),* ]
	};

	//  bitvec![ 0 , 1 , … ]
	( $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ $crate::prelude::BigEndian , u8 ; $( $element ),* ]
	};
	//  bitvec![ 0 , 1 , … , ]
	( $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ $crate::prelude::BigEndian , u8 ; $( $element ),* ]
	};

	//  bitvec![ endian , type ; bit ; rep ]
	( $endian:path , $bits:ty ; $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $element; $rep ]
	};
	//  bitvec![ endian ; bit ; rep ]
	( $endian:path ; $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $element ; $rep ]
	};
	//  bitvec![ bit ; rep ]
	( $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $crate::prelude::BigEndian , u8 ; $element ; $rep ]
	};

	//  Build an array of `bool` (one bit per byte) and then build a `BitVec`
	//  from that (one bit per bit). I have yet to think of a way to make the
	//  source array be binary-compatible with a `BitSlice` data representation,
	//  so the static source is 8x larger than it needs to be.
	//
	//  I’m sure there is a way, but I don’t think I need to spend the effort
	//  yet. Maybe a proc-macro.

	( __bv_impl__ $endian:path , $bits:ty ; $( $element:expr ),* ) => {{
		let init: &[bool] = &[ $( $element != 0 ),* ];
		$crate :: vec :: BitVec :: < $endian , $bits > :: from ( init )
	}};

	( __bv_impl__ $endian:path , $bits:ty ; $element:expr ; $rep:expr ) => {{
		core :: iter :: repeat ( $element != 0 )
			.take ( $rep )
			.collect :: < $crate :: vec :: BitVec < $endian , $bits > > ( )
	}};
}

/** Construct a `BitBox` out of a literal array in source code, like `bitvec!`.

This has exactly the same syntax as [`bitvec!`], and in fact is a thin wrapper
around `bitvec!` that calls `.into_boxed_slice()` on the produced `BitVec` to
freeze it.

[`bitvec!`]: #macro.bitvec
**/
#[cfg(any(feature = "alloc", feature = "std"))]
#[macro_export]
macro_rules! bitbox {
	//  bitbox![ endian , type ; 0 , 1 , … ]
	( $endian:path , $bits:ty ; $( $element:expr ),* ) => {
		bitvec![ $endian , $bits ; $( $element ),* ].into_boxed_bitslice()
	};
	//  bitbox![ endian , type ; 0 , 1 , … , ]
	( $endian:path , $bits:ty ; $( $element:expr , )* ) => {
		bitvec![ $endian , $bits ; $( $element ),* ].into_boxed_bitslice()
	};

	//  bitbox![ endian ; 0 , 1 , … ]
	( $endian:path ; $( $element:expr ),* ) => {
		bitvec![ $endian , u8 ; $( $element ),* ].into_boxed_bitslice()
	};
	//  bitbox![ endian ; 0 , 1 , … , ]
	( $endian:path ; $( $element:expr , )* ) => {
		bitvec![ $endian , u8 ; $( $element ),* ].into_boxed_bitslice()
	};

	//  bitbox![ 0 , 1 , … ]
	( $( $element:expr ),* ) => {
		bitvec![ $crate::prelude::BigEndian , u8 ; $( $element ),* ].into_boxed_bitslice()
	};
	//  bitbox![ 0 , 1 , … , ]
	( $( $element:expr , )* ) => {
		bitvec![ $crate::prelude::BigEndian , u8 ; $( $element ),* ].into_boxed_bitslice()
	};

	//  bitbox![ endian , type ; bit ; rep ]
	( $endian:path , $bits:ty ; $element:expr ; $rep:expr ) => {
		bitvec![ $endian , $bits ; $element; $rep ].into_boxed_bitslice()
	};
	//  bitbox![ endian ; bit ; rep ]
	( $endian:path ; $element:expr ; $rep:expr ) => {
		bitvec![ $endian , u8 ; $element ; $rep ].into_boxed_bitslice()
	};
	//  bitbox![ bit ; rep ]
	( $element:expr ; $rep:expr ) => {
		bitvec![ $crate::prelude::BigEndian , u8 ; $element ; $rep ].into_boxed_bitslice()
	};
}

#[doc(hidden)]
macro_rules! __bitslice_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl < C , T > core :: ops :: ShlAssign < $t >
		for $crate :: prelude :: BitSlice < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			fn shl_assign ( & mut self , shamt : $t ) {
				core :: ops :: ShlAssign :: < usize > :: shl_assign (
					self ,
					shamt as usize ,
				)
			}
		}

		#[doc(hidden)]
		impl < C , T > core :: ops :: ShrAssign < $t >
		for $crate :: prelude :: BitSlice < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			fn shr_assign ( & mut self , shamt : $t ) {
				core :: ops :: ShrAssign :: < usize > :: shr_assign (
					self,
					shamt as usize ,
				)
			}
		}
	)+ };
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[doc(hidden)]
macro_rules! __bitvec_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl < C , T > core :: ops :: Shl < $t >
		for $crate :: vec :: BitVec < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			type Output = < Self as core :: ops :: Shl < usize > > :: Output ;

			fn shl ( self , shamt : $t ) -> Self :: Output {
				core :: ops :: Shl :: < usize > :: shl ( self , shamt as usize )
			}
		}

		#[doc(hidden)]
		impl < C , T > core :: ops :: ShlAssign < $t >
		for $crate :: vec :: BitVec < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			fn shl_assign ( & mut self , shamt : $t ) {
				core :: ops :: ShlAssign :: < usize > :: shl_assign (
					self ,
					shamt as usize,
				)
			}
		}

		#[doc(hidden)]
		impl < C , T > core :: ops :: Shr < $t >
		for $crate :: vec :: BitVec < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			type Output = < Self as core :: ops :: Shr < usize > > :: Output ;

			fn shr ( self , shamt : $t ) -> Self :: Output {
				core :: ops :: Shr :: < usize > :: shr ( self , shamt as usize )
			}
		}

		#[doc(hidden)]
		impl < C , T> core :: ops :: ShrAssign < $t >
		for $crate :: vec :: BitVec < C , T >
		where C : $crate :: cursor :: Cursor , T : $crate :: bits :: Bits {
			fn shr_assign ( & mut self , shamt : $t ) {
				core :: ops :: ShrAssign :: < usize > :: shr_assign (
					self ,
					shamt as usize ,
				)
			}
		}
	)+ };
}

#[cfg(all(test, any(feature = "alloc", feature = "std")))]
mod tests {
	#[allow(unused_imports)]
	use crate::cursor::{
		BigEndian,
		LittleEndian,
	};

	#[test]
	fn compile_bitvec_macros() {
		bitvec![0, 1];
		bitvec![BigEndian; 0, 1];
		bitvec![LittleEndian; 0, 1];
		bitvec![BigEndian, u8; 0, 1];
		bitvec![LittleEndian, u8; 0, 1];
		bitvec![BigEndian, u16; 0, 1];
		bitvec![LittleEndian, u16; 0, 1];
		bitvec![BigEndian, u32; 0, 1];
		bitvec![LittleEndian, u32; 0, 1];
		bitvec![BigEndian, u64; 0, 1];
		bitvec![LittleEndian, u64; 0, 1];

		bitvec![1; 70];
		bitvec![BigEndian; 0; 70];
		bitvec![LittleEndian; 1; 70];
		bitvec![BigEndian, u8; 0; 70];
		bitvec![LittleEndian, u8; 1; 70];
		bitvec![BigEndian, u16; 0; 70];
		bitvec![LittleEndian, u16; 1; 70];
		bitvec![BigEndian, u32; 0; 70];
		bitvec![LittleEndian, u32; 1; 70];
		bitvec![BigEndian, u64; 0; 70];
		bitvec![LittleEndian, u64; 1; 70];
	}

	#[test]
	fn compile_bitbox_macros() {
		bitbox![0, 1];
		bitbox![BigEndian; 0, 1];
		bitbox![LittleEndian; 0, 1];
		bitbox![BigEndian, u8; 0, 1];
		bitbox![LittleEndian, u8; 0, 1];
		bitbox![BigEndian, u16; 0, 1];
		bitbox![LittleEndian, u16; 0, 1];
		bitbox![BigEndian, u32; 0, 1];
		bitbox![LittleEndian, u32; 0, 1];
		bitbox![BigEndian, u64; 0, 1];
		bitbox![LittleEndian, u64; 0, 1];

		bitbox![1; 70];
		bitbox![BigEndian; 0; 70];
		bitbox![LittleEndian; 1; 70];
		bitbox![BigEndian, u8; 0; 70];
		bitbox![LittleEndian, u8; 1; 70];
		bitbox![BigEndian, u16; 0; 70];
		bitbox![LittleEndian, u16; 1; 70];
		bitbox![BigEndian, u32; 0; 70];
		bitbox![LittleEndian, u32; 1; 70];
		bitbox![BigEndian, u64; 0; 70];
		bitbox![LittleEndian, u64; 1; 70];
	}
}
