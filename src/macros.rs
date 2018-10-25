/** Construct a `BitVec` out of a literal array in source code, like `vec!`.

`bitvec!` can be invoked in a number of ways. It takes the name of an
`Endian` implementation, the name of a `Bits`-implementing primitive, and
zero or more primitives (integer, floating-point, or bool) which are used to
build the bits. Each primitive literal corresponds to one bit, and is
considered to represent `1` if it is any other value than exactly zero.

`bitvec!` can be invoked with no specifiers, an `Endian` specifier, or an
`Endian` and a `Bits` specifier. It cannot be invoked with a `Bits`
specifier but no `Endian` specifier, due to overlap in how those tokens are
matched by the macro system.

Like `vec!`, `bitvec!` supports bit lists `[0, 1, …]` and repetition
markers `[1; n]`.

# All Syntaxes

```rust
# use bitvec::*;
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
#[macro_export]
macro_rules! bitvec {
	//  bitvec![endian, type ; 0, 1, …]
	( $endian:ident , $bits:ty ; $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $( $element ),* ]
	};
	//  bitvec![endian, type ; 0, 1, …, ]
	( $endian:ident , $bits:ty ; $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $( $element ),* ]
	};

	//  bitvec![endian ; 0, 1, …]
	( $endian:ident ; $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $( $element ),* ]
	};
	//  bitvec![endian ; 0, 1, …, ]
	( $endian:ident ; $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $( $element ),* ]
	};

	//  bitvec![0, 1, …]
	( $( $element:expr ),* ) => {
		bitvec![ __bv_impl__ BigEndian , u8 ; $($element),* ]
	};
	//  bitvec![0, 1, …, ]
	( $( $element:expr , )* ) => {
		bitvec![ __bv_impl__ BigEndian , u8 ; $($element),* ]
	};

	//  bitvec![endian, type; bit; rep]
	( $endian:ident , $bits:ty ; $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $endian , $bits ; $element; $rep ]
	};

	//  bitvec![endian; bit; rep]
	( $endian:ident ; $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ $endian , u8 ; $element; $rep ]
	};

	//  bitvec![bit; rep]
	( $element:expr ; $rep:expr ) => {
		bitvec![ __bv_impl__ BigEndian , u8 ; $element; $rep ]
	};

	//  Build an array of `bool` (one bit per byte) and then build a `BitVec`
	//  from that (one bit per bit). I have yet to think of a way to make the
	//  source array be binary-compatible with a `BitVec` representation, so the
	//  static source is 8x larger than it needs to be.
	//
	//  I'm sure there is a way, but I don’t think I need to spend the effort
	//  yet.

	( __bv_impl__ $endian:ident , $bits:ty ; $( $element:expr ),* ) => {{
		let init: &[bool] = &[
			$( $element as u8 > 0 ),*
		];
		$crate :: BitVec ::< $endian , $bits >:: from(init)
	}};

	( __bv_impl__ $endian:ident , $bits:ty ; $element:expr; $rep:expr ) => {{
		std::iter::repeat( $element as u8 > 0 )
			.take( $rep )
			.collect ::< $crate :: BitVec < $endian , $bits > > ()
	}};
}

#[doc(hidden)]
macro_rules! __bitslice_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::ShlAssign< $t >
		for crate::BitSlice<E, T>
		{
			fn shl_assign(&mut self, shamt: $t ) {
				std::ops::ShlAssign::<usize>::shl_assign(self, shamt as usize);
			}
		}

		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::ShrAssign< $t >
		for crate::BitSlice<E, T>
		{
			fn shr_assign(&mut self, shamt: $t ) {
				std::ops::ShrAssign::<usize>::shr_assign(self, shamt as usize);
			}
		}
	)+ };
}

#[doc(hidden)]
macro_rules! __bitvec_shift {
	( $( $t:ty ),+ ) => { $(
		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::Shl< $t >
		for $crate :: BitVec<E, T>
		{
			type Output = <Self as std::ops::Shl<usize>>::Output;

			fn shl(self, shamt: $t ) -> Self::Output {
				std::ops::Shl::<usize>::shl(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::ShlAssign< $t >
		for $crate :: BitVec<E, T>
		{
			fn shl_assign(&mut self, shamt: $t ) {
				std::ops::ShlAssign::<usize>::shl_assign(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::Shr< $t >
		for $crate :: BitVec<E, T>
		{
			type Output = <Self as std::ops::Shr<usize>>::Output;

			fn shr(self, shamt: $t ) -> Self::Output {
				std::ops::Shr::<usize>::shr(self, shamt as usize)
			}
		}

		#[doc(hidden)]
		impl<E: $crate :: Endian, T: $crate :: Bits> std::ops::ShrAssign< $t >
		for $crate :: BitVec<E, T>
		{
			fn shr_assign(&mut self, shamt: $t ) {
				std::ops::ShrAssign::<usize>::shr_assign(self, shamt as usize)
			}
		}
	)+ };
}

#[cfg(test)]
mod tests {
	#[allow(unused_imports)]
	use {
		BigEndian,
		LittleEndian,
	};

	#[test]
	fn compile_macros() {
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
}
