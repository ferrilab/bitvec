#[macro_export]
macro_rules! bitvec {
	//  TODO: Refine these to make an array of bool and then iterate through it.
	//  bitvec![BigEndian, type, 0, 1, ...]
	( BigEndian, $prim:ty, $($elt:expr),* ) => {
		bitvec![ BigEndian, $prim, $( $elt , )* ]
	};
	//  bitvec![Little, type, 0, 1, ...]
	( LittleEndian, $prim:ty, $($elt:expr),* ) => {
		bitvec![ LittleEndian, $prim, $( $elt ,)* ]
	};
	//  bitvec![BigEndian, type, 0, 1, ..., ]
	( BigEndian, $prim:ty, $($elt:expr,)* ) => {{
		let init: &[bool] = &[
			$( $elt > 0 ),*
		];
		BitVec::<$crate::BigEndian, $prim>::from(init)
	}};
	//  bitvec![LittleEndian, type, 0, 1, ..., ]
	( LittleEndian, $prim:ty, $($elt:expr,)* ) => {{
		let init: &[bool] = &[
			$( $elt > 0 ),*
		];
		BitVec::<$crate::LittleEndian, $prim>::from(init)
	}};
	( $($elt:expr),* ) => { bitvec![BigEndian, u8, $($elt)*] };
	( $($elt:expr,)* ) => { bitvec![BigEndian, u8, $($elt)*] };
}
