/*! This benchmark compares the speeds of various rotator methods.

The `BitVec` specializations are required to be faster than the `BitSlice`
defaults. If they are slower, then they have no purpose being left in the
codebase.
!*/

#![cfg(all(test, feature = "std"))]

use bitvec::prelude::*;

use criterion::{
	BenchmarkId,
	Criterion,
	criterion_group,
	criterion_main,
};

fn rotate_cmp(c: &mut Criterion) {
	let mut raw = [0x0123u16, 0x4567, 0x89ab, 0xcdef];
	let bs = &mut raw.bits_mut::<LittleEndian>()[1 .. 63];
	let mut bv = [0x0123u16, 0x4567, 0x89ab, 0xcdef]
		.bits_mut::<LittleEndian>()[1 .. 31]
		.to_owned();

	let mut grp = c.benchmark_group("rotators");
	for shamt in 1 .. 62 {
		grp.bench_with_input(
			BenchmarkId::new("BitSlice", shamt),
			&shamt,
			|b, shamt| b.iter(|| bs.rotate_left(*shamt)),
		);
		grp.bench_with_input(
			BenchmarkId::new("BitVec", shamt),
			&shamt,
			|b, shamt| b.iter(|| bv.rotate_left(*shamt)),
		);
	}
}

criterion_group!(rotators, rotate_cmp);
criterion_main!(rotators);
