/*! Test case for [Issue #33], provided by GitHub user [@jonas-schievink].

This report discovered an error in the implementation of `BitVec::reserve`,
which caused it to fail to reällocate in certain conditions.

The error was that the `reserve` method was testing the reservation amount
passed in to `Vec::reserve` against the currently-allocated *capacity*, not the
currently-occupied *element length*. `Vec::reserve` expects the difference to be
against the element length, so `BitVec::reserve` was estimating too few elements
and `Vec::reserve` did not see the request amount as requiring a reällocation.

`BitVec::reserve` now tests the reservation amount against the current element
length, which produces the correct reservation request for `Vec::reserve`,
fixing the error.

[Issue #33]: //github.com/myrrlyn/bitvec/issues/33
[@jonas-schievink]: //github.com/jonas-schievink
!*/

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[cfg(feature = "alloc")]
#[test]
fn issue_33() {
	let mut swdio = BitVec::<Lsb0, u8>::new();

	swdio.resize(64, true);

	let mut seq = 0xE79E; // LSb first
	for _ in 0 .. 16 {
		swdio.push(seq & 0b1 != 0);
		seq >>= 1;
	}

	swdio.reserve(64);
	swdio.resize(swdio.len() + 64, true);

	swdio.resize(swdio.len() + 10, false);
}
