/*! Prove that the example code in `README.md` executes.

Until the README.md file can be linked into the library directly for `rustdoc`
to use, this file must be consistently updated whenever the README’s code
samples are modified.
!*/

#[cfg(feature = "alloc")]
extern crate bitvec;

#[cfg(feature = "alloc")]
use bitvec::prelude::*;

#[cfg(feature = "alloc")]
use std::iter::repeat;

#[cfg(feature = "alloc")]
#[test]
fn readme() {
    let mut bv = bitvec![Msb0, u8; 0, 1, 0, 1];
    bv.reserve(8);
    bv.extend(repeat(false).take(4).chain(repeat(true).take(4)));

    //  Memory access
    assert_eq!(bv.as_slice(), &[0b0101_0000, 0b1111_0000]);
    //                   index 0 -^               ^- index 11
    assert_eq!(bv.len(), 12);
    assert!(bv.capacity() >= 16);

    //  Stack operations
    bv.push(true);
    bv.push(false);
    bv.push(true);

    assert!(bv[12]);
    assert!(!bv[13]);
    assert!(bv[14]);
    assert!(bv.get(15).is_none());

    bv.pop();
    bv.pop();
    bv.pop();

    //  Set operations
    bv &= repeat(true);
    bv |= repeat(false);
    bv ^= repeat(true);
    bv = !bv;

    //  Arithmetic operations
    let one = bitvec![Msb0, u8; 1];
    bv += one.clone();
    assert_eq!(bv.as_slice(), &[0b0101_0001, 0b0000_0000]);
    bv -= one;
    assert_eq!(bv.as_slice(), &[0b0101_0000, 0b1111_0000]);

    //  Borrowing iteration
    let mut iter = bv.iter();
    //  index 0
    assert_eq!(iter.next().copied().unwrap(), false);
    //  index 11
    assert_eq!(iter.next_back().copied().unwrap(), true);
    assert_eq!(iter.len(), 10);
}
