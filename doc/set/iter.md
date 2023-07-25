# Bit-Set Iteration

This module provides iteration protocols for `BitSet`, including:

- extension of existing bit-sets with new data
- collection of data into new bit-sets
- iteration over the contents of a bit-sets

`BitSet` implements `Extend` and `FromIterator` for sources of `usize`.

Since the implementation is the same for sets, the [`IterOnes`] iterator from
the `slice` module is used for the set iterator instead of a wrapper.

[`IterOnes`]: crate::slice::IterOnes
