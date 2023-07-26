# Automatically-Managed Index Set

This module defines the [`BitSet`] collection as a useful wrapper over a
[`BitVec`].

A `BitVec` is a very efficient way of storing a set of [`usize`] values since
the various set operations can be easily represented using bit operations.
However, a `BitVec` is less ergonomic than a `BitSet` because of the need to
resize when inserting elements larger than any already in the set.

[`BitSet`]: crate::set::BitSet
[`BitVec`]: crate::vec::BitVec
