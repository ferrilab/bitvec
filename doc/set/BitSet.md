# Packed-Bits Set

This is a data structure that consists of an automatically managed [`BitVec`]
which stores a set of `usize` values as `true` bits in the `BitVec`.

The main benefit of this structure is the automatic handling of the memory
backing the [`BitVec`], which must be resized to account for the sizes of data
inside it. If you know the bounds of your data ahead of time, you may prefer to
use a regular [`BitVec`] or even a [`BitArray`] instead, the latter of which
will be allocated on the stack instead of the heap.

## Documentation Practices

`BitSet` attempts to replicate the API of the standard-library `BTreeSet` type,
including inherent methods, trait implementations, and relationships with the
[`BitSet`] analogue.

Items that are either direct ports, or renamed variants, of standard-library
APIs will have a `## Original` section that links to their standard-library
documentation. Items that map to standard-library APIs but have a different API
signature will also have an `## API Differences` section that describes what
the difference is, why it exists, and how to transform your code to fit it. For
example:

## Original

[`BTreeSet<T>`](alloc::collections::BTreeSet)

## API Differences

As with all `bitvec` data structures, this takes two type parameters `<T, O>`
that govern the bit-vector’s storage representation in the underlying memory,
and does *not* take a type parameter to govern what data type it stores (always
`usize`)

### Accessing the internal [`BitVec`]

Since `BitSet` is merely an API over the internal `BitVec`, you can freely
take ownership of the internal buffer or borrow the buffer as a `BitSlice`.

However, since would be inconsistent with the set-style API, these require
dedicated methods instead of simple deref:

```rust
use bitvec::prelude::*;
use bitvec::set::BitSet;

fn mutate_bitvec(vec: &mut BitVec) {
  // …
}

fn read_bitslice(bits: &BitSlice) {
  // …
}

let mut bs: BitSet = BitSet::new();
bs.insert(10);
bs.insert(20);
bs.insert(30);
read_bitslice(bs.as_bitslice());
mutate_bitvec(bs.as_mut_bitvec());
```

Since a `BitSet` requires no additional invariants over `BitVec`, any mutations
to the internal vec are allowed without restrictions. For more details on the
safety guarantees of [`BitVec`], see its specific documentation.

[`BitArray`]: crate::array::BitArray
[`BitSet`]: crate::set::BitSet
[`BitVec`]: crate::vec::BitVec
