# Bit-Set Range Iteration

This view iterates over the elements in a bit-set within a given range. It is
created by the [`BitSet::range`] method.

## Original

[`btree_map::Range`](alloc::collections::btree_map::Range)

## API Differences

Since the `usize` are not physically stored in the set, this yields `usize`
values instead of references.

## Examples

```rust
use bitvec::prelude::*;
use bitvec::set::BitSet;

let mut bs: BitSet = BitSet::new();
bs.insert(1);
bs.insert(2);
bs.insert(3);
bs.insert(4);
for val in bs.range(2..6) {
  # #[cfg(feature = "std")] {
  println!("{val}");
  # }
}
```

[`BitSet::range`]: crate::set::BitSet::range
