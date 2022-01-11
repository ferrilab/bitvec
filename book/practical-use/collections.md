# Bit Collections

As discussed in the [Type Parameters] chapter, you should use `usize` as the
`BitStore` parameter for optimal performance in the generated program.

Once you have created some memory that you can view as individual bits, it is
time to actually use it. Here is the one-sentence summary of what `bitvec` can
do:

> Every stable API present in the standard library is replicated in `bitvec`,
> except for `BitSlice<T, O> as IndexMut<usize>`, because `bitvec` cannot
> produce `&mut bool`.

If you were using ordinary collections to manage sequences of `bool`s, then
every part of your code will continue to work on `bitvec` types except for the
array assignment `slice[index] = value;`. Until and unless the `IndexMut` trait
is reshaped, you will need to use one of these two alternatives:
`slice.set(index, value);` or `*slice.get_mut(index).unwrap() = value;`

Subslicing works:

```rust
use bitvec::prelude::*;

let bits = bits![0, 0, 0, 0, 1, 1, 1, 1];
assert!(bits[.. 4].not_any());
assert!(bits[4 ..].all());
```

Incremental munching works:

```rust
use bitvec::prelude::*;

let mut bits = bits![0, 0, 1, 1, 1, 0, 0, 0];
//  ^^^ modify the slice handle, not the slice contents

while let Some((&false, rest)) = bits.split_first() {
  bits = rest;
}
assert_eq!(bits, bits![1, 1, 1, 0, 0, 0]);

while let Some((&false, rest)) = bits.split_last() {
  bits = rest;
}
assert_eq!(bits, bits![1; 3]);
```

Mutation works:

```rust
use bitvec::prelude::*;
use std::{iter, thread};

let bits: &'static mut BitSlice = bits![mut 0; 8];

{
  let (left, right) = bits.split_at_mut(4);

  //  Pretend that better work is happening here
  let a = thread::spawn(|| left |= iter::repeat(true));
  let b = thread::spawn(|| right ^= iter::repeat(true));

  a.join().unwrap();
  b.join().unwrap();
}

assert_eq!(bits, bits![1; 8]);
```

Everything you can do with a slice, an array, or a vector of bits, you can do
with `bitvec`’s equivalent types. Except for `IndexMut<usize>`. The only change
from the standard library types is that you are now guaranteed to use one bit of
storage for each bit of information, rather than eight bits of storage per bit.

> Author’s note: Other than bragging about `bitvec`’s API fidelity, I don’t
> think this section is very useful or educational. If you want to read more
> about how to use `bitvec` for `usize => bool` collections, please let me know
> and I will expound!

[Type Parameters]: ../type-parameters.html
