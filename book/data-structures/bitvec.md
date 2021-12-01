# Vectors

`bitvec` has two types that require compiling the crate with `feature = "alloc"`
(and linking against the Rust distribution crate `alloc`): `BitVec` and
`BitBox`. `BitVec` is a dynamically resizable vector, equivalent to the C++ type
[`std::vector<bool>`] and the Rust type [`Vec<bool>`]. `BitBox` is a frozen
vector, incapable of changing its length, equivalent to the Rust type
`Box<[bool]>` or the C++ type `std::unique_ptr<std::bitset<N>>`.

Since `BitBox` is a vector that cannot `.push` or `.pop`, I will not discuss it
in detail here. It is a heap-allocated `BitSlice`, and is otherwise
uninteresting.

## Getting a `BitVec`

`BitVec` implements the constructors shown in the standard library: `::new`
creates a handle without any allocation, `BitSlice` implements the `.to_bitvec`
method, and the `Clone` and `ToOwned` traits, to copy a slice into a new vector,
and the `bitvec!` macro takes all the `bits!` arguments and produces a vector
instead of a `static` buffer. You can also construct a `BitVec` by `.collect`ing
any iterator of `bool`s.

```rust
use bitvec::prelude::*;

let a: BitVec = BitVec::new();
let b = bits![0, 1, 0, 1].to_bitvec();
let c = bits![0; 4].clone();
let d = bits![u8, Msb0; 1; 4].to_owned();
let e = bitvec![0, 1, 1, 0];
let f = bitvec![u16, Msb0; 0; 4];
let g = [true, false, true, false]
  .iter() // &bool
  .copied() // bool
  .collect::<BitVec>();
```

## Using a `BitVec`

Once constructed, `BitVec` implements the entire API that `Vec` does in the
standard library. This remains uninteresting to write out.

Like `BitSlice`, `BitVec` and `BitBox` are implemented as stack handles that use
the specially-encoded pointer to describe their region. This enables them to
remain the same size as their standard-library counterparts, while making them
completely opaque to inspection.

Because they are fully owned, `BitVec` and `BitBox` have some important
behavioral differences from `BitSlice`. Primarily, because they do not have to
worry about other handles viewing the memory under their control, they can
modify the contents of their buffers outside the `BitSlice` that is considered
live, and they do not exclude partial edge elements when viewing their buffer as
raw memory. If you are using `BitVec` to construct an I/O buffer, these two
facets can have surprising results if you are not careful to fully initialize a
memory span.

Vectors, like slices, do not need to begin at the zeroth index of the base
element. They can begin, and end, at any bit in any element. This will only
happen when copying a vector from a source slice that was misaligned. The
`.force_align` method moves the vector’s live slice down to start at the zero
index. Once done, extending the live slice to reach the last index of an element
ensures that viewing the buffer as raw memory will have no uninitialized bits.

[`Vec<bool>`]: https://doc.rust-lang.org/stable/alloc/vec/struct.Vec.html "Vec API documentation"
[`std::vector<bool>`]: https://en.cppreference.com/w/cpp/container/vector_bool "C++ std::vector<bool> documentation"
