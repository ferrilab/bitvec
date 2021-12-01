# Bitfields

`bitvec`’s more technically-interesting capability is that it provides
load/store memory access behaviors that allow you to write values into, and read
them back out of, any `BitSlice` in memory rather than being constrained to
well-formed references to well-typed memory.

This is useful for the de/construction of packed memory buffers, such as
transporting data through I/O protocols.

All of this behavior is contained in the `BitField` trait. Let’s explore that:

```rust,no_run
//  bitvec::field

pub trait BitField {
  fn load<M>(&self) -> M;
  fn store<M>(&mut self, value: M);
}

impl<T> BitField for BitSlice<T, Lsb0> {
  fn load<M>(&self) -> M { /**/ }
  fn store<M>(&mut self, value: M) { /**/ }
}

impl<T> BitField for BitSlice<T, Msb0> {
  fn load<M>(&self) -> M { /**/ }
  fn store<M>(&mut self, value: M) { /**/ }
}
```

The actual trait is more complex than this, and will be visited later. The
important part, right now, is that `BitField` allows you to load values out of
`BitSlice`s and store values into them. Furthermore, it is implemented
*specifically* on `BitSlices` that use the bit orderings provided by `bitvec`,
and is **not** generic over all orderings.

While `bitvec` could in theory provide a default implementation for all
`<O: BitOrder>`, this would by necessity have the most pessimal possible
performance, and the lack of specialization for overlapping trait
implementations means that faster performance can never be written.

The downside of the two specific implementations is that Rust *coherence* rules
forbid implementation of a `bitvec` trait, on a `bitvec` type, parameterized
with a local, but non-`bitvec`, ordering type. On the off chance that you find
yourself writing a new `BitOrder` implementor, file an issue.

The `M` type parameter on the load and store methods is bounded by `BitMemory`,
which essentially means “is an unsigned integer”, with some extra bookkeeping
information used by `bitvec` internals. This parameterization allows you to
combine any integer type for transfer with any integer type for storage, rather
than being restricted to only transferring, `T` data into and out of a
`BitSlice<_, T>`.

Unfortunately, adding a second integer type parameter is not the only
complication to the `BitStore` memory model. There is also a second dimension of
segment ordering. `bitvec` tries to make explicitly clear that the `Lsb0` and
`Msb0` types refer only to the ordering of *bits* within registers, and not to
the ordering of *bytes* within registers. However, when the register being
stored or stored does not fit within one register of the storage `BitSlice`, it
must be split into multiple segments, and those segments must somehow be ordered
in memory.

## Segment Orderings

There are two segment orderings: little-endian and big-endian. You may select
the segment endianness you prefer by using the `_le` or `_be` suffix,
respectively, on the `.load` and `.store` methods. The unsuffixed method is an
alias for the endianness of your processor: `_be` on big-endian targets, and
`_le` on little-endian.

Let us imagine a `BitSlice<u8, Lsb0>` used to store a `u16` that is misaligned,
and thus stored in two successive bytes. This algorithm is true for all
circumstances where the stored region occupies more than one register of the
backing slice, but smaller examples are simpler to draw.

This diagram uses `0` to refer to the least significant bit, and `7` to refer to
the most significant bit. The first row shows bytes of memory, the second row
shows the bit indices in memory used by `.store_le`, and the third row shows the
bit indices in memory used by `.store_be`.

```text
[ 7 6 5 4 3 2 1 0 ] [ 7 6 5 4 3 2 1 0 ] [ 7 6 5 4 3 2 1 0 ]
  3 2 1 0             b a 9 8 7 6 5 4             f e d c
  f e d c             b a 9 8 7 6 5 4             3 2 1 0
```

`.store_le` places the least significant segment in the low address, while
`.store_be` places the most significant segment in the low address. The ordering
of bits within a segment is *always* preserved, no matter which ordering
parameter is used by the `BitSlice`.

Here is the same example, but using the `Msb0` bit ordering instead. Again, the
second row uses `.store_le`, and the third row uses `.store_be`.

```text
[ 7 6 5 4 3 2 1 0 ] [ 7 6 5 4 3 2 1 0 ] [ 7 6 5 4 3 2 1 0 ]
          3 2 1 0     b a 9 8 7 6 5 4     f e d c
          f e d c     b a 9 8 7 6 5 4     3 2 1 0
```

The only change is in how the segments are placed into memory. The ordering of
bits within a segment never changes, and is always the processor’s significance
order as implemented in hardware.

## How to Use `BitField`

You will probably find real use of the `BitField` trait more educational than
the previous section. It has a very straightforward API, that you can combine
with `println!`-debugging or your favorite means of viewing memory in order to
observe its actions.

Step one: create any `BitSlice`-capable buffer. This can be any of the
Rust-native sequence types, or any of the `bitvec` types.

```rust
use bitvec::prelude::*;

let mut data = [0u8; 4];
let bits = data.view_bits_mut::<Msb0>();
```

Then, narrow the `BitSlice` to be the region you want to access as storage. It
must be no wider than the integer type you are transferring: `BitSlice`s outside
the domain `1 ..= M::BITS` will panic during `.load` or `.store`. The easiest
way to narrow a `BitSlice` (or buffer type that dereferences to it) is by using
range indexing, `[start .. end]`.

```rust
# use bitvec::prelude::*;
# let bits = bits![mut u8, Msb0; 0; 32];
bits[10 ..][.. 13].store_be::<u16>(0x765);
assert_eq!(bits[10 .. 23].load_be::<u16>(), 0x765);

bits[10 .. 23].store_le::<u16>(0x432);
assert_eq!(bits[10 .. 23].load_le::<u16>(), 0x432);
```

That’s the entire API. `.store` truncates the stored value to the width of the
receiving `BitSlice`, and `.load` zero-extends the loaded value to the width of
the destination register type.

> If you want the ability to transfer signed integers, including signed
> truncation during `.store` and sign-extension during `.load`, please file an
> issue.

You can see an example that uses the `BitField` trait to implement an I/O
protocol in the `examples/ipv4.rs` program in the repository. Use
`cargo run --example ipv4` to see it in action.
