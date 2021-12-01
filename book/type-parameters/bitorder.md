# Bit Ordering <!-- omit in toc -->

1. [Provided Orderings](#provided-orderings)
   1. [`Lsb0`](#lsb0)
   1. [`Msb0`](#msb0)
   1. [`LocalBits`](#localbits)
   1. [Default Ordering Parameter](#default-ordering-parameter)
1. [Implementing `BitOrder`](#implementing-bitorder)
   1. [Support Types](#support-types)

`bitvec` expects user code to count semantic indices, and hides the actual
position of a bit within a memory element from users. This allows user code to
treat indices as a uniform domain of integers in `0 ..= !0 >> 3`, and not have
to remember whether `place - 1` means moving “forward” or “backward” in the
buffer.

Internally, each `*BitSlice` pointer contains an element address and a bit
index. The pointer uses its `BitOrder` type parameter to translate the bit index
into a one-hot selector mask that drives actual memory access.

`BitOrder` is open to user implementation, and implementations of it are trusted
to be sound in the `bitvec` memory model. For this reason, the trait is `unsafe`
to implement. Most users will not implement it; almost all users want one of the
two monotonic orderings provided for you. However, some specialized users may
have an ordering of their own, and they are still able to encode that ordering
away from their index logic.

## Provided Orderings

`bitvec` provides two orderings: `Lsb0` and `Msb0`. These each refer to which
numeric bit in a register element is considered to be the zero-index.

You can think of these as corresponding to the little-endian and big-endian
processor byte orderings if you like, as long as you remember that your choice
of bit-ordering is not at all related to the byte-ordering of your target
processor.

### `Lsb0`

The `Lsb0` type sets the zero index at the least significant bit of a register
(numeric value <math><mn>1</mn></math>) and each successive index selects the
next more significant bit in the register, until the most significant bit is at
the final index.

It is the expression `mask = 1 << index;`.

### `Msb0`

The `Msb0` type sets the zero index at the most significant bit of a register
(numeric value
<math><msup><mn>2</mn><mrow><mi>n</mi><mo>-</mo><mn>1</mn></mrow></msup></math>
for an `n`-bit register) and each successive index selects the next less
significant bit in the register, until the least significant bit is at the final
index.

It is the expression `mask = (iN::MIN as uN) >> index;`.

### `LocalBits`

The type alias `LocalBits` refers to the ordering that your target’s C compiler
will likely choose for its bitfield direction. This is `Lsb0` on little-endian
byte-ordered processors, and `Msb0` on big-endian byte-ordered processors.
Remember that the `BitOrder` implementations and processor byte orderings have
no relation to each other! This is only a custom, not a requirement of the
processor architecture.

### Default Ordering Parameter

`Lsb0` is the default type parameter used by the sequence types, as it produces
selection masks using the starting value `1`, which encodes to smaller
instructions than the `Msb0` starting value.

On AMD64, the pairs `<Lsb0, u64>` and `<Msb0, u64>` produce the following object
code and disassembly:

```text
ba 01 00 00 00  movl $1, %edx
48 d3 e2        shlq %cl, %rdx

48 ba 00 00 00 00 00 00 00 80  movabsq $-9223372036854775808, %rdx
48 d3 ea                       shrq    %cl, %rdx
```

The `Msb0` load requires an additional four bytes of zeros in its immediate,
and the 64-bit modifier prefix (`0x48`), in order to encode `movabsq` instead of
`movl`

## Implementing `BitOrder`

As stated above, this is an `unsafe trait` because `bitvec` relies on its
implementations to uphold certain mathematical invariants. Failure will result
in memory unsafety and/or program crashes.

`BitOrder` has three functions: `at`, `select`, and `mask`. Implementors are
required to provide `at`; `select` and `mask` have default implementations that
rely on it. These functions are all generic over the `BitMemory` trait; this
trait describes the register types (unsigned integers) that can be used by
`bitvec`. It provides some useful associated constants, and is otherwise
uninteresting.

- [`at`] receives the semantic index of a bit within a register type, and must
  produce the concrete position corresponding to the semantic index. The input
  and output are both integers in the domain `[0, W)` where `W` is the bit-width
  of the register type being indexed.

  `at` **must** implement an exactly one-to-one mapping from all inputs to all
  outputs in the `[0, W)` domain. This mapping must never observably change.
  These are strict requirements of the library, and failing to uphold either
  **will** break your program.

- [`select`] receives the semantic index of a bit within a register type, and
  must produce a value of that register type with exactly one bit set. The
  produced value is a mask that selects only the bit specified by the provided
  index, and will be used in Boolean arithmetic to manipulate memory.

  The default implementation is `1 << at(index)`. You are required to maintain
  this behavior in your override.

- `mask` receives an inclusive start index and an exclusive end index, and must
  produce a register value that selects every bit in the indexed range.

  The default implementation is `(start .. end).map(select).sum()`. You are
  required to maintain this behavior in your override.

### Support Types

The `BitOrder` trait APIs use supporting types to enforce requirements on the
bare numbers being passed through it. These types are documented in the [`index`]
module. They all provide a `.value()` method that removes the wrapper and yields
the inner number, and a `::new()` constructor that ensures that values to be
wrapped uphold the type’s requirements.

- `at` and `select` receive a [`BitIdx<M>`] argument. This is a wrapper over
  `u8` that ensures that the contained value is in the domain `0 .. M::BITS`. It
  serves to indicate that a number is a semantic counter, not an electrical
  position.
- `at` returns a [`BitPos<M>`] value. This has the same behavior and
  restrictions as `BitIdx<M>`, and indicates that the number is an electrical
  position within a register.
- `select` returns a [`BitSel<M>`] value. This wraps an `M` register value, and
  ensures that the contained number is a power of two – exactly one bit is set,
  and all others are zero. This type indicates that the mask is guaranteed to
  select exactly one bit in a register.
- `mask` receives an inclusive `BitIdx<M>` and an exclusive [`BitEnd<M>`]
  argument, and returns a [`BitMask<M>`] value. `BitEnd<M>` ensures that the
  contained number is in the domain `0 ..= M::BITS`, including the final count,
  and marks a one-past-the-end exclusive boundary. `BitMask<M>` marks that the
  contained number may select any number of bits in a register.

New implementors of `BitOrder` will use these types to satisfy behavior
requirements individually.

In addition, implementors’ test suites should call the function
`order::verify_for_type::<O, M>()` to check that an implementation `O` satisfies
the behavior requirements for a particular register type `M`, or call
`order::verify::<O>()` to check that an implementation satisfies the behavior
requirements for *all* supported register types. These functions are conditional
upon `cfg(test)`, and accept a `verbose: bool` parameter that allows the test
functions to print diagnostics to `stdout` during evaluation.

If the verification functions panic, your implementation is incorrect, and
cannot be safely used in `bitvec`.

[`BitIdx<M>`]: https://docs.rs/bitvec/latest/bitvec/index/struct.BitIdx.html "BitIdx API documentation"
[`BitMask<M>`]: https://docs.rs/bitvec/latest/bitvec/index/struct.BitMask.html "BitMask API documentation"
[`BitPos<M>`]: https://docs.rs/bitvec/latest/bitvec/index/struct.BitPos.html "BitPos API documentation"
[`BitSel<M>`]: https://docs.rs/bitvec/latest/bitvec/index/struct.BitSel.html "BitSel API documentation"
[`BitEnd<M>`]: https://docs.rs/bitvec/latest/bitvec/index/struct.BitEnd.html "BitEnd API documentation"
[`at`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html#tymethod.at "BitOrder::at API documentation"
[`index`]: https://docs.rs/bitvec/latest/bitvec/index/index.html "index module documentation"
[`mask`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html#method.mask "BitOrder::mask API documentation"
[`select`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html#method.select "BitOrder::select API documentation"
