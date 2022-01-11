# Slices <!-- omit in toc -->

1. [Getting a `BitSlice`](#getting-a-bitslice)
   1. [Borrowing Constructors](#borrowing-constructors)
   1. [Macro Constructor](#macro-constructor)
1. [What `BitSlice` Can Do](#what-bitslice-can-do)
   1. [… That `[bool]` Can](#-that-bool-can)
   1. [… That `[bool]` Cannot](#-that-bool-cannot)
   1. [Set Queries](#set-queries)
   1. [Boolean Arithmetic](#boolean-arithmetic)
   1. [Writing To Memory](#writing-to-memory)
   1. [Viewing the Underlying Memory](#viewing-the-underlying-memory)
1. [Footnotes](#footnotes)

The base type of the project is `BitSlice`. This is a region type, like
`[bool]`, and cannot be held directly. Instead, it is accessed by borrowed
references (`&BitSlice`, `&mut BitSlice`) or owning handles (`BitArray`,
`BitBox`, `BitVec`). The distinction between the handles and the region is the
same as it is in ordinary Rust types.

The `BitSlice` region is able to begin and end at any bit in memory, and is not
restricted to having one edge aligned to the edge of its initial element. This
restriction, present in all of its competitors, is removed through the use of a
special encoding in all pointers to the region, which stores the starting bit of
the base element in part of the slice pointer that describes the real memory.

There are eight bits to a byte on all systems Rust targets, and therefore the
index of a bit within a byte is itself three bits wide. These bits are taken
from the length counter of a slice pointer, which means that `BitSlice` is able
to address only ⅛<sup>th</sup> of the indices that `[bool]` can.

> This is 64 [Mebibytes] on a 32-bit system, and 256 [Pebibytes] on a 64-bit
> system. If you can even allocate that much real memory in one handle, then you
> have very different operating conditions than I can help you with.

## Getting a `BitSlice`

`BitSlice` is strictly a borrowed region. It can neither be created nor
destroyed; rather, views to it are acquired from a memory buffer that some other
binding owns.

The [`BitStore` chapter] covers this in more detail, but only slices of the
unsigned integers `u8`, `u16`, `u32`, `usize`, and (on 64-bit targets) `u64` can
be used as the source memory for a `BitSlice`. (You can also use their `Cell<>`
wrappers or atomic variants; this will be discussed later).

### Borrowing Constructors

The simplest way to create a `BitSlice` reference is to borrow it from ordinary
Rust data. The [`BitView`] trait, available in the [prelude], implements methods
on the supported unsigned integers, all arrays of them, and their slices.

```rust
use bitvec::prelude::*;

let byte = 0u8;
let bits = byte.view_bits::<LocalBits>();

let array = [0u16; 2];
let bits = array.view_bits::<Lsb0>();

let mut array = [0u32; 3];
let slice = &mut array[..];
let bits = slice.view_bits_mut::<Msb0>();
```

The `.view_bits()` and `.view_bits_mut()` methods take the other type parameter
`bitvec` requires. This is described in the [`BitOrder` chapter]. Use `Lsb0`
until you have a specific need for a more precise parameter.

In addition, `BitSlice` offers constructor functions `::from_element()`,
`::from_slice()`, and their `_mut` variants, which borrow elements and slices,
respectively, and construct `&/mut BitSlice` references from them. The trait
methods are generally easier, and certainly shorter to write, but they all do
the same work.

Lastly, empty slices can be produced with the `::empty()` or `::empty_mut()`
functions, since there is no `&[]` or `&mut []` literal available.

### Macro Constructor

In addition to these method constructors, you may also use the [`bits!`]
constructor macro. This macro runs at compile-time to produce a buffer
containing the correct data values, then borrows it as a `BitSlice` reference.
It is a `macro_rules!` macro, not a procedural macro, and should not have a
significant impact on your compilation times.

By default, the produced buffer is a temporary that the compiler will then
extend to have the minimum lifetime of the produced reference handle. However,
you can use the `static` keyword to cause the macro to produce a hidden and
unnameable `static BitArray` backing buffer, which then provides the
`&'static BitSlice` lifetime. Since this `static` buffer cannot be named, it is
safe to use even when `mut`able, as the provided reference is the only handle to
it.

The macro syntax extends that of `vec!`. The simplest invocations are sequences
or repetitions of expressions, which can optionally be made `mut`able:

```rust
use bitvec::prelude::*;

let r = bits![0, 1, 0, 1];
let w = bits![mut 0, 1, 0, 1];

let r2 = bits![static 1; 4];
let w2 = bits![static mut 1; 4];
```

> You are not required to use the literals `0` or `1`; you can use any
> expression  that is `const`-evaluable and can be placed into the expression
> `expr != 0`. This means that you cannot use the names of runtime `let`
> bindings, but can use the names of `const` bindings, or other literals. You
> probably do not want to do this, but you *can*.

In addition, you can specify the bit-ordering parameter and the integer storage
parameter, for even more precise control over the memory layout. If you do not
specify them, the macro uses the default parameters of `usize` storage and
`Lsb0` ordering.

```rust
use bitvec::prelude::*;

let in_bytes = bits![u8, LocalBits; 0, 1, 0, 1];
let in_shorts = bits![u16, Lsb0; 0, 1, 0, 1];
let in_ints = bits![mut u32, Msb0; 0; 4];
```

To summarize the macro rules:

- If the first macro argument is `mut`, then the macro produces `&mut BitSlice`,
  otherwise it produces `&BitSlice`. You do not need to bind the name as `mut`
  unless you want to reässign it to a different slice.
- You may then optionally provide the storage and ordering type parameters,
  followed by a semicolon. If you choose to add type parameters:
  - You *must* provide the bit-ordering parameter.
  - You *may* provide the storage parameter.
- The data input to the macro is one of the two `vec!` token lists:
  - One or more expressions that can be placed into `$expr != 0`, separated by
    commas. A trailing comma is permitted.
  - A single expression that can be placed into `$expr != 0`, followed by a
    semicolon and a repetition counter. The resulting `BitSlice` will be
    `counter` bits long, all set to `expression`.

> Emulation tests indicate that `bitvec` correctly instructs the compiler to
> produce suitable buffers even when compiling for a target with a different
> byte-endianness than the host. However, I have not actually performed such
> cross-compilation and testing with real hardware. It should be correct; please
> file an issue if it is not.

## What `BitSlice` Can Do

Now that you have acquired a `BitSlice` reference, either by borrowing memory
from elsewhere in your program or by creating a temporary, it is time to do some
actual work with it.

### … That `[bool]` Can

Everything[^1]. I am not going to rewrite the standard library’s slice
documentation here.

### … That `[bool]` Cannot

In addition to the standard library `[bool]` API, `BitSlice` offers some
inherent methods tailored to its specialization.

### Set Queries

The five query methods `.any()`, `.all()`, `.not_any()`, `.not_all()`, and
`.some()` test how many bits in a region are set to `1`. As you can guess from
the names, these methods have the following truth table:

|Slice| `any` | `all` |`not_any`|`not_all`|`some` |
|:---:|:-----:|:-----:|:-------:|:-------:|:-----:|
|`00` |`false`|`false`| `true`  | `true`  |`false`|
|`01` |`true` |`false`| `false` | `true`  |`true` |
|`11` |`true` |`true` | `false` | `false` |`false`|

`any` is the Boolean OR operator; `all` is the Boolean AND operator, and `some`
is the Boolean XOR operator.

In addition, `.count_ones()` and `.count_zeros()` count how many bits of the
slice are set to one or zero, rather than merely indicating whether any exist.
These methods are slower than the Boolean queries, which are capable of
short-circuiting once satisfied. You can also use `.iter_{ones,zeros}()` to walk
each *index* of bits with the specified value. These are equivalent to running
`.filter()` and `.enumerate()` calls on iterators of `bool`, but are specialized
to use dedicated bit-counting instructions where processors provide them.

### Boolean Arithmetic

`bitvec` data structures all implement the Boolean operators (`&`, `|`, `^`, and
`!`) against each other.

> In version 0, they allowed any `impl Iterator<Item = bool>`. This has been
> changed for performance reasons, since people never used the arbitrary
> iterator support but did require improved behavior when operating on two
> bit-slices.

```rust
use bitvec::prelude::*;

let mut or  =  bits![mut 0, 0, 1, 1];
        or |=  bits![    0, 1, 0, 1];
assert_eq!(or, bits![    0, 1, 1, 1]);

let mut and  =  bits![mut 0, 0, 1, 1];
        and &=  bits![    0, 1, 0, 1];
assert_eq!(and, bits![    0, 0, 0, 1]);

let mut xor  =  bits![mut 0, 0, 1, 1];
        xor ^=  bits![    0, 1, 0, 1];
assert_eq!(xor, bits![    0, 1, 1, 0]);

let mut not = bits![mut 0, 1];
        not = !not;
assert_eq!(not, bits![  1, 0]);
```

### Writing To Memory

You can set all bits in a region to a new value by using the `.fill()` method,
or you can set one bit in a region to a new value by using either the `.set` or
`.get_mut` methods. `.get_mut` produces a proxy type which acts roughly like an
`&mut bool` reference slot.

```rust
use bitvec::prelude::*;

let bits = bits![0; 4];
assert!(bits.not_any());

bits[0 .. 1].set_all(true);
assert!(bits[0]);

bits.set(1, true);
assert!(bits[1]);

*bits.get_mut(2).unwrap() = true;
assert!(bits[2]);

let mut bit = bits.get_mut(3).unwrap();
assert!(!bit);
*bit = true;
assert!(bits[3]);

assert!(bits.all());
```

The proxy type produced by `.get_mut()` implements `DerefMut<Target = bool>`, so
you can assign into it and read out of it. However, it does not commit the value
assigned into it back to its source `BitSlice` until it `Drop`s.

You can force the destruction of a named proxy reference by using its
`.commit()` method, which takes `self` by value, destroying it and releasing the
borrow.

### Viewing the Underlying Memory

The memory underlying any bit-slice region is subject to some restrictions about
aliasing that are documented more thoroughly in the [`domain`] module and the
[*Memory Model* chapter]. In short, borrowed `BitSlice` regions cannot view
their underlying memory directly without violating aliasing rules established by
either the Rust language or by `bitvec` itself. Instead, the `.domain()` and
`.domain_mut()` methods provide views that correctly handle aliasing and edge
conditions, and mediate access to the underlying memory.

The owning handles (`BitArray`, `BitVec`, and `BitBox`) do not have this
limitation, as they can guarantee unique access to a memory location without any
possibility of aliasing. As such, *these* types all have `.as_raw_slice()` and
`.as_raw_mut_slice()` methods that provide ordinary slice views to their storage
region.

## Footnotes

[^1]: Except write-assignment through indexing. I am not going to keep
      mentioning this exception.

[`BitOrder` chapter]: ../type-parameters/bitorder.html
[`BitStore` chapter]: ../type-parameters/bitstore.html
[`BitView`]: https://docs.rs/bitvec/latest/bitvec/view/trait.BitView.html
[`bits!`]: https://docs.rs/bitvec/latest/bitvec/macro.bits.html
[`domain`]: https://docs.rs/bitvec/latest/bitvec/domain
[Mebibytes]: https://en.wikipedia.org/wiki/Mebibyte
[Pebibytes]: https://en.wikipedia.org/wiki/Pebibyte
[prelude]: https://docs.rs/bitvec/latest/bitvec/prelude
[*Memory Model* chapter]: ../memory-model.html
