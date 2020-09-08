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
> system. You’ll be fine.

## Getting a `BitSlice`

`BitSlice` is strictly a borrowed region. It can neither be created nor
destroyed; rather, views to it are aquired from a memory buffer that some other
binding owns.

The [`BitStore` chapter] covers this in more detail, but only sequences of the
unsigned integers `u8`, `u16`, `u32`, `usize`, and (on 64-bit targets) `u64` can
be used as the source memory for a `BitSlice`.

### Borrowing Constructors

The simplest way to create a `BitSlice` reference is to borrow it from ordinary
Rust data. The [`BitView`] trait, available in the [prelude], implements methods
on the supported unsigned integers, all[^1] arrays of them, and their slices.

```rust
use bitvec::prelude::*;

let byte = 0u8;
let bits = byte.view_bits::<Local>();

let array = [0u16; 2];
let bits = array.view_bits::<Lsb0>();

let mut array = [0u32; 3];
let slice = &mut array[..];
let bits = slice.view_bits_mut::<Msb0>();
```

The `.view_bits` and `.view_bits_mut` methods take the other type parameter
`bitvec` requires. This is the [`BitOrder` chapter]. Use `LocalBits` until you have
a specific need for a more precise parameter.

In addition, `BitSlice` offers constructor functions `::from_element`,
`::from_slice`, and their `_mut` variants, which borrow elements and slices,
respectively, and construct `&/mut BitSlice` references from them. The trait
methods are generally easier, and certainly shorter to write, but they all do
the same work.

Lastly, empty slices can be produced with the `::empty` or `::empty_mut`
functions, since there is no `&[]` or `&mut []` literal available.

### Macro Constructor

In addition to these method constructors, you may also use the [`bits!`]
constructor macro. This macro runs at compile-time to produce a `static` buffer
containing the correct data values, then borrows it as a `BitSlice` reference.
It is a `macro_rules!` macro, not a procedural macro, and should not have a
significant impact on your compilation times.

The macro syntax extends that of `vec!`. The simplest invocations are sequences
or repetitions of expressions, which can optionally be made `mut`able:

```rust
use bitvec::prelude::*;

let r = bits![0, 1, 0, 1];
let w = bits![mut 0, 1, 0, 1];

let r2 = bits![1; 4];
let w2 = bits![mut 1; 4];
```

> You are not required to use the literals `0` or `1`; you can use any
> expression  that is `const`-evaluable and can be placed into the expression
> `expr != 0`. This means that you cannot use the names of runtime `let`
> bindings, but can use the names of `const` bindings, or other literals. You
> probably do not want to do this, but you *can*.

In addition, you can specify the bit-ordering parameter and the integer storage
parameter, for even more precise control over the memory layout. If you do not
specify them, the macro uses the default parameters of `LocalBits` ordering and
`usize` storage.

```rust
use bitvec::prelude::*;

let in_bytes = bits![Local, u8; 0, 1, 0, 1];
let in_shorts = bits![Lsb0, u16; 0, 1, 0, 1];
let in_ints = bits![mut Msb0, u32; 0; 4];

let in_usize = bits![mut Local; 0; 4];
```

You can specify the bit-order without the storage, but you cannot specify the
storage without the bit-order. This is a limitation of the macro matching
implementation.

To summarize the macro rules:

- If the first macro argument is `mut`, then the macro produces `&mut BitSlice`,
  otherwise it produces `&BitSlice`. You do not need to bind the name as `mut`
  unless you want to reässign it to a different slice.
- You may then optionally provide the ordering and storage type parameters,
  followed by a semicolon. If you choose to add type parameters:
  - You *must* provide the bit-ordering parameter.
  - You *may* provide the storage parameter.
- The data input to the macro is one of the two `vec!` token lists:
  - One or more expressions that can be placed into `$expr != 0`, separated by
    commas. A trailing comma is permitted.
  - A single expression that can be placed into `$expr != 0`, followed by a
    semicolon and a repetition counter. The resulting `BitSlice` will be
    `counter` bits long, all set to `expression`.

The `&mut BitSlice` reference produced by each `bits![mut, …]` is safe to use
because, despite borrowing a `static mut` binding, the produced symbol is not
accessible anywhere in the program *except* through the sole reference emitted
by the macro.

> I have not actually tested what happens when you compile a `bits!` macro call
> on a little-endian host for a big-endian target, and then deploy the artifact
> to the target machine to run it. I hope the compiler inserts the
> endian-flipping methods in its process of assigning to `static`s, because
> `bitvec` does not.
>
> If this is a problem that affects you, please file an issue!

## What `BitSlice` Can Do

Now that you have acquired a `BitSlice` reference, either by borrowing memory
from elsewhere in your program or by creating a secret `static`, it is time to
do some actual work with it.

### … That `[bool]` Can

Everything[^2]. I am not going to rewrite the standard library’s slice
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

In addition, `.count_ones` and `.count_zeros` count how many bits of the slice
are set to one or zero, rather than merely indicating whether any exist. These
methods are slower than the Boolean queries, which are capable of
short-circuiting once satisfied.

### Boolean Arithmetic

`BitSlice` implements the three Boolean operators `|=`, `&=`, and `^=` against
any iterator that produces `bool`s, allowing you to write set-arithmetic
expressions.

```rust
use bitvec::prelude::*;

let mut or  =  bits![mut 0, 0, 1, 1];
        or |=  bits![    0, 1, 0, 1].iter().copied();
assert_eq!(or, bits![    0, 1, 1, 1]);

let mut and  =  bits![mut 0, 0, 1, 1];
        and &=  bits![    0, 1, 0, 1].iter().copied();
assert_eq!(and, bits![    0, 0, 0, 1]);

let mut xor  =  bits![mut 0, 0, 1, 1];
        xor ^=  bits![    0, 1, 0, 1].iter().copied();
assert_eq!(xor, bits![    0, 1, 1, 0]);
```

### Writing To Memory

You can set all bits in a region to a new value by using the `.set_all` method,
or you can set one bit in a region to a new value by using either the `.set` or
`.get_mut` methods. `.get_mut` produces a proxy type which acts like a `bool`
slot.

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

let bit = bits.get_mut(3).unwrap();
assert!(!bit);
bit.set(true);
assert!(bits[3]);

assert!(bits.all());
```

The proxy type produced by `.get_mut` implements `DerefMut<Target = bool>`, so
you can assign into it and read out of it. However, it does not commit the value
assigned into it back to its source `BitSlice` until it `Drop`s.

You can force the destruction of a named proxy reference by using *its* `.set`
method, which takes `self` by value, destroying it and releasing the borrow.

In addition to direct writes, the `.for_each` method yields each successive
index and value pair to a function `(usize, bool) -> bool`, then writes the
value this function returns back into the slice. This can be used to rapidly
rewrite a slice with the contents of a new generator function.

### Viewing the Underlying Memory

The slice of memory that any given `BitSlice` region occupies can be resurfaced
without releasing the `BitSlice` borrow. This action is subject to some
restrictions: while `BitSlice` can start or end anywhere in an element, ordinary
slice references cannot.

As such, `.as_mut_slice` and `.as_raw_slice` will exclude the edge elements of a
`BitSlice` if the bit-slice only partially uses them, while `.as_slice` will
always include them. The `.as_slice` method does not create an `&mut` exclusion
to memory, and permits other handles to reference the memory that it does. It is
correctly marked as aliased when other handles are capable of writing to the
edge elements.

```rust
use bitvec::prelude::*;
use std::sync::atomic::{AtomicU8, Ordering};

//  Without aliasing
let mut data = [0u8; 3];
let fewer_bits = &mut data.view_bits_mut::<Local>()[2 .. 22];

{
  let a: &mut [u8] = fewer_bits.as_mut_slice();
  assert_eq!(a.len(), 1);
  *a[0] = !0;
}

{
  let b: &[u8] = fewer_bits.as_raw_slice();
  assert_eq!(a.len(), 1);
  assert_eq!(b[0], !0);
}

{
  let c: &[u8] = fewer_bits.as_slice();
  assert_eq!(c.len(), 3);
  assert_eq!(c, &[0, !0, 0]);
}

//  With aliasing
let mut data = [0u8; 3];
let (some, rest) = data.view_bits_mut::<Local>().split_at_mut(2);

{
  let some_bytes: &mut [u8] = some.as_mut_slice();
  assert!(some.is_empty());

  let rest_bytes: &[u8] = rest.as_raw_slice();
  assert_eq!(rest.len(), 2);
}

{
  let d: &[AtomicU8] = some.as_slice();
  let e: &[AtomicU8] = rest.as_slice();

  assert_eq!(d.len(), 1);
  assert_eq!(e.len(), 3);

  assert!(!rest[0]);
  d[0].store(!0, Ordering::SeqCst);
  assert_eq!(e[0].load(Ordering::SeqCst), !0);
  assert!(rest[0]);
}
```

When a `BitSlice` is split into mutable slices that overlap in memory elements,
they switch to using atomics (or `Cell`s, when atomics are unavailable) for
memory access, as demonstrated above. `.as_slice` yields slices of atomics,
which can correctly cope with mutation of the referent memory outside of their
control, and `.as_mut_slice` and `.as_raw_slice` exclude the aliased memory
elements from their slices.

The [*Memory Model* chapter] discusses the type system used to handle aliasing.

## Footnotes

[^1]: Currently, `0 <= N <= 32`; once the type-level-integer feature stabilizes,
      *all*

[^2]: Except write-assignment through indexing. I am not going to keep
      mentioning this exception.

[`BitOrder` chapter]: ../type-parameters/bitorder.html "BitOrder type parameter"
[`BitStore` chapter]: ../type-parameters/bitstore.html "BitStore type parameter"
[`BitView`]: https://docs.rs/bitvec/latest/bitvec/view/trait.BitView.html
[`bits!`]: https://docs.rs/bitvec/latest/bitvec/macro.bits.html
[Mebibytes]: https://en.wikipedia.org/wiki/Mebibyte "Wikipedia: Mebibyte"
[Pebibytes]: https://en.wikipedia.org/wiki/Pebibyte "Wikipedia: Pebibyte"
[prelude]: https://docs.rs/bitvec/latest/bitvec/prelude
[*Memory Model* chapter]: ../memory-model.html "bitvec memory model"
