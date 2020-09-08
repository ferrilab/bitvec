# Arrays

While `BitSlice` describes a region of borrowed data, `BitArray` provides a
container that can hold and manage such a region.

It is most comparable to the C++ type [`std::bitset<N>`]. Unfortunately, the
Rust support for type-level integers is still experimental, so it is unable to
take the length of the `BitSlice` it contains as a type parameter. Instead, it
must take the entire region it contains as a type parameter. The full type
declaration is

```rust,ignore
# use bitvec::prelude::*;
pub struct BitArray<
  O: BitOrder,
  V: BitView,
> {
  _ord: PhantomData<O>,
  data: V,
}
```

As described in the [previous chapter], the `BitView` trait is implemented on
the unsigned integers, and on arrays of them. Currently, array support is
limited to arrays up to and including 32 elements long; as Rust type-level
integers mature, this will grow to include all arrays.

> Once type-level computation stabilizes, `BitArray` will change to have the
> type parameters `<O: BitOrder, T: BitStore, const N: usize>`, matching the
> `std::bitset<N>` length parameter.

This array dereferences to a `BitSlice` region over its entire length. It does
not currently permit shortening its `BitSlice` from either end. If this is a
behavior you want, please file an issue.

## Using a `BitArray`

The `::zeroed` function constructs a new `BitArray` with its memory completely
zeroed. The `::new` function wraps an existing element or array into a
`BitArray`. In addition, the macro constructor `bitarr!` takes the exact same
arguments as the `bits!` constructor, except that it returns an array directly
rather than a reference to a `static` buffer.

In addition, `BitArray` structures and references can be constructed from
`&BitSlice` references using the `TryFrom` trait, just as arrays can be
constructed in the standard library.

Once constructed, `BitArray` offers the `.as_bitslice` and `.as_mut_bitslice`
explicit methods, as well as all the standard traits, to borrow its data as a
`BitSlice`. The array has no functionality of its own, and serves only to own a
region used as a`BitSlice`.

Once you are done using `BitSlice` to manipulate the array, you can remove the
array with `.unwrap` and regain the `V` memory within. This name is subject to
change if users are sufficiently unhappy with it.

That’s everything that the array does! Like regular arrays, it is useful
primarily for its ability to move memory through a program, and has essentially
no behavior in its own right. It is useful for programs that do not have access
to a dynamic allocator, and do not wish to use `static` buffers. However, if you
do have access to an allocator, you will probably prefer to use `BitVec`
instead.

[previous chapter]: ./bitslice.html "BitSlice region"
[`std::bitset<N>`]: https://en.cppreference.com/w/cpp/utility/bitset "C++ std::bitset documentation"
