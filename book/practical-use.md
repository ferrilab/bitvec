# Practical Use

That’s enough theory; let’s talk about how to use the crate. This chapter is
divided into two subsections, one for use cases that want an ordinary `bool`
collection library with transparent memory compaction, and one for use cases
that want a convenient way to precisely sculpt memory. Before getting in to
either, let’s quickly recap how the `bitvec` types interact with memory
ownership.

## Rustic Memory Management

The first and most important thing to remember is that, despite the extra
complexity just discussed about memory parameters and aliasing behavior,
`bitvec` is *just Rust*. It obeys all of the rules and patterns that the rest of
Rust does.

`BitSlice`s, like regular slices, are exclusively borrowed from owned memory
higher up the stack. Their references can be passed down the stack, and are
subject to the same lifetime and mutation-exclusivity rules.

The owned memory that creates a `BitSlice` view can be an array, boxed slice, or
vector of either ordinary integers, or their wrapper equivalents provided by
`bitvec`:

```rust
use bitvec::prelude::*;

let array = [0u8; 8];
let boxed: Box<[u16]> = Box::new([0u16; 4]);
let vec = vec![0u32; 2];

let bits_a = bitarr![u8, Msb0; 0; 64];
let bits_b = bitbox![u16, Lsb0; 0; 64];
let bits_v = bitvec![u32, LocalBits; 0; 32];
```

Once memory is bound, it can be borrowed as a `BitSlice` by using the `BitView`
trait (imported in the prelude), or by using the fact that all `bitvec`
containers borrow themselves as `BitSlices` just like standard-library
containers borrow themselves as slices:

```rust
# use bitvec::prelude::*;
# let array = [0u8; 8];
# let boxed: Box<[u16]> = Box::new([0u16; 4]);
# let vec = vec![0u32; 2];
# let bits_a = bitarr![u8, Msb0; 0; 64];
# let bits_b = bitbox![u16, Lsb0; 0; 64];
# let bits_v = bitvec![u32, LocalBits; 0; 32];
let array_bits = array.view_bits::<Msb0>();
let boxed_bits = boxed.view_bits::<Lsb0>();
let vec_bits = vec.view_bits::<LocalBits>();

let bits_a_ref: &BitSlice<_, _> = &bits_a;
let bits_b_ref: &BitSlice<_, _> = &bits_b;
let bits_c_ref: &BitSlice<_, _> = &bits_c;
```

> And, of course, mutability applies:
>
> ```rust
> let mut arr = bitarr![0; 10];
> let arr_ref: &mut BitSlice = &mut arr;
> arr_ref.set(1, true);
> assert!(arr_ref[1]);

Just as with ordinary Rust code, `BitSlice` is the type you want to use when
working with memory that you are not responsible for moving around or
destroying. However, when you do need to move memory around, you need to switch
to either a `static` binding or a container: `BitArray` is always available, and
`BitBox` and `BitVec` require an allocator.

I am spending this much time discussing the Rust memory management system
because this is a *very* common question I receive. No other bit-stream crate
has reference types, and therefore users coming from, e.g., `bit-vec` see the
same `BitSlice` name and attempt to use their habits from that crate.

`bitvec` is not like any other bitstream library, in Rust, C++, or another
language. `bitvec` is like ordinary Rust. I promise.
