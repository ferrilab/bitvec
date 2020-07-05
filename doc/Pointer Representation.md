# Bit Slice Pointer Representation

`bitvec`’s core value proposition rests on the fact that it is capable of
defining an unsized slice type, and controlling references to it. The Rust
language rests heavily on the two reference types `&` and `&mut`, and does not
ordinarily allow these to be faked or created by anything other than the
compiler.

## Rust Reference Rules

It so happens that not only does rust strongly guarantee the [in-memory layout]
of a reference to a slice, it also provides a stable API for
[constructing values] of `&[T]` type without using `mem::transmute`. Subject to
certain value requirements imposed by types, slice references can be constructed
through these functions and the compiler will accept them as valid.

These requirements traditionally make it difficult to encode non-address
information into a bare reference, since the compiler has a very firm
expectation that a reference to a type is immediately dereferencable to a value
of that type, but if your type happens to be zero-sized, then it can never exist
in memory, no loads or stores to it can ever be produced, and the compiler no
longer concerns itself with the actual bit-pattern value of references to it.

Which is why the definition of `BitSlice` is

```rust
//  src/slice.rs

#[repr(transparent)]
pub struct BitSlice<O, T>
where
  O: BitOrder,
  T: BitStore,
{
  _mem: [()],
  _ord: PhantomData<O>,
  _typ: PhantomData<T>,
}
```

`BitSlice` is `[()]` with some markers that only `typeck` can see. `&BitSlice`
is thus `&[()]`, and `&[()]` can have any values it wants.

## Pointer Encoding

Slice references contain two pieces of information: the address of the base
element, and the number of elements, starting at the base, contained in the
slice region. Theoretically, bit-slice references have the same pair of
information: the address of the first bit, and the number of bits in the region.

However, computers are byte-addressed, not bit-addressed, so we need to store
three more bits (to select a bit in the base byte) in the reference somewhere.
Since slice references are defined as `{ base: *const T, elts: usize }`, and
there are no[^1] spare bits in `*const _`, the bits to store the base bit are
taken out of the length counter.

Reference address values are also required to be integer multiples of the
alignment of the referent type `T`. This alignment is, on all supported targets,
the width in bytes of the referent type. As a result, there are as many low bits
in the address of any `T` that are *guaranteed* to be the `0` value, as there
are bits needed to select a byte within the element. The end result is that the
length counter must always use three bits to store the starting bit, and the
base address will be composed of an aligned `T` address and an index of the
starting byte within it.

As Rust does not have bitfield syntax, a definition of the pointer structure in
C++ looks like this:

```cpp
template <typename T>
struct BitPtr<T> {
  static_assert(
    std::is_unsigned<T>
    && sizeof(T) <= sizeof(size_t)
  );

  uintptr_t ptr_head : __builtin_ctzll(alignof(T));
  uintptr_t ptr_addr : sizeof(uintptr_t) * CHAR_BITS;
                     - __builtin_tczll(alignof(T));

  size_t len_head : 3;
  size_t len_bits : sizeof(size_t) * 8 - 3;
}
```

In Rust, the structure is declared as

```rust
//  src/pointer.rs

#[repr(C)]
pub struct BitPtr<T>
where T: BitStore {
  ptr: NonNull<u8>,
  len: usize,
  _ty: PhantomData<T>,
}
```

and the logical components must be accessed through get/set functions, rather
than through compiler-generated field stubs.

By marking the pointer as `NonNull`, `BitPtr` declares that it will never be a
null pointer and becomes subject to the same peephole optimization that allows
`mem::size_of::<Option<&T>>() == mem::size_of::<&T>()`. By marking it as
unconditionally a pointer to `u8`, we declare that all low bits of the address
value are in use, and none can be used as slots for anything else (since our
encoding is using them to select a byte within the `T`).

## Significant Values

The null value, `{ ptr: 0, len: 0 }`, is not valid in `BitPtr<T>`, but rather is
used to mark `Option::<BitPtr<T>>::None`.

### Empty Slices

All slices with a `bits` *logical* field are considered equally empty, and equal
to each other. The `addr` and `head` logical fields can be anything. However,
they are not required to be clamped to `1` and `0`, respectively, because they
can contain important information about the region.

Specifically, the `BitVec` type is an owning type that manages a buffer assigned
to it by the memory allocator. It is never allowed to forget the address of its
buffer, even if the user has removed all live bits from the vector.

## Summary

Rust requires that slice references have a specific ABI, but makes no
requirements about the encoding of values of those references for certain types.
We can supply our own ABI-equivalent structure, define functions that use the
structural encoding to compute the information needed to actually interact with
memory, and convert our structures into Rust-accepted slices through the
provided compiler API in `core`.

## Footnotes

[^1]: On AMD64, pointers are actually aggregates of [MMU translation pages], and
      processors only decode the low 48 or 57 bits of them, leaving the high 16
      or 7 bits available for other information not part of the memory
      addressing system. However, these processors also trap when attempting to
      dereference a pointer whose high `[48:]` or `[57:]` bits do not have the
      same bit value as bit `[47]` or `[56]`, and that bit is typically used to
      differentiate unprivileged user memory from privileged kernel memory.
      Furthermore, this dead region does not exist on 32-bit architectures, x86
      or otherwise, and since `bitvec` explicitly supports 32-bit systems, the
      use of dead bits only present on a subset of supported targets and subject
      to their own extra rules

[MMU translation pages]: https://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details
[constructing values]: https://github.com/rust-lang/rust/blob/8558ccd/src/libcore/slice/mod.rs#L5642-L5739
[in-memory layout]: https://github.com/rust-lang/rust/blob/8558ccd/src/libcore/ptr/mod.rs#L220-L231
