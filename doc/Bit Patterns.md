# Bit Patterns

This document describes how bit slices describe memory, and how their pointer
structures are composed.

## Cursor Addressing

This table displays the *bit index*, in [base64], of each position in a
`BitSlice<Cursor, Fundamental>` on a little-endian machine.

```text
byte  | 00000000 11111111 22222222 33333333 44444444 55555555 66666666 77777777
bit   | 76543210 76543210 76543210 76543210 76543210 76543210 76543210 76543210
------+------------------------------------------------------------------------
LEu__ | HGFEDCBA PONMLKJI XWVUTSRQ fedcbaZY nmlkjihg vutsrqpo 3210zyxw /+987654
BEu64 | 456789+/ wxyz0123 opqrstuv ghijklmn YZabcdef QRSTUVWX IJKLMNOP ABCDEFGH
BEu32 | YZabcdef QRSTUVWX IJKLMNOP ABCDEFGH 456789+/ wxyz0123 opqrstuv ghijklmn
BEu16 | IJKLMNOP ABCDEFGH YZabcdef QRSTUVWX opqrstuv ghijklmn 456789+/ wxyz0123
BEu8  | ABCDEFGH IJKLMNOP QRSTUVWX YZabcdef ghijklmn opqrstuv wxyz0123 456789+/
```

This table displays the bit index, in [base64], of each position in a
`BitSlice<Cursor, Fundamental>` on a big-endian machine.

```text
byte  | 00000000 11111111 22222222 33333333 44444444 55555555 66666666 77777777
bit   | 76543210 76543210 76543210 76543210 76543210 76543210 76543210 76543210
------+------------------------------------------------------------------------
BEu__ | ABCDEFGH IJKLMNOP QRSTUVWX YZabcdef ghijklmn opqrstuv wxyz0123 456789+/
LEu64 | /+987654 3210zyxw vutsrqpo nmlkjihg fedcbaZY XWVUTSRQ PONMLKJI HGFEDCBA
LEu32 | fedcbaZY XWVUTSRQ PONMLKJI HGFEDCBA /+987654 3210zyxw vutsrqpo nmlkjihg
LEu16 | PONMLKJI HGFEDCBA fedcbaZY XWVUTSRQ vutsrqpo nmlkjihg /+987654 3210zyxw
LEu8  | HGFEDCBA PONMLKJI XWVUTSRQ fedcbaZY nmlkjihg vutsrqpo 3210zyxw /+987654
```

`<BigEndian, u8>` and `<LittleEndian, u8>` will always have the same
representation in memory on all machines. The wider cursors will not.

## Pointer Representation

The bit pointer type `BitPtr<T>` is the fundamental component of the library. It
is a slice pointer with the capability to refine its concept of start and span
to bit-level granularity, allowing it to “point to” a single bit and count how
many bits after the pointed-to bit are included in the slice span.

The naïve implementation of such a pointer might be

```rust
struct BitPtr<T> {
  eltptr: *const T,
  elts: usize,
  first_bit: u8,
  last_bit: u8,
}
```

but this is three words wide, whereas a standard slice pointer is two. It also
has many invalid states, as indices into a slice of any type are traditionally
`usize`, and there only `usize::max_value() / 8` bytes in a fully widened bit
slice.

The next step might be for the struct to count bits, instead of elements, and
compute how many elements are in its domain based on the first live bit in the
slice and the count of all live bits. This eliminates the `last_bit` field,
folding it into `elts` to become `bits`,

```rust
struct BitPtr<T> {
  ptr: *const T,
  bits: usize,
  first_bit: u8,
}
```

but the width problem remains.

The (far too) clever solution is to fold the first-bit counter into the pointer
and length fields. This was not a problem with the last-bit counter, because
doing so brought the `bits` counter to match the indexing `usize` domain rather
than being far too large for it. However, there is not space to hold the
first-bit counter inside the other two elements!

Not without sacrificing range, anyway.

The naïve clever answer is to store both `last_bit` and `first_bit` in their
entirety inside the `len` field. However, each bit counter is a minimum of three
bits (indexing inside a `u8`) to a maximum of six bits (indexing inside a `u64`)
wide. On 32-bit systems, a bit slice over `u32` would lose ten bits to bit
tracking, but only had two bits to spare.

The astute observer will note that all architectures “require” – more of a
strongly prefer, but will grudgingly allow violation – pointers to be aligned to
the width of their pointed type. That is, a pointer to a `u32` must have an
address that is an even multiple of four, and so addresses like `6` or `102` are
not valid places in memory for a `u32` to begin.

I personally find this easier to show than to write. The diagram below shows the
acceptable placements of each value type in a region of sixteen bytes, and the
number after each `[` glyph is an acceptable modulus for the address.

> ```text
> u64 |[0---------------------][8---------------------]
> u32 |[0---------][4---------][8---------][c---------]
> u16 |[0---][2---][4---][6---][8---][a---][c---][e---]
>  u8 |[0][1][2][3][4][5][6][7][8][9][a][b][c][d][e][f]
> ```

That means that there is a bit available in the low end of the *pointer* for
every power of 2 element size above a byte. Narrowing from a byte to a bit still
requires three bits, which must be placed in the length field, but the low bits
of the pointer are able to take the rest.

> It so happens that pointers on x64 systems only use the low 48 bits of space,
> and the high 16 bits are not used for addressing. Some environments use the
> empty high bits for data storage, but this is risky as the high bits are
> considered “not used YET”, and not “available for whatever use”. Also, MMUs
> tend to trap when these bits are not sign-extensions of bit 47.
>
> Also, this trick does not work on 32-bit systems.
>
> While `bitvec` *could* have used pointer-mangling on 32-bit and dead-region
> storage on 64-bit, I made an executive decision that one sin was enough, and
> two unnecessary.

The end result of this packing scheme is that bit slice pointers will have the
following representation, written in C++ because Rust does not have bitfield
syntax. The ranges in comments are the range of the field width.

```cpp
template <typename T>
struct BitPtr {
  size_t ptr_head : __builtin_ctzll(alignof(T)); // 0 ... 3
  size_t ptr_data : sizeof(uintptr_t) * 8
                  - __builtin_ctzll(alignof(T)); // 64/32 ... 61/29

  size_t len_head : 3;
  size_t len_tail : 3 + __builtin_ctzll(alignof(T)); // 3 ... 6
  size_t len_data : sizeof(size_t) * 8
                  - 6 - __builtin_ctzll(alignof(T)); // 58/26 ... 55/23
};
```

So, for any storage fundamental, its bitslice pointer representation has:

- the low `alignof` bits of the pointer for selecting a byte, and the rest of
  the pointer for selecting the fundamental. This is just a `*const u8` except
  the type remembers how to find the correctly aligned pointer.
- the lowest 3 bits of the length counter for selecting the bit under the head
  pointer
- the *next* log<sub>2</sub>(bit size) bits of the length counter index the
  first *dead* bit *after* the slice ends.
- the remaining high bits index the final *storage fundamental* of the slice,
  counting from the correctly aligned address in the pointer.

## Value Patterns

### Null Value

The null value, `ptr: 0, len: 0` is reserved as an invalid value of `BitPtr<T>`
so that it may be used as `Option<BitPtr<T>>::None`.

### Empty Slices

All pointers whose non-`data` members are fully zeroed are considered
uninhabited. All empty pointers have the same data address, as provided by the
`NonNull::<T>::dangling()` function. The pointer is marked as `NonNull` in order
to take advantage of the null-pointer optimization of `Option`. Bit pointers to
empty space with no backing allocation use the uninhabited address, and bit
pointers to an allocation with no bits stored use the allocation address. The
distinction is important for `BitVec`.

Terminology: I will strive to use *uninhabited* to mean a pointer that does not
have an associated memory region, and *inhabited* to mean a pointer that does
have an associated memory region. All *uninhabited* slices **must** be empty;
*inhabited* slices may be empty or non-empty.

The region associated with a pointer is not required to be granted by the memory
allocator, nor managed by the pointer. This information is provided by the
semantic types atop the pointer; the pointer itself is solely a region
descriptor.

### Inhabited Slices

For inhabited slices, `elts` contains the offset of the last live element in the
underlying region.

A slice with its head and tail in the same element will have an `elts` count of
`0`. Since the `tail` count marks the first *unusable* bit, when `tail` is `0`
then there are exactly `elts` elements in the domain; when `tail` is non-zero,
there are `elts + 1` elements.

A slice with `elts` at `0` *must* have a `tail` which is greater than both zero
and `head`, in order to be considered inhabited.

### Full Slices

The full slices have `0` as their `head` value, and `!0` as their `tail` and
`elts` values. This means that they will contain `1 << P - N` elements, where
`P` is the local CPU word size and `N` is `3 + 3..=6`.

|Type |Word Size|Maximum Elements|
|----:|--------:|---------------:|
| `u8`|       64|       `1 << 58`|
|`u16`|       64|       `1 << 57`|
|`u32`|       64|       `1 << 56`|
|`u64`|       64|       `1 << 55`|
| `u8`|       32|       `1 << 24`|
|`u16`|       32|       `1 << 23`|
|`u32`|       32|       `1 << 22`|
|`u64`|       32|       `1 << 21`|

The final element in the slice is not able to use its final bit, as this would
cause a `tail` value of `0`, incrementing `elts` from `!0` to `0`, becoming the
empty slice.

[base64]: https://en.wikipedia.org/wiki/Base64
