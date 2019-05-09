# Bit Patterns

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

This table displays the bit index in [base64] of each position in a
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

The bit region pointer allows addressing of any individual bit as the start and
end points of the span. The region pointer does not have any `Cursor`
information for mapping bit semantics onto bit positions; this is provided by
the public handle types. The added information in the pointer representation
reduces the bit-addressable span of a bit region to `usize::max_value() / 8`.

2<sup>29 bits is still a very large number, so I do not anticipate 32-bit
machines being overly constrained by this problem.

The logical structure of the bit region pointer is laid out roughly as follows,
written in C++ as Rust does not have bitfield syntax:

```cpp
template <typename T>
struct BitPtr {
  size_t ptr_head : __builtin_ctzll(alignof(T)); // 0 ... 3
  size_t ptr_data : sizeof(T*) * 8
                  - __builtin_ctzll(alignof(T)); // 64 ... 61

  size_t len_head : 3;
  size_t len_tail : 3 + __builtin_ctzll(alignof(T)); // 3 ... 6
  size_t len_data : sizeof(size_t) * 8
                  - 6 - __builtin_ctzll(alignof(T)); // 58 ... 55
};
```

So, for any storage fundamental, its bitslice pointer representation has:

- the low `alignof` bits of the pointer for selecting a byte, and the rest of
  the pointer for selecting the fundamental. This is just a `*const u8` except
  the type remembers how to find the correctly aligned pointer.
- the lowest 3 bits of the length counter for selecting the bit under the head
  pointer
- the *next* (3 + log<sub>2</sub>(bit width)) bits of the length counter address
  the first dead bit *after* the live span ends.
- the remaining high bits index the final *storage fundamental* of the slice,
  counting from the correctly aligned address in the pointer.

## Value Patterns

### Null Value

The null value, `ptr: 0, len: 0` is reserved as an illegal value of `BitPtr<T>`
so that it may be used as `Option<BitPtr<T>>::None`.

### Empty Slices

The empty slices all have *some* pointer value, and fully zeroed other fields.
The canonical empty slice uses `NonNull::<T>::dangling()` as its pointer value,
and empty vectors use their allocation address.

### Inhabited Slices

For inhabited slices, `elts` contains the offset of the last inhabited element
in the underlying region.

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
