# Bit Ordering

`bitvec` is unique among its class of libraries in that it distinguishes
indexing within a sequence versus selecting a bit within a memory element. Users
are allowed to choose, or even create, a function that transforms an abstract
index into an actual selection mask. To make matters even more complex, users
are also allowed to choose which of the fundamental register types will be used
as the base unit of memory, with no intermediate subdivision between that type
and the individual bits.

This is expressed through the pair of type parameters
`<O: BitOrder, T: BitStore>` on all `bitvec` data structures. The correct choice
of parameters depends on your use case. This chapter explains how each
combination translates to real memory.

## `BitOrder` Types

`bitvec` provides three ordering names in its prelude: `LocalBits`, `Lsb0`, and
`Msb0`.

The `Lsb0` type uses the function `selector = 1 << index`, and is the typical
behavior of other bit-sequence libraries and of C-style structural bitfields on
most architectures. Notably, it is *not* the behavior of many I/O protocols,
which is why `bitvec` allows substitution.

The `Msb0` type uses the function `selector = !(!0 >> 1) >> index`, and is the
behavior used by I/O protocols such as TCP and IP, as well as C-style structural
bitfields on targets with big-endian byte ordering, such as SPARCv8.

If you do not have an explicit need for memory layout, you should probably not
use this ordering: its base constant is one of `0x80`, `0x80_00`,
`0x8000_0000`, or `0x8000_0000__0000_0000`, while the `Lsb0` base constant is
uniformly `1`. When used with register types wider than a byte, the base
constant probably will not be inlined into the instruction as an immediate
value, but will rather be computed at runtime as `(1 << reg_width) >> index`.

The `LocalBits` name aliases to either `Lsb0` or `Msb0`, depending on what C
compilers targeting your architecture would probably select when performing
structural bitfield layout. This is the default parameter used in `bitvec` types
that do not explicitly specify an ordering.

> I am uncertain whether this is specified in the C Standard, or if it is an
> implementation-defined practice. As bit-orderings within a memory element are
> unrelated to the byte-orderings of multi-byte elements, I cannot explain
> further why this change in behavior exists. Nevertheless, if you have written
> cross-platform I/O protocol code using bitfields, as I have, you have probably
> run into this behavior.

## `BitStore` Types

Unsigned integers that roughly correspond to ordinary (non-vector) CPU registers
on your target architecture implement `BitStore`.

This is not *quite* true: the actual **requirement** is that integers
implementing `BitStore` must always be aligned to their size. This is not the
case for `u64` on 32-bit `x86`, architectures (see the Rust [layout docs]).

In addition, `BitStore` is implemented on `Cell` wrappers of the integers, and
their atomic variants. This is used to provide alias-aware memory access, as
most architectures do not support modifying a single bit within a memory address
without locking the entire referent element.

`bitvec` is primarily developed and tested on `x86_64`, and may be incorrect on
embedded architectures. Please file an issue if you encounter errors involving
this trait.

## Memory Layout

The `BitOrder` and `BitStore` traits combine with your target architecture’s
byte-ordering of register elements to create a matrix of memory traversals. This
matrix informs what is the appropriate choice of parameters to use for your
program whenever you are using `bitvec` for precise memory control rather than
solely for a compact `usize`-to-`bool` data collection.

The tables below list bytes of a memory address space with addresses increasing
to the right, and the bits *within* those bytes with numeric significance
decreasing to the right. This is the ordering used in most debug-printing of
memory, so hopefully the table contents should match up with your prior
experience viewing memory bytes.

The `L` and `M` indicate the `Lsb0` and `Msb0` ordering parameters,
respectively, and `XX` indicates that the row matches all register types.
Within each row, traversal begins at zero and follows the arrows to each
successive step. Boundaries between registers are marked with a column;
boundaries between bytes within the same register are marked with a space.

### Little-Endian Byte-Ordered Machines

On little-endian machines, the least-significant *byte* of a register type is
stored at the lowest memory address, and each byte higher is one step more
numerically significant than the last.

```text
byte ║ 00000000│11111111│22222222│33333333│44444444│55555555│66666666│77777777
bit  ║ 76543210│76543210│76543210│76543210│76543210│76543210│76543210│76543210
═════╬═════════╪════════╪════════╪════════╪════════╪════════╪════════╪════════
 LXX ║ 1 <--- 0│3 <--- 2│5 <--- 4│7 <--- 6│9 <--- 8│B <--- A│D <--- C│F <--- E
─────╫─────────┼────────┼────────┼────────┼────────┼────────┼────────┼────────
 M8  ║ 0 ---> 1│2 ---> 3│4 ---> 5│6 ---> 7│8 ---> 9│A ---> B│C ---> D│E ---> F
 M16 ║ 2 ---> 3 0 ---> 1│6 ---> 7 4 ---> 5│A ---> B 8 ---> 9│E ---> F C ---> D
 M32 ║ 6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1│E ---> F C ---> D A ---> B 8 ---> 9
 M64 ║ E ---> F C ---> D A ---> B 8 ---> 9 6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1
```

### Big-Endian Byte-Ordered Machines

On big-endian machines, the most-significant *byte* of a register type is stored
at the lowest memory address, and each byte higher is one step less numerically
significant than the last.

```text
byte ║ 00000000│11111111│22222222│33333333│44444444│55555555│66666666│77777777
bit  ║ 76543210│76543210│76543210│76543210│76543210│76543210│76543210│76543210
═════╬═════════╪════════╪════════╪════════╪════════╪════════╪════════╪════════
 L8  ║ 1 <--- 0│3 <--- 2│5 <--- 4│7 <--- 6│9 <--- 8│B <--- A│D <--- C│F <--- E
 L16 ║ 3 <--- 2 1 <--- 0│7 <--- 6 5 <--- 4│B <--- A 9 <--- 8│F <--- E D <--- C
 L32 ║ 7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0│F <--- E D <--- C B <--- A 9 <--- 8
 L64 ║ F <--- E D <--- C B <--- A 9 <--- 8 7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0
─────╫─────────┬────────┬────────┬────────┬────────┬────────┬────────┬────────
 MXX ║ 0 ---> 1│2 ---> 3│4 ---> 5│6 ---> 7│8 ---> 9│A ---> B│C ---> D│E ---> F
```

[layout docs]: https://doc.rust-lang.org/reference/type-layout.html#primitive-data-layout
