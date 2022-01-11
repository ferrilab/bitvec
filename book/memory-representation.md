# Memory Representation

As discussed in the *Type Parameters* chapter, `bitvec` allows users to select
the specific ordering of bits within a memory element when constructing a type.
This has consequences for how source code translates to an in-memory
representation.

To review: `bitvec` provides two orderings of bits within a single memory
element (`Lsb0` and `Msb0`) and three or four types of memory elements (`u8`,
`u16`, `u32`, and only on systems where it is 8-byte-aligned, `u64`). The
`usize` type is also supported, but it is not portable, and behaves exactly as
the named register of its width.

> The `Cell` and atomic integer variants are not interesting here, as they only
> affect how the memory bus operates, not the processor register.

Let us now examine how each possible combination of register width,
bit-ordering, **and processor byte endianness** affects the placement of bits in
memory.

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
respectively, and `xx` indicates that the row matches all register types.
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
 Lxx ║ 1 <--- 0│3 <--- 2│5 <--- 4│7 <--- 6│9 <--- 8│B <--- A│D <--- C│F <--- E
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
 Mxx ║ 0 ---> 1│2 ---> 3│4 ---> 5│6 ---> 7│8 ---> 9│A ---> B│C ---> D│E ---> F
```

----

If you need to care about the memory representation, then you *most likely* want
to use the `<u8, Msb0>` pair. This provides a consistent ordering on all
machines, and the numeric value of the underlying memory will probably match
your expectations about the semantic contents of a data structure.

This chapter, and the [`BitField`] trait, are the two most common sources of
questions about how `bitvec` operates. Their intersection is even more complex,
and the layout of numeric integers stored into a `BitSlice` is an extremely
common point of confusion.

Read these chapters and the API documentation thoroughly, and experiment with
placing data into memory and changing the type parameters to observe their
effects on buffer representation.

[`BitField`]: https://docs.rs/bitvec/latest/bitvec/field/trait.BitField.html
