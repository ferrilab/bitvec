# Bit Ordering

`bitvec` is unique among its class of libraries in that it differentiates
indexing within a sequence from selecting a bit within a memory element. Users
are allowed to choose, or even create, a function that transforms an abstract
index into an actual selection mask. To make matters even more complex, users
are also allowed to choose which of the fundamental integer types will be used
as the base unit of memory, with no intermediate subdivision between that type
and the individual bits.

This document shows how each combination of ordering and memory parameters
correspond to actual bits in memory.

These tables list bytes in increasing distance from the base address from left
to right, and the bits *within* those bytes in decreasing numeric significance
from left to right. There is nothing special about this ordering; it is merely
the custom that the author was taught.

The `L0` and `M0` indicate the `Lsb0` and `Msb0` ordering parameters,
respectively, and `uXX` indicates that the row matches all integer types. Within
the table, traversal begins at zero and follows the arrows to each successive
integer step. Boundaries between integers are marked with a column; boundaries
between bytes within the same integer are marked with a space.

## Little-Endian Byte-Ordered Machines

On little-endian machines, the least-significant *byte* of a register type is
stored at the lowest memory address, and each byte higher is one step more
numerically significant than the last.

```text
byte ║00000000│11111111│22222222│33333333│44444444│55555555│66666666│77777777
bit  ║76543210│76543210│76543210│76543210│76543210│76543210│76543210│76543210
═════╬════════╪════════╪════════╪════════╪════════╪════════╪════════╪════════
M0u8 ║0 ---> 1│2 ---> 3│4 ---> 5│6 ---> 7│8 ---> 9│A ---> B│C ---> D│E ---> F
M0u16║2 ---> 3 0 ---> 1│6 ---> 7 4 ---> 5│A ---> B 8 ---> 9│E ---> F C ---> D
M0u32║6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1│E ---> F C ---> D A ---> B 8 ---> 9
M0u64║E ---> F C ---> D A ---> B 8 ---> 9 6 ---> 7 4 ---> 5 2 ---> 3 0 ---> 1
─────╫────────┬────────┬────────┬────────┬────────┬────────┬────────┬────────
L0uXX║1 <--- 0│3 <--- 2│5 <--- 4│7 <--- 6│9 <--- 8│B <--- A│D <--- C│F <--- E
```

## Big-Endian Byte-Ordered Machines

On big-endian machines, the most-significant *byte* of a register type is stored
at the lowest memory address, and each byte higher is one step less numerically
signifcant than the last.

```text
byte ║00000000│11111111│22222222│33333333│44444444│55555555│66666666│77777777
bit  ║76543210│76543210│76543210│76543210│76543210│76543210│76543210│76543210
═════╬════════╪════════╪════════╪════════╪════════╪════════╪════════╪════════
M0uXX║0 ---> 1│2 ---> 3│4 ---> 5│6 ---> 7│8 ---> 9│A ---> B│C ---> D│E ---> F
─────╫────────┼────────┼────────┼────────┼────────┼────────┼────────┼────────
L0u8 ║1 <--- 0│3 <--- 2│5 <--- 4│7 <--- 6│9 <--- 8│B <--- A│D <--- C│F <--- E
L0u16║3 <--- 2 1 <--- 0│7 <--- 6 5 <--- 4│B <--- A 9 <--- 8│F <--- E D <--- C
L0u32║7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0│F <--- E D <--- C B <--- A 9 <--- 8
L0u64║F <--- E D <--- C B <--- A 9 <--- 8 7 <--- 6 5 <--- 4 3 <--- 2 1 <--- 0
```
