# Type Parameters

`bitvec` uses type parameters to permit precise user control of its behavior and
in-memory representation. The Rust generic system permits `bitvec` to have a
more powerful and capable behavior than any other bitstream library yet
implemented in any language.

All `bitvec` types take two type parameters. The first, common to all of them, is
an implementor of the `BitOrder` trait. The second type parameter for
`BitSlice`, `BitVec`, and `BitBox` is an implementor of `BitStore`; the second
type parameter for `BitArray` is an implementor of `BitView`. `BitView` is a
wrapper of `BitStore` that enables the use of arrays as well as scalar integers,
and is not otherwise interesting.

The combination of these two parameters governs how a `bitvec` type computes its
accesses to memory. The full matrix of parameter combinations is described in
the [provided types chapter][ptc].

The next two chapters describe each trait in more detail. You may be able to
skip them with this sentence as a good-enough summary:

Use `<LocalBits, usize>` as the parameters if you are implementing a collection,
and do not care about memory layout; if you are implementing an I/O protocol
specification, the specification document will tell you what ordering and unit
size it requires.

Rust syntax requires explicitly choosing type parameters when using generic
expressions, such as `BitVec::<Order, Store>::new()`, and will not substitute in
the default parameters when attempting to elide the parameters with
`BitVec::new()`. However, Rust *will* use the default type parameters in pattern
types: `let bv: BitVec = BitVec::new();` will use the default type parameters in
the `: BitVec` type annotation, which then completes the type of the expression
on the right side of the assignment `=`.

[ptc]: ./type-parameters/provided.html "Provided Types"
