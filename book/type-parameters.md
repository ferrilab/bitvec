# Type Parameters

`bitvec` uses type parameters to permit precise user control of its behavior and
in-memory representation. The Rust generic system permits `bitvec` to have a
more powerful and capable behavior than any other bitstream library yet
implemented in any language.

All `bitvec` types take two type parameters. The first denotes the storage type
being used: for everything but `BitArray`, this is an implementor of the
[`BitStore`] trait, and denotes the integer component of an underlying slice;
for `BitArray`, it is an implementor of [`BitViewSized`], and is the entire
storage block. The second is an implementor of [`BitOrder`], and informs how the
structure translates a semantic index into a memory access.

The combination of these two parameters governs how a `bitvec` type computes its
accesses to memory.

The next two chapters describe each trait and their implementors in more detail.
You may be able to skip them with this sentence as a good-enough summary:

Use `<Lsb0, usize>` as the parameters if you are implementing a collection and
do not care about memory layout; if you are implementing an I/O protocol
specification, the specification document will tell you what ordering and unit
size it requires.

----

Rust syntax requires explicitly choosing type parameters when using generic
expressions, such as `BitVec::<Store, Order>::new()`, and will not substitute in
the default parameters when attempting to elide the parameters with
`BitVec::new()`. However, Rust *will* use the default type parameters in
patterns: `let bv: BitVec = BitVec::new();` will use the default type parameters
in the `: BitVec` type annotation, which then completes the type of the
expression on the right side of the assignment `=`.

[`BitOrder`]: https://docs.rs/bitvec/latest/bitvec/order/trait.BitOrder.html
[`BitStore`]: https://docs.rs/bitvec/latest/bitvec/store/trait.BitStore.html
[`BitViewSized`]: https://docs.rs/bitvec/latest/bitvec/view/trait.BitViewSized.html
