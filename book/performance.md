# Runtime Performance

`bitvec` increases the instruction cost of each access to a `bool` in its data
structures. This is an inevitable consequence of the fact that, even on
architectures that have them, compilers typically do not emit object code
instructions that access individual bits within a memory location. Therefore,
each access in `bitvec` has, in addition to a memory operation, one or two
shift instructions one or two `AND`/`OR`/`NOT` instructions.

This means that, inevitably, `bitvec` is slower in CPU time than `[bool]` is.
Measurements indicate roughly a factor of ten, but with also about 10x more
variance. However, this cost is only apparent *and meaningful* when walking the
entirety of very large buffers, and tends to fade into noise on smaller buffers,
or be obviated by compile-time fixed accesses. As always, try it on a
representative workload.

## Benchmarking

I have tried (with admittedly low priority) to have some benchmarks in the
project to back up my claims that `bitvec` is fast. This has been difficult to
maintain for a few reasons, but I have at least a few that have stayed present
in order to demonstrate important claims, such as showing that specialization
for matching types does provide massive performance benefits (it does).

In particular, LLVM is *very good* at propagating compile-time constants through
the code, and `bitvec` strives to maintain an internal implementation that is
easily accessible to optimizers. This means that basically any benchmark that
takes input from a source file that the compiler can see gets artificially
solved during codegen.

For instance, I don’t know how long it takes to construct a `&BitSlice` view
over memory, because my benchmarks report 0ns: LLVM computes my pointer encoding
at compile time, and a consequence of the way I designed my pointer encoding is
that the only operation `BitSlice::from_slice` actually performs is `.len << 3`.
When LLVM can see the original length, it just does this itself, and emits an
immediate with the correct length instead of the constructor call.

Other constructor benchmarks are only showing me the time required to run
`memcpy`, and arbitrary indexing just shows the time required to run three
instructions, because LLVM solved the shift/mask arguments ahead of time.

The important takeäway here is that if your code is at all dependent on
constants that the compiler can see, and is not exclusively performing indexing
based on runtime inputs, then `bitvec` is going to be *plenty* fast.

## Specialization

`bitvec` strives to use its knowledge of the underlying memory representation
wherever possible. This means that operations between `BitSlice`s with the same
type parameters can rely on an identical representation and use integer behavior
rather than walking each bit individually.

Try to do this wherever possible, especially in performance-sensitive code. You
typically should not be mixing `bitvec` structures with different type
parameters anyway: use the representation that serves your needs, and keep using
it in all buffers that interact with it.

As an example, as of 1.0, walking two large `BitSlice`s with incompatible type
parameters takes 3µs (microseconds), while walking the same sizes with
identical type parameters takes 100ns (nanoseconds). It’s roughly a 32x
performance difference, which is only half the speedup that I expected using
`usize` on a 64-bit machine, but still quite stark.
