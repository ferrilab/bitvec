# Atomic Behavior

Most computers do not offer machine-code instructions capable of manipulating
exactly one bit in a register. Some embedded architectures have such
instructions, since they are very useful for device-register manipulation, but
even so, no high-level language offers syntax for bit access. That is, after
all, why this crate exists.

Bits are manipulated by reading from memory into a register, modifying the whole
register, and writing the modified register back out.

This is the classic example of data race errors: two threads read the same data,
modify their copy independently of each other, and then write their copies back
to the same spot. The faster thread’s write is clobbered by the slower thread’s,
and that event is lost entirely.

Rust ordinarily prevents such problems with compile-time analysis.

`bitvec` purposefully clouds such analysis, allowing race conditions to manifest
in memory errors.

## Problem

`BitSlice::split_at_mut` is empowered to split a single `&mut BitSlice` into
two smaller mutable bit slices. The library ensures that these slices are not
overlapping in each others’ bits, but it is both valid and encouraged for those
slices to share the same *underlying storage element*.

Since `&mut BitSlice` is `Send`, adjacent mutable bit slices can be sent to
different threads, modify themselves, and create the exact data race scenario
described above.

## Solution

The simplest solution is “don’t do that”, but, that’s not how Rust is supposed
to work.

The second simplest solution is to use CPU capabilities to enforce uninterrupted
read/modify/write sequences in single modifications. The exact details are left
as implementation details of the CPU and the Rust standard library, but in
`1.34.0`, the atomic wrapper types stabilized to allow the desired behavior.

This problem does not require any ordering constraints or relationships. Rust
already guarantees us that each bit in memory can be the property of exactly one
`&mut BitSlice` writer at any given moment, and all bits in memory are
independent of each other. As such, all we need is to ensure that once a memory
location is read at the beginning of a modification sequence, no other thread
can read from it until after the write back concludes.

This is the `core::sync::atomic::Ordering::Relaxed` constraint.

## Implementation

The `BitStore::set_at` method is the only function in the whole library that
writes to memory regions. Changing it from

```rust,ignore
if (bit) {
  *self |= 1 << place;
}
else {
  *self &= !(1 << place);
}
```

to

```rust,ignore
let aptr: *const Atomic<T> = &self as *const Atomic<T>;
if (bit) {
  unsafe { &*aptr }.fetch_or(1 << place);
}
else {
  unsafe { &*aptr }.fetch_and(!(1 << place));
}
```

is sufficient to introduce atomic read/modify/write instructions rather than the
default unsynchronized instructions.

The exact implementation is slightly more complex, because Rust does not provide
atomicity as a wrapper property of the fundamental types, but as sibling types.
This required storing the name of the atomic sibling type as an associated type
in the `BitStore` trait, and using `Self::Atom` instead of `Atomic<T>`, though
the latter would have been a nicer design.

This is a design document about `bitvec`, not a complaint about the Rust
standard library, so I will end here.
