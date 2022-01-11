# BitStore

The [`BitStore`] trait governs the processor behaviors used to interact with the
memory of a `BitSlice` buffer. These include both the width of the processor
register used to contain a memory element, and the load/store instructions the
processor uses to move data across the memory bus.

`BitStore` has no behavior of its own, and serves only to collect associated
types and constants. It cannot be implemented outside `bitvec`, and is a closed
portion of the API. You can freely use the trait as a bound in types that
contain `bitvec` structures, but should not otherwise attempt to make use of it.

## Implementations

`BitStore` is implemented on all unsigned integer types not larger than a target
processor’s word size, all `Cell<T>` wrappers of them (as `Cell` is a compiler
directive), and their `AtomicT` variants.

Not all processors have atomic instructions for all their scalar registers. The
compiler maintains a list of all atomics available on all supported targets, and
exposes this list as unstable attributes in the standard library, unavailable to
user code such as `bitvec`. `bitvec` uses the [`radium`] crate (which I also
maintain) to provide information about atomic support for a register width, and
`radium` maintains a best-effort guess at what atomics are available.

On architectures with missing atomics, `bitvec`’s default feature set will cause
a compiler error when you attempt to instantiate a `bitvec` structure with the
register that is missing an atomic variant. You can fix this by using a narrower
register that does have atomic instructions, or by disabling `default-features`
and not enabling the `"atomic"` feature. ***Please*** file an issue with
[`radium`] with your target and failing type, so that we can improve our
precision.

## Associated Types

The `Mem` associated type names the scalar integer corresponding to the
`BitStore` type. `u8`, `Cell<u8>`, and `AtomicU8` all implement `BitStore` with
their `Mem` type assigned as `u8`; the same is true for the wider registers.

This type is used to create selection masks in the processor and permit access
to unaliased memory.

The `Access` associated type names the type used to implement memory access. The
`BitAccess` trait is an internal bridge to `Radium` that allows a consistent
memory API, regardless of instructions used. All reads from and writes to memory
route through this association and trait.

Lastly, the `Alias` associated type enables `bitvec` to gracefully and correctly
handle events that cause multiple handles to alias the same memory address. This
association is used in `.split_at_mut()` to select the alias-aware type used for
all subsequent accesses.

The `Mem` and `Alias` types are exposed in public APIs according to local alias
information. The `Access` type is never publicly exposed, and only used for code
generation.

[`BitStore`]: https://docs.rs/bitvec/latest/bitvec/store/trait.BitStore.html
[`radium`]: https://github.com/mystor/radium/
