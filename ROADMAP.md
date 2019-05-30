# `bitvec` Roadmap

This document lists out some future work items, with varying levels of detail
for their requirements or path to implementation.

## Consider a Fallible API

The current implementation relies on `panic!` for all error behavior. This has
unpleasant connotations for FFI work (Rust inserts catch-and-abort guards in all
`extern fn` items, but the presence of `panic!` requires linking `libunwind` or
setting `panic="abort"` in the compiler) and makes the library eagerly suicidal.

The invariant checking should be converted to, at minimum, `Option<T>`, and
ideally, `Result<T, impl failure::Error>`. `Option<T>` has the advantage that
all handles in the library have the null-value optimization in place, allowing
them to indicate nullability with no size penalty, and a fast compiled behavior
(test the slot against the zero value). `Result<T, impl failure::Error>` has
nicer behavior for the user, but incurs heavy cost that `Option<T>` does not.

Perhaps `Option<T>` and `log` macros would suffice? The majority use case will
never encounter obscure invalid states: Intra-language use will favor the
assurances of the `Bits`/`Mut` traits when creating `BitSlice` references, and
the allocator when creating `BitBox` and `BitVec` objects, to ensure that the
library will never see invalid state. Cross-language use cannot meaningfully
carry `Result` across the FFI boundary, and uses `Option` already.

Benefits: thread-killing `panic!` calls will be deferred to the caller, and the
multitude of `panic!` sites in the library will be reduced to test-and-return
rather than test-and-begin-unwind.

Costs: the Rust stdlib API is *not* `Option`al, and making this change would be
a *massive* usage break. While callers can largely ignore this by inserting `?`
everywhere the compiler complains, this requires making their functions fallible
also, or explicitly acknowledging all the possible `panic!` sites that will, in
practice, never fire by adding an `.unwrap()` call.

I will not support a feature flag to switch between these APIs. That is an
enormous maintenance cost that doubles the volume of the entire library.

## Use `const fn` Items

`bitvec` is a heavily generic library. Generic `const fn` items are gated on the
`#![feature(const_fn)]` (issue [#57563]) feature.

The foundation type in `bitvec` uses a union to perform pointer value
manipulation. `union` items in `const fn` items are gated on issue [#51909].

If/when these features, or equivalents, stabilize, the library can begin adding
`const` decorators to function items in `BitPtr`, and then propagate outward
from there as supported by the core/std libraries (`const fn` items can only
call other `const fn` items, so core/std must provide `core/std` before `bitvec`
can propagate `const`ness).

Immediate candidates:

- `BitPtr::<T>::empty`
- `BitPtr::<T>::empty_mut`
- `BitPtr::<T>::new_unchecked`
- `BitPtr::<T>::elements`
- `BitPtr::<T>::head`
- `BitPtr::<T>::tail`
- `BitPtr::<T>::region_data`
- `BitPtr::<T>::cursors`

Possible candidates:

- `BitPtr::<T>::pointer`
- `BitPtr::<T>::raw_parts`

- `BitSlice::<C, T>::empty` and `BitSlice::<C, T>::empty_mut`: These functions
  use slice reconstructors, which may not be `const fn`.

Not candidates:

- `BitPtr::<T>::uninhabited`:
  - `core::ptr::NonNull::<T>::new` is not `const fn`
  - `core::option::Option::<T>::unwrap_or_else` is not `const fn`
- `BitPtr::<T>::as_slice` and `BitPtr::<T>::as_mut_slice`
  - `slice::from_raw_parts` and `_mut` are not `const fn`
- `BitPtr::<T>::is_empty` and `BitPtr::<T>::len`
  - issue [#49146]: flow control (`if` and `match`) are illegal in `const fn`

[#49146]: https://github.com/rust-lang/rust/issues/49146
[#51909]: https://github.com/rust-lang/rust/issues/51909
[#57563]: https://github.com/rust-lang/rust/issues/57563
