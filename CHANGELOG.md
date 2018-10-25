# Changelog

All notable changes will be documented in this file.

## 0.7.0

### Added

- `examples/readme.rs` tracks the contents of the example code in `README.md`.
  It will continue to do so until the `external_doc` feature stabilizes so that
  the contents of the README can be included in the module documentation of
  `src/lib.rs`.

- Officially use the Rust community code of conduct.

- README sections describe why a user might want this library, and what makes it
  different than `bit-vec`.

### Changed

- Update minimum Rust version to `1.30.0`.

  Internally, this permits use of `std` rather than `::std`. This compiler
  edition does not change *intra-crate* macro usage. Clients at `1.30.0` and
  above no longer need `#[macro_use]` above `extern crate bitvec;`, and are able
  to import the `bitvec!` macro directly with `use bitvec::bitvec;` or
  `use bitvec::*;`.

  Implementation note: References to literals stabilized at *some* point between
  `1.20.0` and `1.30.0`, so the static bool items used for indexing are no
  longer needed.

- Include numeric arithmetic as well as set arithmetic in the README.

## 0.6.0

### Changed

- Update minimum Rust version to `1.25.0` in order to use nested imports.
- Fix logic in `Endian::prev`, and re-enabled edge tests.
- Pluralize `BitSlice::count_one()` and `BitSlice::count_zero()` function names.
- Fix documentation and comments.
- Consolidate implementation of `bitvec!` to not use any other macros.

## 0.5.0

### Added

- `BitVec` and `BitSlice` implement `Hash`.

- `BitVec` fully implements addition, negation, and subtraction.

- `BitSlice` implements in-place addition and negation.
  - `impl AddAssign for BitSlice`
  - `impl Neg for &mut BitSlice`

  This distinction is required in order to match the expectations of the
  arithmetic traits and the realities of immovable `BitSlice`.

- `BitSlice` offers `.all()`, `.any()`, `.not_all()`, `.not_any()`, and
  `.some()` methods to perform n-ary Boolean logic.
  - `.all()` tests if all bits are set high
  - `.any()` tests if any bits are set high (includes `.all()`)
  - `.not_all()` tests if any bits are set low (includes `.not_all()`)
  - `.not_any()` tests if all bits are set low
  - `.some()` tests if any bits are high and any are low (excludes `.all()` and
    `.not_all()`)

- `BitSlice` can count how many bits are set high or low with `.count_one()` and
  `.count_zero()`.

## 0.4.0

### Added

`BitSlice::for_each` provides mutable iteration over a slice. It yields each
successive `(index: usize, bit: bool)` pair to a closure, and stores the return
value of that closure at the yielded index.

`BitVec` now implements `Eq` and `Ord` against other `BitVec`s. It is impossible
at this time to make `BitVec` generic over anything that is `Borrow<BitSlice>`,
which would allow comparisons over different ownership types. The declaration

```rust
impl<A, B, C, D, E> PartialEq<C> for BitVec<A, B>
where A: Endian,
    B: Bits,
    C: Borrow<BitSlice<D, E>>,
    D: Endian,
    E: Bits,
{
    fn eq(&self, rhs: E) { … }
}
```

is impossible to write, so `BitVec == BitSlice` will be rejected.

As with many other traits on `BitVec`, the implementations are just a thin
wrapper over the corresponding `BitSlice` implementations.

### Changed

Refine the API documentation. Rust guidelines recommend imperative rather than
descriptive summaries for function documentation, which largely meant stripping
the trailing -s from the first verb in each function document.

I also moved the example code from the trait-level documentation to the
function-level documentation, so that it would show up an `type::func` in the
`rustdoc` output rather than just `type`. This makes it much clearer what is
being tested.

### Removed

`BitVec` methods `iter` and `raw_len` moved to `BitSlice` in `0.3.0` but were
not removed in that release.

The remaining debugging `eprintln!` calls have been stripped.

## 0.3.0

Split `BitVec` off into `BitSlice` wherever possible.

### Added

- The `BitSlice` type is the `[T]` to `BitVec`'s `Vec<T>`. `BitVec` now `Deref`s
  to it, and has offloaded all the work that does not require managing allocated
  memory.
- Almost all of the public API on both types has documentation and example code.

### Changed

- The implementations of left- ard right- shift are now faster.
- `BitVec` can `Borrow` and `Deref` down to `BitSlice`, and offloads as much
  work as possible to it.
- `Clone` is more intelligent.

## 0.2.0

Improved the `bitvec!` macro.

### Changed

- `bitvec!` takes more syntaxes to better match `vec!`, and has better
  runtime performance. The increased static memory used by `bitvec!` should be
  more than counterbalanced by the vastly better generated code.

## 0.1.0

Initial implementation and release.

### Added

- `Endian` and `Bits` traits
- `BitVec` type with basic `Vec` idioms and parallel trait implementations
- `bitvec!` generator macro
