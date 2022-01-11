# Miscellaneous Implementation Details

`bitvec` has a number of internal implementation details used to facilitate
development but are not part of the public API. While not user-facing, these
details are nevertheless important to document as explanations for how the
library is built.

## Integer Refinement

`bitvec` offloads abstraction over the fundamental integers to the `funty`
crate. It provides traits such as `Unsigned` that generalize over any unsigned
integer and allow them to be used in generic code.

`funty` only unifies the standard-library APIs of the integers into trait-based
code; `bitvec` further extends this with useful constants in the `BitRegister`
trait. This trait delimits the integers that correspond to machine registers
actually available for use as storage, and provides minor conveniences for
working with them.

## Specialization Hacks

`bitvec` is built to be agnostic to the ordering of bits within an element. This
is an important aspect of its design, and even if no other ordering than the
provided `Lsb0` and `Msb0` are used, *must* remain so that these two orderings
can be used on equal footing. However, the deferral of register operations to
type parameters outside of the data structures’ control results in some
unpleasant performance losses that would not occur in a hand-written equivalent.

Some operations, like copying between, or comparing, slices, can be accelerated
with partial-element access, but require knowledge of the `O` ordering type to
provide a semantic interpretation of register contents. Language-level
specialization could allow writing override `impl` blocks, like this:

```rust
impl<T, O> BitSlice<T, O>
where
  T: BitStore,
  O: BitOrder,
{
  fn eq(&self, other: &Self) -> bool {
    todo!("baseline")
  }
}

impl<T> BitSlice<T, Lsb0>
where T: BitStore {
  fn eq(&self, other: &Self) -> bool {
    todo!("lsb0-accelerated version")
  }
}

impl<T> BitSlice<T, Msb0>
where T: BitStore {
  fn eq(&self, other: &Self) -> bool {
    todo!("msb0-accelerated version")
  }
}
```

While waiting on this feature, we can use the compiler’s stable `TypeId` API to
simulate access to specialization. By comparing the `TypeId` of the `O` type
argument to the `TypeId`s of `bitvec`’s provided orderings, functions can detect
when they are in a monomorphization with an `Lsb0` or `Msb0` ordering argument
and specialize accordingly. The above block can be replaced with:

```rust
impl<T, O> BitSlice<T, O>
where
  T: BitStore,
  O: BitOrder,
{
  fn eq(&self, other: &Self) -> bool {
    if let (Some(this), Some(that)) = (
      self.coerce::<T, Lsb0>(),
      other.coerce::<T, Lsb0>(),
    ) {
      todo!("lsb0-accelerated version")
    }
    else if let (Some(this), Some(that)) = (
      self.coerce::<T, Msb0>(),
      other.coerce::<T, Msb0>(),
    ) {
      todo!("msb0-accelerated version")
    }
    else {
      todo!("baseline")
    }
  }
}
```

and, during monomorphization, only one branch of the `if` stack will be
preserved. The `.coerce()` method is defined in `slice::specialization` and
provides easy access to a fully-typed value only within the monomorphization
that matches it.
