/*! Tracking mutability through the trait system.

This module enables the pointer structure system to enforce
!*/

/// A marker trait for distinguishing `*const` vs `*mut` when working with
/// structs, rather than raw pointers.
pub(crate) trait Mutability {}

/// An immutable pointer.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Const;

impl Mutability for Const {
}

/// A mutable pointer. Contexts with a `Mutable` may lower to `Immutable`, then
/// re-raise to `Mutable`; contexts with `Immutable` may not raise to `Mutable`
/// on their own.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct Mut;

impl Mutability for Mut {
}
