/*! Reference-counted bit-slices.

This module provides analogues to [`Rc<[bool]>`][rc] and [`Arc<[bool]>`][arc],
with some modifications or allowances for `bitvec`’s type system.

[arc]: alloc::sync::Arc
[rc]: alloc::rc::Rc
!*/

#![cfg(feature = "alloc")]

mod boxed;
mod strong;
mod weak;

use core::cell::Cell;

use radium::types::RadiumUsize;

pub use self::{
	strong::BitRefStrong,
	weak::BitRefWeak,
};
pub use crate::{
	bitarc,
	bitrc,
};

/// A thread-unsafe strong reference handle, equivalent to `Rc<[bool]>`.
pub type BitRc<O, T> = BitRefStrong<Cell<usize>, O, T>;

/// A thread-safe strong reference handle, equivalent to `Arc<[bool]>`.
pub type BitArc<O, T> = BitRefStrong<RadiumUsize, O, T>;

/// A thread-unsafe weak reference handle, equivalent to `rc::Weak<[bool]>`.
pub type BitRcWeak<O, T> = BitRefWeak<Cell<usize>, O, T>;

/// A thread-safe weak reference handle, equivalent to `sync::Weak<[bool]>`.
pub type BitArcWeak<O, T> = BitRefWeak<RadiumUsize, O, T>;

#[cfg(test)]
mod tests;
