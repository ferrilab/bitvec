# Changelog

All notable changes will be documented in this file.

This document is written according to the [Keep a Changelog][kac] style.

1. [Version 1](#version-1)
   1. [1.0.1](#101)
   1. [1.0.0](#100)
1. [Version 0 (Prototyping)](#version-0-prototyping)
   1. [0.22](#022)
   1. [0.21](#021)
   1. [0.20](#020)
   1. [0.19](#019)
   1. [0.18](#018)
   1. [0.17](#017)
   1. [0.16](#016)
   1. [0.15](#015)
   1. [0.14](#014)
   1. [0.13](#013)
   1. [0.12](#012)
   1. [0.11](#011)
   1. [0.10](#010)
   1. [0.9](#09)
   1. [0.8](#08)
   1. [0.7](#07)
   1. [0.6](#06)
   1. [0.5](#05)
   1. [0.4](#04)
   1. [0.3](#03)
   1. [0.2](#02)
   1. [0.1](#01)

## Version 1

`bitvec`’s initial development is now complete, and uses the one-dot series. It
will continue to receive maintenance, but its API is now stable and **will not**
change until const-generics allow `BitArray` to be rewritten.

### 1.0.1

#### Notes

Performance regressions have been reported between the development series `0.20`
onwards and `1.0`. It appears at least some of these regressions are due to the
removal of the `#[inline]` attribute on `bitvec` public functions.

This attribute has been applied to *all* `bitvec` functions. You may see
regressions in size of your final artifact, but you should also see improvements
in your runtime speed. This is being tracked in [`sharksforarms/deku#246`].

#### Changes

- The `bits![static mut …]` invocation has been made `unsafe` at the invocation
  site, in response to [Issue #156] filed by GitHub user [@SimonSapin].

  This is technically an API break (formerly safe code now requires an `unsafe`
  block) but as no run-time behavior or compile-time types have changed except
  for this, and Rust considers breaking incorrect code to be acceptable within
  SemVer patches, I am publishing it as a patch.

- GitHub user [@dtolnay] fixed incorrect `serde` behaviors in
  [Pull Request #185]. This behavior was first reported in [Issue #167] by
  GitHub user [@Nelarius].

- Compilation no longer depends on environment variables set by Cargo, as
  requested in [Pull Request #162] by GitHub user [@rocallahan].

- The `bitvec![val; len]` macro can again take `len` as a runtime value as well
  as a compile-time constant. [Pull Request #160] was provided by GitHub user
  [@coolreader18].

- The return types of `slice::Iter::by_{refs,vals}` are restored to named types,
  rather than `impl Iterator...` opaque types. This allows them to be used
  directly in other sites. This defect was reported in [Issue #169] by GitHub
  user [@dignifiedquire].

### 1.0.0

🚨 **THIS IS A BREAKING CHANGE RELEASE!** 🚨

Your code *has* broken. You *will* need to change it in order to use this. This
work on your part *is* worth it.

This release has a *great deal* of changes from the `0.22` development series!
Most breaking changes should have reasonable error messages indicating how they
can be repaired.

Removed APIs *do not* have deprecation notices! Use of removed APIs will fail to
compile. You **must** check this changelog, or the crate documentation, to find
out appropriate replacements.

#### Type Parameter Reördering

The `<O, T>` type parameter pair that has existed since `0.10` is **reversed**
to be `<T, O>`! This will cause all of your type definitions to fail, as
suddenly all of your chosen type arguments do not satisfy the demanded traits.

This change was made in accordance with [Issue #136], requested by GitHub user
[@changhe3].

#### Additional Changes

- The MSRV is raised to `1.56`.
- `BitField` now supports signed integers! `BitMemory` is completely removed.
- `BitSlice::from_slice{,_mut}` are now infallible constructors, and panic when
  the source is too long. The original fallible behavior is renamed to
  `BitSlice::try_from_slice{,_mut}`.
- the `{Bit,}DomainMut` types have been removed. The `{Bit,}Domain` types now
  take a `Mutability` type parameter instead. The `.{bit_,}domain{,_mut}()`
  methods on `BitSlice` exist as normal, but have changed their return types to
  specify a `Const` or `Mut` type parameter rather than `{Bit,}Domain` or
  `{Bit,}DomainMut`, respectively.
- `Iter::by_{ref,val}` are renamed to `by_{ref,val}s`, to prevent collision with
  `Iterator::by_ref`.
- The long-standing behavior of the `&=`, `|=`, and `^=` operators has been
  changed! They now operate *directly on data structures*, rather than routing
  through iterators. If you want to perform boolean arithmetic using arbitrary
  `bool` streams, use iterator combinators like
  `.iter_mut().zip(stream).for_each(|(mut orig, new)| *orig ^= new)`. This
  change allows the arithmetic implementations to be accelerated when working
  between bit-slices of equal types.
- `BitSlice::set_all` is removed, as the standard-library API `[T]::fill`
  replaces it.
- `BitSlice::offset_from` is removed. Use `.as_bitptr().offset_from()`.
- `BitSlice::as_raw_slice` is removed. Use `.domain()` to access the underlying
  memory.

#### Documentation

Module and type documentation have been lifted into the `doc/` tree as Markdown
files. The [user guide], in `book/` has been more thoroughly rewritten.

Please file any problems or confusions about the documentation as an issue! The
documentation is a project artifact equally, if not more, important as the
Rust library.

#### Dependency Raises

As part of the migration of incidental logic out of `bitvec`, the following
utility libraries have been updated:

- `funty 2.0` provides a more comprehensive coverage of the language primitives.
- `wyz 0.5` contains more logic formerly in the utility module, as well as a
  stronger system for generalizing over references.

## Version 0 (Prototyping)

`bitvec`’s first three and a half years of development used the zero-dot series
as it explored its behavior. These versions are now deprecated and will not
receive further support. They are listed only in summary, and may be removed
from crates.io in the future.

### 0.22

- Raised MSRV to `1.51` for const generics.
- Named the iterators produced by `Iter::by_{ref,val}`.
- Fixed [Issue #114], reported by GitHub user [@VilleHallivuori].
- Extracted pointer mutability tracking to `wyz 0.4`.

### 0.21

- Raised `funty` dependency to `~1.2`.
- Moved bit-array typename construction out of `bitarr!` and into `BitArr!`.
- Created `BitVec::from_{element,slice}` constructors for [Issue #6], reöpened
  by GitHub user [@HamishWMC].
- Fixed the behavior of `BitSlice::{first,last}_{one,zero}`, requested in
  [Issue #103] by GitHub user [@seanyoung].
- Added `BitSlice::{leading,trailing}_{ones,zeros}`, also in #103 by @seanyoung.
- Added `static` to the `bits!` argument for hidden-static construction.
- Accelerate `Iter{Ones,Zeros}` with specialization.
- [Pull Request #104] by GitHub user [@ordian] fixed crashing when calling
  `BitVec::insert` exactly at `self.len()`.

### 0.20

- Allowed use of atomic and `Cell` types as the original storage type.
- Added bit-seeking APIs (`.iter_{ones,zeros}`) to match APIs in [`bit-set`],
  requested in [Issue #83] by GitHub user [@arucil].
- Refined the `<T: Unsigned as BitStore>::Alias` system to prevent improper
  mutation.
- Implemented `IntoIterator` on `BitArray`.
- Construct `BitVec` from integer elements, not just bits.
- Added `.remove_alias()` to mutable-bit-slice iterators.
- Ported more of `core::ptr` as `bitvec::ptr`.
- Renamed `BitMut` to `BitRef` and create single-bit `BitPtr` pointers.
- Created `BitPtrRange` as an analogue to `Range<*bool>`.
- Removed deprecated `BitView` methods.

### 0.19

- Accelerated `BitSlice::copy_from_bitslice`
- Created `BitSlice::offset_from` to enable computing how far into a base
  bit-slice a subslice begins.
- Used `radium 0.5`’s stronger type system, including fallback aliases when
  targets do not have atomics.
- Changed internal implementation of the macro constructors.

### 0.18

- Raised MSRV to `1.44`.
- Renamed the C-compatible ordering `Local` to `LocalBits`.
- Fixed an incomplete change of default type parameters from `LocalBits` to
  `Lsb0`.
- Introduced the `BitStore::Alias` system for coöperative mutation.
- Reärranged the view conversion traits, creating `BitView` alongside `AsBits`
  and `AsBitsMut`.
- Greatly improved cross-compile testing with a CI suite by [@AlexHuszagh].
- Removed numeric arithmetic, per [Issue #17] (by me) and [Issue #50] by GitHub
  user [@luojia65].
- Created `BitArray`, as requested in [Issue #32] by GitHub user
  [@FedericoPonzi]. This also includes a `bitarr!` constructor.
- Merged [Pull Request #68] by GitHub user [@sharksforarms].
- Fixed [Issue #69] by GitHub user [@YoshikiTakashima].
- Per [Issue #75] by GitHub user [@diondokter], `BitMemory` describes all
  unsigned integers, not just `BitStore` implementors, and `BitField` can
  transact them all.

### 0.17

- In [Pull Request #34], GitHub user [@mystor] provided a `bits!` implementation
  that encodes buffers at compile time, and allows them to be borrowed as
  `BitSlice`s.
- Renamed `Cursor` to `BitOrder`, and `LittleEndian` and `BigEndian` to `Lsb0`
  and `Msb0`.
- Removed the `Words` alias, and implemented `BitStore` on `usize.
- Removed the `As{Ref,Mut}<BitSlice<_, T>>` implementations for `[T]`, as
  requested in [Issue #35] by GitHub user [@Fotosmile].
- Fixed [Issue #40] with [Pull Request #41], both provided by GitHub user
  [@ImmemorConsultrixContrarie].
- Fixed [Issue #43], reported by GitHub users [@AlexHuszagh] and [@obeah].
- Fixed an improper deällocation, per [Issue #55] reported by GitHub user
  [@kulp].

### 0.16

- Created `Cursor::mask` for faster direct memory access.
- Created the `BitField` trait.
- Added a `Word` alias to the target’s `usize` equivalent (now just `usize`).
- Created a `Local` implementation of `Cursor` (now the `LocalBits` alias).
- Changed default type parameters to `<Local, Word>`.
- Created the `index` module, reducing runtime assertions.
- Fixed [Issue #33], reported by GitHub sure [@jonas-schievink], which addressed
  incorrect reällocation in `BitVec::reserve`.
- Updated `radium` dependency to `0.3`, fixing [Issue #36] reported by GitHub
  user [@lynaghk].

### 0.15

- Raised MSRV to `1.36`.
- Reärranged the feature set to use the now-available `extern crate alloc;`.
- Conditionally remove `Send` from `BitSlice`.
- Improve the `bitvec!` repetition constructor, as reported in [Issue #28] by
  GitHub user [@caelunshun].

### 0.14

- Added reversed (left-to-right) addition, requested in [Issue #16] by GitHub
  user [@GeorgeGkas].

### 0.13

- Changed the bit-region pointer encoding to its final form.

### 0.12

- Created `BitSlice::at`, which manifests a proxy reference to a single bit.
- Renamed `Bits` to `BitStore`
- Created the `Bits` and `BitsMut` traits to view ordinary memory as a
  bit-slice.

### 0.11

- Raised the MSRV to `1.33`.
- Created the `domain` module, which manages all translations of bit-precision
  views into raw underlying memory.
- Added a `bitbox!` macro constructor.
- Improved the bit-region pointer encoding.
- `BitBox` and `BitVec` are now `Sync`, per discussions with [@ratorx].
- Implemented `serde` support (behind the `serde` feature).
- Began working with atomics.
- Fixed [Issue #9], reported by GitHub user [@torce].
- Fixed [Issue #10], reported by GitHub user [@overminder].
- Fixed [Issue #12], reported by GitHub user [@koushiro].
- Fixed [Issue #15], reported by GitHub user [@schomatis].

### 0.10

- Raised the MSRV to `1.31`.
- Created the `BitPtr` (now `BitSpan`) pointer encoding that enables addressing
  any bit, not just the front of an element.
- Fixed [Issue #7], reported by GitHub user [@geq1t], repairing
  `.count_{ones,zeros}` inside single-element bit-slices.
- Fixed [Issue #8], reported by GitHub user [@ratorx], implementing `Send` and
  `Sync` on `BitSlice`.
- Disallowed `u64` on 32-bit targets.

### 0.9

- Renamed `Endian` to `Cursor` (now `BitOrder`)
- Removed `Default` bound on `Bits` (now `BitStore`)

### 0.8

- Added `alloc` and `std` features in [Pull Request #3] by GitHub user
  [@rphmeier].

### 0.7

- Raised MSRV to `1.30`.
- Created the `prelude` module.
- Adopted the Rust CoC.

### 0.6

- Raised MSRV to `1.25`.
- Renamed `.count_{one,zero}` to `.count_{ones,zeros}`.

### 0.5

- Implemented `Hash`.
- Created numeric 2’s-complement arithmetic implementations.
- Created set-testing methods (`all`, `any`, `not_all`, `not_any`, `some`,
  `count_one`, `count_zero`).

### 0.4

- Added `BitSlice::for_each`.
- Added more trait implementations.

### 0.3

- Added `BitSlice`, and offloaded much of the `BitVec` API to it.

### 0.2

- Expanded `bitvec!` argument syntax, and improved its codegen.

### 0.1

- Created `BitVec` and `bitvec!`.
- Created `Endian` (now `BitOrder`) and `Bits` (now `BitStore`) traits.

<!-- Credits -->

[@AlexHuszagh]: https://github.com/AlexHuszagh
[@FedericoPonzi]: https://github.com/FedericoPonzi
[@Fotosmile]: https://github.com/Fotosmile
[@GeorgeGkas]: https://github.com/GeorgeGkas
[@HamishWMC]: https://github.com/HamishWMC
[@ImmemorConsultrixContrarie]: https://github.com/ImmemorConsultrixContrarie
[@Nelarius]: https://github.com/Nelarius
[@SimonSapin]: https://github.com/SimonSapin
[@VilleHallivuori]: https://github.com/VilleHallivuori
[@YoshikiTakashima]: https://github.com/YoshikiTakashima
[@arucil]: https://github.com/arucil
[@caelunshun]: https://github.com/caelunshun
[@changhe3]: https://github.com/changhe3
[@coolreader18]: https://github.com/coolreader18
[@dignifiedquire]: https://github.com/dignifiedquire
[@diondokter]: https://github.com/diondokter
[@dtolnay]: https://github.com/dtolnay
[@geq1t]: https://github.com/geq1t
[@jonas-schievink]: https://github.com/jonas-schievink
[@koushiro]: https://github.com/koushiro
[@kulp]: https://github.com/kulp
[@luojia65]: https://github.com/luojia65
[@lynaghk]: https://github.com/lynaghk
[@mystor]: https://github.com/mystor
[@obeah]: https://github.com/obeah
[@ordian]: https://github.com/ordian
[@overminder]: https://github.com/overminder
[@ratorx]: https://github.com/ratorx
[@rocallahan]: https://github.com/rocallahan
[@rphmeier]: https://github.com/rphmeier
[@schomatis]: https://github.com/schomatis
[@seanyoung]: https://github.com/seanyoung
[@sharksforarms]: https://github.com/sharksforarms
[@torce]: https://github.com/torce

<!-- Issues -->

[Issue #6]: https://github.com/bitvecto-rs/bitvec/issues/6
[Issue #7]: https://github.com/bitvecto-rs/bitvec/issues/7
[Issue #8]: https://github.com/bitvecto-rs/bitvec/issues/8
[Issue #9]: https://github.com/bitvecto-rs/bitvec/issues/9
[Issue #10]: https://github.com/bitvecto-rs/bitvec/issues/10
[Issue #12]: https://github.com/bitvecto-rs/bitvec/issues/12
[Issue #15]: https://github.com/bitvecto-rs/bitvec/issues/15
[Issue #16]: https://github.com/bitvecto-rs/bitvec/issues/16
[Issue #17]: https://github.com/bitvecto-rs/bitvec/issues/17
[Issue #28]: https://github.com/bitvecto-rs/bitvec/issues/28
[Issue #32]: https://github.com/bitvecto-rs/bitvec/issues/32
[Issue #33]: https://github.com/bitvecto-rs/bitvec/issues/33
[Issue #35]: https://github.com/bitvecto-rs/bitvec/issues/35
[Issue #36]: https://github.com/bitvecto-rs/bitvec/issues/36
[Issue #40]: https://github.com/bitvecto-rs/bitvec/issues/40
[Issue #43]: https://github.com/bitvecto-rs/bitvec/issues/43
[Issue #50]: https://github.com/bitvecto-rs/bitvec/issues/50
[Issue #55]: https://github.com/bitvecto-rs/bitvec/issues/55
[Issue #69]: https://github.com/bitvecto-rs/bitvec/issues/69
[Issue #75]: https://github.com/bitvecto-rs/bitvec/issues/75
[Issue #83]: https://github.com/bitvecto-rs/bitvec/issues/83
[Issue #103]: https://github.com/bitvecto-rs/bitvec/issues/103
[Issue #114]: https://github.com/bitvecto-rs/bitvec/issues/114
[Issue #136]: https://github.com/bitvecto-rs/bitvec/issues/136
[Issue #156]: https://github.com/bitvecto-rs/bitvec/issues/156
[Issue #167]: https://github.com/bitvecto-rs/bitvec/issues/167
[Issue #169]: https://github.com/bitvecto-rs/bitvec/issues/169

<!-- Pull Requests -->

[Pull Request #3]: https://github.com/bitvecto-rs/bitvec/pull/3
[Pull Request #34]: https://github.com/bitvecto-rs/bitvec/pull/34
[Pull Request #41]: https://github.com/bitvecto-rs/bitvec/pull/41
[Pull Request #68]: https://github.com/bitvecto-rs/bitvec/pull/68
[Pull Request #104]: https://github.com/bitvecto-rs/bitvec/pull/104
[Pull Request #160]: https://github.com/bitvecto-rs/bitvec/pull/160
[Pull Request #162]: https://github.com/bitvecto-rs/bitvec/pull/162
[Pull Request #185]: https://github.com/bitvecto-rs/bitvec/pull/185

<!-- Other -->

[`bit-set`]: https://crates.io/crates/bit-set
[`sharksforarms/deku#246`]: https://github.com/sharksforarms/deku/pull/246
[kac]: https://keepachangelog.com/en/1.0.0/
[user guide]: https://bitvecto-rs.github.io/bitvec/
