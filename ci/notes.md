# Notes on Cross Targets

`bitvec` is primarily developed on the `x86_64-unknown-linux-gnu`,
`x86_64-apple-darwin`, and `aarch64-unknown-linux-gnu` targets. It is
tested for the other supported Rust targets using the cross-compile and
emulation tools available to us.

Because of the limitations in environmental awareness available to
crates about their destination targets, there are some oddities that we
currently are unable to detect or work around in source code, and
instead merely tolerate in our processes.

## Serde Discrepancies

On these targets, Serde does not define its traits on atomic types. However,
these targets *do* possess the atomic types, so the test suite errors when
attempting to assert that `bitvec`’s types (which do exist) implement the Serde
traits (which are gated on Serde’s own implementations).

Since `rustc` does not provide the precise target string as a `#[cfg()]` value,
these cannot be excluded in source code.

The `ci/target_{test,check}_no_serde.txt` files list all targets where Serde
disagrees with `radium` on atomic presence, and thus where our Serde
implementation tests cannot compile.

## Standard Library

The `ci/target_{test,check}_no_std.txt` files list targets that either do not
have a standard library at all, or where the standard library is insufficient to
operate the test suite (notably, certain WASM targets are unsupported by `rand`,
so the test suite cannot produce random data on them).

## Testing vs Check-Only

The `ci/target_check_*.txt` files do not have Cross images available where the
test suite can be executed as a target program. As such, we can only check that
`bitvec` builds correctly for these targets, but we cannot emulate them to
execute the tests directly.

In general, this is considered acceptable, as `bitvec` has no logic that is
strongly dependent on the precise target that is not *already* covered by the
distribution’s own infrastructure.

However, we still strive to run the test suite on every target possible, and
should promote targets from `_check_` to `_test_` if Cross gains support for
them.
