################################################################################
#                                   Justfile                                   #
#                                                                              #
# Set of routines to execute for development work. As of 2019-05-01, `just`    #
# does not work on Windows.                                                    #
################################################################################

# Builds the library.
build:
	cargo build --no-default-features
	cargo build --no-default-features --features alloc
	cargo build --all-features
	cargo build --all-features --example sieve
	cargo build --all-features --example tour

# Checks the library for syntax and HIR errors.
check:
	cargo check --no-default-features
	cargo check --no-default-features --features alloc
	cargo check --all-features

# Runs all of the recipes necessary for pre-publish.
checkout: check clippy build doc test package

# Continually runs the development routines.
ci:
	just loop dev

# Removes all build artifacts.
clean:
	cargo clean

# Runs clippy.
clippy: check
	cargo clippy --no-default-features
	cargo clippy --no-default-features --features alloc
	cargo clippy --all-features

# Runs the development routines.
dev: clippy doc test

# Builds the crate documentation.
doc:
	cargo doc --all-features --document-private-items

# Continually runs some recipe from this file.
loop action:
	cargo watch -s "just {{action}}"

miri:
	cargo +nightly miri test

# Packages the crate in preparation for publishing on crates.io
package:
	cargo package --allow-dirty

# Publishes the crate to crates.io
publish: checkout
	cargo publish

# Runs the test suites.
test: check clippy
	cargo test --no-default-features
	cargo test --all-features
	cargo run --all-features --example sieve
	cargo run --all-features --example tour
