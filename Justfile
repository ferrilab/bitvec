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
checkout: format check lint build doc test package

# Continually runs the development routines.
ci:
	just loop dev

# Removes all build artifacts.
clean:
	cargo clean

# Runs the development routines.
dev: format lint doc test

# Builds the crate documentation.
doc:
	cargo doc --all-features --document-private-items

# Runs the formatter on all Rust files.
format:
	cargo +nightly fmt -- --config-path rustfmt-nightly.toml

# Runs the linter.
lint: check
	cargo clippy --no-default-features
	cargo clippy --no-default-features --features alloc
	cargo clippy --all-features

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
test: check lint
	cargo test --no-default-features
	cargo test --all-features
	cargo run --all-features --example ipv4
	cargo run --all-features --example sieve
	cargo run --all-features --example tour
