################################################################################
#                                   Justfile                                   #
#                                                                              #
# Set of routines to execute for development work. As of 2019-05-01, `just`    #
# does not work on Windows.                                                    #
################################################################################

# Runs the benchmark suite
bench *ARGS:
	cargo +nightly bench {{ARGS}}

# Builds the library.
build:
	cargo build --no-default-features
	cargo build --no-default-features --features alloc
	cargo build --all-features
	@cargo build --all-features --example sieve
	@cargo build --all-features --example tour

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

cover: format check lint
	@cargo +nightly tarpaulin --all-features -o Lcov -l --output-dir target/tarpaulin --lib --tests --ignore-tests --ignore-panics &>/dev/null &
	cargo +nightly tarpaulin --all-features -o Html -l --output-dir target/tarpaulin --lib --tests --ignore-tests --ignore-panics
	@tokei

cross:
	@# You will need to run this the first time you start cross-compiling on a
	@# machine.
	@# TRAVIS_OS_NAME=linux ci/install_rust.sh

	@# Run on a Linux host, and execute the test suite
	parallel -v 'env ENABLE_CROSS=1 TARGET={} ci/script.sh' :::: ci/target_test.txt

	@# Run on a Linx host, but do not execute the test suite.
	parallel -v 'env ENABLE_CROSS=1 TARGET={} DISABLE_TESTS=1 ci/script.sh' :::: ci/target_notest.txt

	@# Cross-compile only, without attempting to emulate.
	parallel -v 'rustup target add {} ; cargo check --no-default-features --target {}' :::: ci/target_local.txt

# Runs the development routines.
dev: format lint doc test cover

# Builds the crate documentation.
doc:
	@cargo +nightly doc --all-features --document-private-items

# Runs the formatter on all Rust files.
format:
	@cargo +nightly fmt -- --config-path rustfmt-nightly.toml

# Runs the linter.
lint: check
	cargo clippy --no-default-features
	cargo clippy --no-default-features --features alloc
	cargo clippy --all-features

# Continually runs some recipe from this file.
loop action:
	watchexec -w src -- "just {{action}}"

miri:
	cargo +nightly miri test

# Packages the crate in preparation for publishing on crates.io
package:
	cargo package --allow-dirty

# Publishes the crate to crates.io
publish: checkout
	cargo publish

# Runs the test suites.
test *ARGS: check lint
	cargo test --no-default-features -q --lib --tests {{ARGS}}
	cargo test --all-features -q --lib --tests {{ARGS}}
	cargo test --all-features -q --doc {{ARGS}}
	@cargo run --all-features --example aliasing &>/dev/null
	@cargo run --all-features --example ipv4 &>/dev/null
	@cargo run --all-features --example sieve &>/dev/null
	@cargo run --all-features --example tour &>/dev/null
	cargo +nightly miri test {{ARGS}}
