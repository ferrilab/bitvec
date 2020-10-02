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
	# You will need to run this the first time you start cross-compiling on a
	# machine.
	# TRAVIS_OS_NAME=linux ci/install_rust.sh

	# Run on a Linux host, and execute the test suite
	CI=1 TARGET=aarch64-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=arm-unknown-linux-gnueabi ci/script.sh
	CI=1 TARGET=armv7-unknown-linux-gnueabihf ci/script.sh
	CI=1 TARGET=i686-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=i686-unknown-linux-musl ci/script.sh
	CI=1 TARGET=mips-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=mips64-unknown-linux-gnuabi64 ci/script.sh
	CI=1 TARGET=mips64el-unknown-linux-gnuabi64 ci/script.sh
	CI=1 TARGET=mipsel-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=powerpc-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=powerpc64le-unknown-linux-gnu ci/script.sh
	CI=1 TARGET=x86_64-unknown-linux-musl ci/script.sh

	# Run on a Linx host, but do not execute the test suite.
	CI=1 TARGET=aarch64-linux-android DISABLE_TESTS=1 ci/script.sh
	CI=1 TARGET=arm-linux-androideabi DISABLE_TESTS=1 ci/script.sh
	CI=1 TARGET=armv7-linux-androideabi DISABLE_TESTS=1 ci/script.sh
	CI=1 TARGET=i686-linux-android DISABLE_TESTS=1 ci/script.sh
	CI=1 TARGET=s390x-unknown-linux-gnu DISABLE_TESTS=1 ci/script.sh
	CI=1 TARGET=x86_64-linux-android DISABLE_TESTS=1 ci/script.sh

# Runs the development routines.
dev: format lint doc test cover

# Builds the crate documentation.
doc:
	@cargo doc --all-features --document-private-items

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
test: check lint
	cargo test --no-default-features -q --lib --tests
	cargo test --all-features -q --lib --tests
	cargo test --all-features -q --doc
	@cargo run --all-features --example aliasing &>/dev/null
	@cargo run --all-features --example ipv4 &>/dev/null
	@cargo run --all-features --example sieve &>/dev/null
	@cargo run --all-features --example tour &>/dev/null
	cargo +nightly miri test
