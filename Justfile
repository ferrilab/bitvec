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
	cargo build --all-features --example sieve
	cargo build --all-features --example tour

# Checks the library for syntax and HIR errors.
check:
	cargo clippy --no-default-features
	cargo clippy --no-default-features --features alloc
	cargo clippy --all-features

# Runs all of the recipes necessary for pre-publish.
checkout: format check build doc test package

# Continually runs the development routines.
ci:
	just loop dev

# Removes all build artifacts.
clean:
	cargo clean

# Produces coverage statistics for the (non-doc) test suite.
cover *ARGS: format check lint
	docker run --security-opt seccomp=unconfined -v "${PWD}:/volume" xd009642/tarpaulin:0.16.0 cargo-tarpaulin tarpaulin -- {{ARGS}}
	@tokei

# This runs the cross-compile battery on a development machine. It is not
# suitable for use in a CI environment. It requires the Rust projects
# <https://crates.io/crates/parallel> and
# <https://github.com/rust-embedded/cross>.
cross:
	@# You will need to run this the first time you start cross-compiling on a
	@# machine.
	@# TRAVIS_OS_NAME=linux ci/install_rust.sh

	@# Run on a Linux host, and execute the test suite
	parallel -v 'env ENABLE_CROSS=1 TARGET={} ci/script.sh' :::: ci/target_test.txt

	@# Run on a Linx host, but do not execute the test suite.
	parallel -v 'env ENABLE_CROSS=1 TARGET={} DISABLE_TESTS=1 ci/script.sh' :::: ci/target_notest.txt

	@# Cross-compile only, without attempting to emulate.
	@# You will need to install rustup targets in order to check for them:
	@# parallel -v 'rustup target add {}' :::: ci/target_local.txt
	parallel -v 'cargo check --no-default-features --target {}' :::: ci/target_local.txt

cross_seq:
	xargs -n1 -I'{}' env ENABLE_CROSS=1 TARGET='{}' ci/script.sh < ci/target_test.txt
	xargs -n1 -I'{}' env ENABLE_CROSS=1 TARGET='{}' DISABLE_TESTS=1 ci/script.sh < ci/target_notest.txt
	xargs -n1 -I'{}' cargo check --no-default-features --target '{}' < ci/target_local.txt

# Runs the development routines.
dev: format doc test cover
	@echo "Complete at $(date)"

# Builds the crate documentation.
doc *ARGS:
	cargo +nightly doc --all-features {{ARGS}}

# Runs the formatter on all Rust files.
format:
	cargo +nightly fmt -- --config-path rustfmt-nightly.toml

# Continually runs some recipe from this file.
loop +ACTIONS:
	watchexec -w src -- "just {{ACTIONS}}"

# Looks for undefined behavior in the (non-doc) test suite.
miri *ARGS:
	cargo +nightly miri test --all-features -q --lib --tests {{ARGS}}

# Packages the crate in preparation for publishing on crates.io
package:
	cargo package --allow-dirty

# Publishes the crate to crates.io
publish: checkout
	cargo publish

# Runs the test suites.
test *ARGS: check
	cargo test --no-default-features -q --lib --tests {{ARGS}}
	cargo test --no-default-features --features alloc -q --lib --tests {{ARGS}}
	cargo test --all-features -q --lib --tests {{ARGS}}
	cargo test --all-features -q --doc {{ARGS}}
	cargo run --all-features --example aliasing &>/dev/null
	cargo run --all-features --example ipv4 &>/dev/null
	cargo run --all-features --example sieve &>/dev/null
	cargo run --all-features --example tour &>/dev/null
	just miri
