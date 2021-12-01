########################################################################
#                               Justfile                               #
#                                                                      #
# Set of routines to execute for project development and management.   #
# Written against `just 0.10.0`.                                       #
########################################################################

default:
	just --list

# Runs the benchmark suite.
bench *ARGS: check
	cargo +nightly bench {{ARGS}}

# Builds the project.
build: check
	cargo build --no-default-features --lib
	cargo build --no-default-features --lib --features alloc
	cargo build        --all-features --lib
	cargo build        --all-features --examples

# Checks the project for syntax and HIR errors.
check:
	cargo clippy --no-default-features
	cargo clippy --no-default-features --features alloc
	cargo clippy        --all-features

# Runs all of the recipes necessary for pre-publish.
checkout: format check build doc test package

# Continually runs the development routines.
ci:
	just loop dev

# Removes all build artifacts.
clean:
	cargo clean

# Produces coverage reports for the test suite.
cover *ARGS: test
	cargo +nightly tarpaulin --all-features -- {{ARGS}}
	@# docker run --security-opt seccomp=unconfined -v "${PWD}:/volume" xd009642/tarpaulin:0.18.0 cargo-tarpaulin tarpaulin -- {{ARGS}}
	@tokei

# Runs the cross-compile battery test.
#
# This is suitable for a development machine **only**, and should not run in CI.
# The `.travis.yml` file controls CI usage.
#
# It requires <https://crates.io/crates/parallel> and
# <https://github.com/rust-embedded/cross>.
cross:
	@# You will need to run this the first time you start cross-compiling
	@# on a given machine.
	@# TRAVIS_OS_NAME=linux ci/install_rust.sh

	@# Run on a Linux host, and execute the test suite.
	parallel -v 'env ENABLE_CROSS=1 TARGET={} ci/script.sh' :::: ci/target_test.txt

	@# Run on a Linux host, but do not execute the test suite.
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
dev: check doc test
	parallel ::: "just miri" "just cover"
	@echo "Complete at $(date)"

# Builds the crate documentation and user guide.
doc:
	cargo doc --all-features --document-private-items
	mdbook build

# Runs the formatter.
format:
	cargo +nightly fmt

# Continually runs some recipe from this file.
loop +ACTIONS:
	watchexec -i target -- "just {{ACTIONS}}"

# Looks for undefined behavior in the (non-doc) test suite.
miri *ARGS:
	cargo +nightly miri test --features atomic,serde,std -q --lib --tests {{ARGS}}

# Packages the crate in preparation for publishing on crates.io
package: build
	cargo package --allow-dirty

# Publishes the crate to crates.io
publish: checkout
	cargo publish

# Spawns an HTTP file server to easily view compiled artifacts.
#
# The API documentation, user manual, and code coverage reports all produce HTML
# artifacts inside `target/`.
serve:
	miniserve . -p 7878 -Drzq

# Run the test suite.
#
# If arguments are provided, they select both `#[test]` functions and doctests.
test *ARGS: check
	just test_lib {{ARGS}}
	just test_doc
	just test_examples

# Runs the library and integration tests.
test_lib *ARGS:
	cargo test --no-default-features                  -q --lib --tests {{ARGS}}
	cargo test --no-default-features --features alloc -q --lib --tests {{ARGS}}
	cargo test        --all-features                  -q --lib --tests {{ARGS}}

# Runs the doctests.
test_doc *ARGS:
	cargo test        --all-features                  -q --doc         {{ARGS}}

# Runs the example programs (suppressing their output)
test_examples:
	echo aliasing ipv4 sieve tour \
	| xargs -n1 cargo run --all-features --example
