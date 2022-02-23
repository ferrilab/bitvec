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
cross: rustup_targets
	@# xargs -n1 -I'{}' env ENABLE_CROSS=1 TARGET='{}' ci/script.sh        --all-features                         < ci/target_test_all.txt
	xargs -n1 -I'{}' env ENABLE_CROSS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,std   < ci/target_test_no_serde.txt

	xargs -n1 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh        --all-features                         < ci/target_check_all.txt
	xargs -n1 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,std   < ci/target_check_no_serde.txt
	xargs -n1 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,alloc < ci/target_check_no_std.txt

# Runs the cross-compile battery in some parallelism.
#
# This is only useful if don’t expect the tests to fail, because
cross_par: rustup_targets
	@# You will need to run this the first time you start cross-compiling
	@# on a given machine.
	@# TRAVIS_OS_NAME=linux ci/install_rust.sh

	xargs -n1 -P4 -I'{}' env ENABLE_CROSS=1 TARGET='{}' ci/script.sh        --all-features                         < ci/target_test_all.txt
	xargs -n1 -P4 -I'{}' env ENABLE_CROSS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,std   < ci/target_test_no_serde.txt

	xargs -n1 -P4 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh        --all-features                         < ci/target_check_all.txt
	xargs -n1 -P4 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,std   < ci/target_check_no_serde.txt
	xargs -n1 -P4 -I'{}' env DISABLE_TESTS=1 TARGET='{}' ci/script.sh --no-default-features --features atomic,alloc < ci/target_check_no_std.txt

# Runs the development routines.
dev: check doc test
	echo miri cover | xargs -n1 -P2 just
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
miri *ARGS: miri_install
	cargo +nightly miri test --features atomic,serde,std -q --lib --tests {{ARGS}}

# Installs Miri and ensures that it is able to run uninteractively.
miri_install:
	rustup toolchain add nightly --component miri
	cargo +nightly miri setup

# Packages the crate in preparation for publishing on crates.io
package: build
	cargo package --allow-dirty

# Publishes the crate to crates.io
publish: checkout
	cargo publish

# Installs *every* target.
rustup_targets:
	xargs -P1 rustup target add < ci/targets.txt 2>&1 | grep -v "up to date" || true

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
