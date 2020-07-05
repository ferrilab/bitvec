#!/usr/bin/env bash

set -ex

if [[ ! -z $COVERAGE ]]; then
    cargo +nightly install cargo-tarpaulin -f
fi
