#!/bin/bash

set -ex

if [[ ! -z $COVERAGE ]]; then
    cargo install cargo-tarpaulin -f
fi
