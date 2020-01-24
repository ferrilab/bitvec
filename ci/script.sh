#!/bin/bash

set -ex

# Detect our build command if we are on travis or not (so we can test locally).
if [ -z $CI ] || [ ! -z $DISABLE_CROSS ]; then
    # Not on CI or explicitly disabled cross, use cargo
    CARGO=cargo
else
    # On CI, use cross.
    CARGO=cross
    CARGO_TARGET="--target $TARGET"
fi

$CARGO clean
$CARGO build $CARGO_TARGET --all-features
if [ -z $DISABLE_TESTS ]; then
    $CARGO test $CARGO_TARGET --all-features
fi
