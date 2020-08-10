#!/usr/bin/env bash

set -ex

if [[ ! -z $COVERAGE ]]; then
  bash <(curl https://raw.githubusercontent.com/xd009642/tarpaulin/master/travis-install.sh)
fi
