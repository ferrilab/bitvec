#!/usr/bin/env bash

# Uncomment the following line for coveralls.io
cargo tarpaulin --all-features --ciserver travis-ci --coveralls $TRAVIS_JOB_ID

# Uncomment the following two lines create and upload a report for codecov.io
cargo tarpaulin --all-features --out Xml
bash <(curl -s https://codecov.io/bash)
echo "Uploaded code coverage"
