#!/usr/bin/env bash

if [[ ! -z $COVERAGE ]]; then
    # Uncomment the following line for coveralls.io
    # cargo tarpaulin --ciserver travis-ci --coveralls $TRAVIS_JOB_ID

    # Uncomment the following two lines create and upload a report for codecov.io
    cargo tarpaulin --out Xml
    bash <(curl -s https://codecov.io/bash)
    echo "Uploaded code coverage"
fi
