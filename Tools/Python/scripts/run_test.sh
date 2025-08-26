#!/bin/sh
# Script to run basic test of strata generator.
set -e

test_dir="$PWD/test_results"

mkdir -p "$test_dir/dialects"
python -m strata.gen dialect "$test_dir/dialects"
../../.lake/build/bin/strata check "$test_dir/dialects/Python.dialect.st.ion"


python -m strata.gen parse strata/base.py "$test_dir/base.python.st.ion"
../../.lake/build/bin/strata check --include "$test_dir/dialects" "$test_dir/base.python.st.ion"
