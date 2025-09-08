#!/bin/sh
# Script to run basic test of strata generator.
set -e

test_dir="$PWD/test_results"

strata=../../.lake/build/bin/strata

mkdir -p "$test_dir/dialects"
mkdir -p "$test_dir/dialect_src"

python -m strata.gen dialect "$test_dir/dialects"
$strata print "$test_dir/dialects/Python.dialect.st.ion" > "$test_dir/dialect_src/Python.dialect.st"

$strata check "$test_dir/dialects/Python.dialect.st.ion"
$strata check "$test_dir/dialect_src/Python.dialect.st"


python -m strata.gen parse strata/base.py "$test_dir/base.python.st.ion"

$strata print --include "$test_dir/dialects" "$test_dir/base.python.st.ion" > "$test_dir/base.python.st"

$strata check --include "$test_dir/dialects" "$test_dir/base.python.st.ion"
$strata check --include "$test_dir/dialects" "$test_dir/base.python.st"
