#!/bin/sh
# Script to run basic test of strata generator.
set -e

strata=../../.lake/build/bin/strata

if [ ! -f $strata ]; then
  echo "strata is not built: $strata"
  exit 1
fi

dialect_dir="dialects"

mkdir -p "$dialect_dir"

python3 -m strata.gen dialect "$dialect_dir"
$strata print "$dialect_dir/Python.dialect.st.ion" > "$dialect_dir/Python.dialect.st"

$strata check "$dialect_dir/Python.dialect.st.ion"
$strata check "$dialect_dir/Python.dialect.st"
