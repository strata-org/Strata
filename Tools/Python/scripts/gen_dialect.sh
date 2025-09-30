#!/bin/sh
# Script to run basic test of strata generator.
set -e

test_dir="$PWD/test_results"

strata=../../.lake/build/bin/strata

if [ ! -f $strata ]; then
  echo "strata is not built: $strata"
  exit 1
fi

mkdir -p "$test_dir/dialects"

python3 -Xgil=0 -m strata.gen dialect PythonAST "$test_dir/dialects"
$strata print "$test_dir/dialects/PythonAST.dialect.st.ion" > "$test_dir/dialects/PythonAST.dialect.st"

$strata check "$test_dir/dialects/PythonAST.dialect.st.ion"
$strata check "$test_dir/dialects/PythonAST.dialect.st"

python3 -Xgil=0 -m strata.gen dialect PythonSSA "$test_dir/dialects"
$strata print "$test_dir/dialects/PythonSSA.dialect.st.ion" > "$test_dir/dialects/PythonSSA.dialect.st"

$strata check "$test_dir/dialects/PythonSSA.dialect.st.ion"
$strata check "$test_dir/dialects/PythonSSA.dialect.st"
