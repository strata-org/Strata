#!/bin/sh
# Script to run basic test of strata generator.
set -e

# Get the directory where this script is located
script_dir="$(cd "$(dirname "$0")" && pwd)"
# Change to the strata-python package root so dialects and imports work
strata_python_dir="$(cd "$script_dir/.." && pwd)"
cd "$strata_python_dir"

strata=../../../StrataCLI/.lake/build/bin/strata

if [ ! -f $strata ]; then
  echo "strata is not built: $strata"
  exit 1
fi

dialect_dir="dialects"

mkdir -p "$dialect_dir"

python3 -m strata_python.gen dialect "$dialect_dir"
$strata print "$dialect_dir/Python.dialect.st.ion" > "$dialect_dir/Python.dialect.st"

$strata check "$dialect_dir/Python.dialect.st.ion"
$strata check "$dialect_dir/Python.dialect.st"
