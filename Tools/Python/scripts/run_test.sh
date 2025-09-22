#!/bin/sh
# Script to run basic test of strata generator.
set -e

if [ "$#" -ne 1 ] ; then
  echo "run_test.sh <input python file>"
  exit 1
fi

test_dir="$PWD/test_results"

strata=../../.lake/build/bin/strata

# Dialect files:
# $test_dir/dialects/Python.dialect.st.ion
# $test_dir/dialect_src/Python.dialect.st

input_path=$1
input_dir=`dirname "$input_path"`
filename=`basename "$input_path"`
mkdir -p $test_dir/$input_dir

python3 -m strata.gen parse $input_path "$test_dir/$input_dir/$filename.st.ion"
$strata print --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion" > "$test_dir/$input_dir/$filename.st"

# Check the validity of the two programs
$strata check --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion"
$strata check --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st"

# Check whether 'strata print' worked ok
$strata diff --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st" "$test_dir/$input_dir/$filename.st.ion"
