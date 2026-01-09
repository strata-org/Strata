#!/bin/sh
# Script to run basic test of strata generator.
set -e

if [ "$#" -ne 1 ] ; then
  echo "run_test.sh <input python file>"
  exit 1
fi

if [ ! -f "dialects/Python.dialect.st.ion" ] ; then
  echo "Cannot find Python dialect"
  exit 1
fi

test_dir="$PWD/test_results"

strata=../../.lake/build/bin/strata

# Dialect files:
# dialects/Python.dialect.st.ion

input_path=$1
input_dir=`dirname "$input_path"`
filename=`basename "$input_path"`
mkdir -p $test_dir/$input_dir

python=${PYTHON:-python3}
$python -m strata.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" $input_path "$test_dir/$input_dir/$filename.st.ion"

$strata toIon --include "dialects" "$test_dir/$input_dir/$filename.st.ion" "$test_dir/$input_dir/$filename.st.ion2"

# Check whether 'strata toIon' worked ok
$strata diff --include "dialects" "$test_dir/$input_dir/$filename.st.ion" "$test_dir/$input_dir/$filename.st.ion2"