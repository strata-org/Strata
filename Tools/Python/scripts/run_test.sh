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

python3 -m strata.gen py_to_strata $input_path "$test_dir/$input_dir/$filename.st.ion"

$strata toIon --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion" "$test_dir/$input_dir/$filename.st.ion2"

# Check whether 'strata toIon' worked ok
$strata diff --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion" "$test_dir/$input_dir/$filename.st.ion2"

#N.B. We plan to eventually check round trip for the plaintext format, but it
# is currently not preserved (see https://github.com/strata-org/Strata/issues/132).
# Check the validity of the two programs
#$strata print --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion" > "$test_dir/$input_dir/$filename.st"
#$strata diff --include "$test_dir/dialects" "$test_dir/$input_dir/$filename.st.ion" "$test_dir/$input_dir/$filename.st"
