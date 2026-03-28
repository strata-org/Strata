#!/bin/bash

# Usage: ./run_py_analyze.sh [laurel] [--update] [--filter <pattern>] [--vc-directory <dir>]
# Runs pyAnalyzeLaurel on all test_*.py files and compares output to expected.
# With --update, overwrite existing expected files with actual output
# With --filter <pattern>, only run tests whose name contains <pattern>
# With --vc-directory <dir>, store VCs in SMT-Lib format in <dir>
# Note: pyAnalyze (non-Laurel) is deprecated; laurel mode is the default.

failed=0
update=0
mode="laurel"
filter=""
vc_directory=""

while [ $# -gt 0 ]; do
    case "$1" in
        --update) update=1 ;;
        --filter) filter="$2"; shift ;;
        --vc-directory) vc_directory="$2"; shift ;;
        *) mode="$1" ;;
    esac
    shift
done

if [ "$mode" = "laurel" ]; then
    command="pyAnalyzeLaurel"
    expected_dir="expected_laurel"
    skip_tests=""
else
    command="pyAnalyze"
    expected_dir="expected_non_laurel"
    skip_tests=""
fi

(cd ../../.. && lake exe strata --help > /dev/null)

for test_file in tests/test_*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)

        # Skip tests if specified
        skip=0
        for skip_test in $skip_tests; do
            if [ "$base_name" = "$skip_test" ]; then
                echo "Skipping: $base_name"
                skip=1
                break
            fi
        done
        [ $skip -eq 1 ] && continue

        # Apply name filter if specified
        if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
            continue
        fi

        ion_file="tests/${base_name}.python.st.ion"
        expected_file="${expected_dir}/${base_name}.expected"

        if [ -f "$expected_file" ]; then
            (cd ../../../Tools/Python && python3 -m strata.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

            # Check for per-file strata arguments (e.g. # strata-args: --check-mode bugFinding)
            extra_args=$(grep '^# strata-args:' "$test_file" | sed 's/^# strata-args://' | head -1)
            vc_flag=""
            [ -n "$vc_directory" ] && vc_flag="--vc-directory $vc_directory"
            output=$(cd ../../.. && ./.lake/build/bin/strata $command $extra_args $vc_flag "StrataTest/Languages/Python/${ion_file}")

            if [ $update -eq 1 ]; then
                echo "$output" > "$expected_file"
                echo "Updated: $expected_file"
            elif ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
                failed=1
            else
                echo "Test passed: " $base_name
            fi
        fi
    fi
done

exit $failed
