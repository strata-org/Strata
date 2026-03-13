#!/bin/bash

# Usage: ./run_py_analyze.sh [laurel] [--update]
# Run without arguments for pyAnalyze, with "laurel" for pyAnalyzeLaurel
# With --update, overwrite existing expected files with actual output

failed=0
update=0
mode="core"

for arg in "$@"; do
    case "$arg" in
        --update) update=1 ;;
        *) mode="$arg" ;;
    esac
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

        ion_file="tests/${base_name}.python.st.ion"
        expected_file="${expected_dir}/${base_name}.expected"

        if [ -f "$expected_file" ]; then
            (cd ../../../Tools/Python && python3 -m strata.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

            output=$(cd ../../.. && ./.lake/build/bin/strata $command "StrataTest/Languages/Python/${ion_file}")

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
