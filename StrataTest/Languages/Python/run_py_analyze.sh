#!/bin/bash

# Usage: ./run_py_analyze.sh [--print-only]
# Default: Compare outputs with expected files
# --print-only: Just run tests and print results without comparing

print_only=false
if [ "$1" = "--print-only" ]; then
    print_only=true
fi

failed=0
mode="${1:-core}"

if [ "$mode" = "laurel" ]; then
    command="pyAnalyzeLaurel"
    expected_dir="expected_laurel"
    skip_tests="test_datetime test_class_decl test_strings"
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

        if [ -f "$expected_file" ] || [ "$print_only" = true ]; then
            (cd ../../../Tools/Python && python -m strata.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

            output=$(cd ../../.. && lake exe strata pyAnalyzeLaurel "StrataTest/Languages/Python/${ion_file}" 0)

            if [ "$print_only" = true ]; then
                echo "=== $base_name ==="
                echo "$output"
                echo ""
            else
                if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                    echo "ERROR: Analysis output for $base_name does not match expected result"
                    echo "$output" | diff "$expected_file" -
                    failed=1
                else
                    echo "Test passed: " $base_name
                fi
            fi
        fi
    fi
done

exit $failed
