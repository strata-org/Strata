#!/bin/bash

for test_file in test_[0-9]*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)
        ion_file="${base_name}.python.st.ion"
        expected_file="expected/${base_name}.expected"

        (cd ../../../Tools/Python && python -m strata.gen py_to_strata "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

        output=$(cd ../../.. && lake exe strata pyAnalyze --include Tools/Python/test_results/dialects "StrataTest/Languages/Python/${ion_file}" 0)

        if [ -f "$expected_file" ]; then
            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
            fi
        else
            echo "ERROR: No expected file found for $base_name"
            exit 1
        fi
    fi
done
