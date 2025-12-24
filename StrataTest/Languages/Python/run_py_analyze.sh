#!/bin/bash

failed=0

for test_file in tests/test_*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)
        ion_file="tests/${base_name}.python.st.ion"
        expected_file="expected/${base_name}.expected"

        if [ -f "$expected_file" ]; then
            (cd ../../../Tools/Python && python -m strata.gen py_to_strata "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

            output=$(cd ../../.. && lake exe strata pyAnalyze --include Tools/Python/test_results/dialects "StrataTest/Languages/Python/${ion_file}" 0)

            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
                failed=1
            fi
        fi
    fi
done

exit $failed
