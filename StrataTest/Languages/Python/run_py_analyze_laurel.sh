#!/bin/bash

failed=0

# Initialize conda
eval "$(conda shell.bash hook)"
conda activate strata

(cd ../../.. && lake exe strata --help > /dev/null)

for test_file in tests/test_*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)
        
        # Skip test_datetime and test_class_decl
        if [ "$base_name" = "test_datetime" ] || [ "$base_name" = "test_class_decl" ]; then
            echo "Skipping: $base_name"
            continue
        fi
        
        ion_file="tests/${base_name}.python.st.ion"
        expected_file="expected/${base_name}.expected"

        if [ -f "$expected_file" ]; then
            (cd ../../../Tools/Python && python -m strata.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataTest/Languages/Python/$test_file" "../../StrataTest/Languages/Python/$ion_file")

            output=$(cd ../../.. && ./.lake/build/bin/strata pyAnalyzeLaurel "StrataTest/Languages/Python/${ion_file}" 0)

            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
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
