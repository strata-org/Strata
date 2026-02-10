#!/bin/bash

failed=0

for test_file in *.st; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" ".st")
        expected_file="expected/${base_name}.expected"
        if [ -f "$expected_file" ]; then

            output=$(cd .. && lake exe StrataVerify "Examples/${test_file}")

            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
                failed=1
            fi
        fi	
    fi
done

exit $failed
