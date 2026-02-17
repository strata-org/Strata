#!/bin/bash

failed=0

for test_file in *.st; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" ".st")
        expected_file="expected/${base_name}.expected"
        if [ -f "$expected_file" ]; then

            output=$(cd .. && lake exe StrataVerify --vc-directory vcs "Examples/${test_file}")

            if ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match expected result"
                echo "$output" | diff "$expected_file" -
                failed=1
            fi
            if ls ../vcs/*.smt2 2> /dev/null > /dev/null ; then
                if ! grep -q "set-info" ../vcs/*.smt2 ; then
                  echo "ERROR: No provenance information in VCs"
                  failed=1
                fi
            fi
            rm -rf ../vcs
        fi
    fi
done

exit $failed
