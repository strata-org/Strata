#!/bin/bash

# Usage: ./run_py_analyze.sh [--update] [--filter <pattern>] [--vc-directory <dir>]
# Runs pyAnalyzeLaurel on all test_*.py files and compares output to expected.
# With --update, overwrite existing expected files with actual output
# With --filter <pattern>, only run tests whose name contains <pattern>
# With --vc-directory <dir>, store VCs in SMT-Lib format in <dir>

failed=0
update=0
filter=""
vc_directory=""

while [ $# -gt 0 ]; do
    case "$1" in
        --update) update=1 ;;
        --filter) filter="$2"; shift ;;
        --vc-directory) vc_directory="$2"; shift ;;
        laurel) ;; # accepted for backward compatibility
        *) echo "Unknown argument: $1"; exit 1 ;;
    esac
    shift
done

command="pyAnalyzeLaurel"
expected_dir="expected_laurel"

(cd ../../.. && lake exe strata --help > /dev/null)

for test_file in tests/test_*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)

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

            # Check user_errors.txt if a .user_errors.expected file exists
            user_errors_expected="${expected_dir}/${base_name}.user_errors.expected"
            user_errors_file="../../../user_errors.txt"
            if [ $update -eq 1 ] && [ -f "$user_errors_file" ]; then
                cp "$user_errors_file" "$user_errors_expected"
                echo "Updated: $user_errors_expected"
                rm -f "$user_errors_file"
            elif [ -f "$user_errors_expected" ]; then
                if [ ! -f "$user_errors_file" ]; then
                    echo "ERROR: user_errors.txt not generated for $base_name"
                    failed=1
                elif ! diff -q "$user_errors_expected" "$user_errors_file" > /dev/null; then
                    echo "ERROR: user_errors.txt content for $base_name does not match expected"
                    diff "$user_errors_expected" "$user_errors_file"
                    failed=1
                else
                    echo "Test passed:  ${base_name} (user_errors.txt)"
                fi
            fi
            rm -f "$user_errors_file"
        fi
    fi
done

exit $failed
