#!/bin/bash

# Usage: ./run_py_interpret.sh [--filter <pattern>] [--fuel <n>] [--direct] [--verbose]
# Runs pyInterpret on all test_*.py files and reports pass/fail/skip.
# With --filter <pattern>, only run tests whose name contains <pattern>
# With --fuel <n>, set the interpreter fuel limit (default: 100000)
# With --direct, use the direct Python→Core path (no Laurel)
# With --verbose, show full interpreter output on failure

failed=0
passed=0
skipped=0
filter=""
fuel=""
direct=""
verbose=0

while [ $# -gt 0 ]; do
    case "$1" in
        --filter) filter="$2"; shift ;;
        --fuel) fuel="--fuel $2"; shift ;;
        --direct) direct="--direct" ;;
        --verbose) verbose=1 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
    shift
done

# Ensure strata is built
(cd ../../.. && lake build strata:exe strata > /dev/null 2>&1)

for test_file in tests/test_*.py; do
    [ -f "$test_file" ] || continue
    base_name=$(basename "$test_file" .py)

    # Apply name filter if specified
    if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
        continue
    fi

    ion_file="tests/${base_name}.python.st.ion"

    # Compile Python to Ion
    compile_output=$(cd ../../../Tools/Python && python3 -m strata.gen py_to_strata \
        --dialect "dialects/Python.dialect.st.ion" \
        "../../StrataTest/Languages/Python/$test_file" \
        "../../StrataTest/Languages/Python/$ion_file" 2>&1)
    if [ $? -ne 0 ]; then
        echo "SKIP (parse): $base_name"
        skipped=$((skipped + 1))
        continue
    fi

    # Run interpreter
    output=$(cd ../../.. && ./.lake/build/bin/strata pyInterpret $direct $fuel \
        "StrataTest/Languages/Python/${ion_file}" 2>&1)
    exit_code=$?

    # Filter out lake build warnings
    clean_output=$(echo "$output" | grep -v "^⚠\|^warning:")

    if [ $exit_code -eq 0 ]; then
        echo "PASS: $base_name"
        passed=$((passed + 1))
    else
        # Show a concise failure reason
        reason=$(echo "$clean_output" | grep -v "^$" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^trace:" | tail -1)
        echo "FAIL: $base_name — $reason"
        if [ $verbose -eq 1 ]; then
            echo "$clean_output" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^$" | sed 's/^/  /'
        fi
        failed=$((failed + 1))
    fi

    # Clean up Ion file
    rm -f "$ion_file"
done

echo ""
echo "Results: $passed passed, $failed failed, $skipped skipped"
exit $failed
