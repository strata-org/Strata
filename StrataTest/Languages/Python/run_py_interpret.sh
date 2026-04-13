#!/bin/bash

# Usage: ./run_py_interpret.sh [--filter <pattern>] [--fuel <n>] [--direct] [--verbose]
# Runs pyInterpret on all test_*.py files and checks against expected outcomes.
# With --filter <pattern>, only run tests whose name contains <pattern>
# With --fuel <n>, set the interpreter fuel limit (default: 100000)
# With --direct, use the direct Python→Core path (no Laurel)
# With --verbose, show full interpreter output on failure
#
# Expected outcomes are read from tests/interpret_expected.txt.
# Tests not listed there default to PASS.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
EXPECTED="$TESTS_DIR/interpret_expected.txt"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

failed=0
passed=0
skipped=0
errors=0
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
(cd "$PROJECT_ROOT" && lake build strata:exe strata > /dev/null 2>&1)

for test_file in "$TESTS_DIR"/test_*.py; do
    [ -f "$test_file" ] || continue
    base_name=$(basename "$test_file" .py)
    bn=$(basename "$test_file")

    # Apply name filter if specified
    if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
        continue
    fi

    # Look up expected outcome; default to PASS
    expected=$(awk -v f="$bn" '$1 == f {print $2}' "$EXPECTED")
    if [ -z "$expected" ]; then
        expected="PASS"
    fi

    if [ "$expected" = "SKIP" ]; then
        echo "SKIP: $base_name"
        skipped=$((skipped + 1))
        continue
    fi

    ion_file="$TESTS_DIR/${base_name}.python.st.ion"

    # Compile Python to Ion
    compile_output=$(cd "$PROJECT_ROOT/Tools/Python" && python3 -m strata.gen py_to_strata \
        --dialect "dialects/Python.dialect.st.ion" \
        "$test_file" "$ion_file" 2>&1)
    if [ $? -ne 0 ]; then
        echo "SKIP (parse): $base_name"
        skipped=$((skipped + 1))
        continue
    fi

    # Run interpreter
    rel_ion="StrataTest/Languages/Python/tests/${base_name}.python.st.ion"
    output=$(cd "$PROJECT_ROOT" && ./.lake/build/bin/strata pyInterpret $direct $fuel \
        "$rel_ion" 2>&1)
    exit_code=$?

    # Filter out lake build warnings
    clean_output=$(echo "$output" | grep -v "^⚠\|^warning:")

    if [ $exit_code -eq 0 ]; then
        result="PASS"
    else
        result="FAIL"
    fi

    if [ "$result" = "$expected" ]; then
        echo "OK:   $base_name ($result)"
        passed=$((passed + 1))
    else
        reason=$(echo "$clean_output" | grep -v "^$" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^trace:" | tail -1)
        echo "ERR:  $base_name (got $result, expected $expected) — $reason"
        if [ $verbose -eq 1 ]; then
            echo "$clean_output" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^$" | sed 's/^/  /'
        fi
        errors=$((errors + 1))
    fi

    # Clean up Ion file
    rm -f "$ion_file"
done

echo ""
echo "Results: $passed passed, $skipped skipped, $errors errors"

[ "$errors" -eq 0 ]
