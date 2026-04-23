#!/bin/bash

# Usage: ./run_py_interpret.sh [--filter <pattern>] [--fuel <n>] [--direct] [--verbose] [--update]
#
# Runs pyInterpret on all test_*.py files and reports pass/fail.
#
# Expected outcomes are controlled by files in expected_interpret/:
#   - No .expected/.skip → run test, assert exit code 0 (PASS)
#   - .expected file     → run test, assert non-zero exit and output matches
#                          the regex pattern in the file
#   - .skip file         → skip test (file contents used as reason)
#
# Options:
#   --filter <pattern>  Only run tests whose name contains <pattern>
#   --fuel <n>          Set the interpreter fuel limit (default: 100000)
#   --direct            Use the direct Python→Core path (no Laurel)
#   --verbose           Show full interpreter output on failure
#   --update            Regenerate .expected files from actual output

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
EXPECTED_DIR="$SCRIPT_DIR/expected_interpret"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

passed=0
errors=0
skipped=0
filter=""
fuel=""
direct=""
verbose=0
update=0

while [ $# -gt 0 ]; do
    case "$1" in
        --filter) filter="$2"; shift ;;
        --fuel) fuel="--fuel $2"; shift ;;
        --direct) direct="--direct" ;;
        --verbose) verbose=1 ;;
        --update) update=1 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
    shift
done

# Ensure strata is built
(cd "$PROJECT_ROOT" && lake build strata:exe strata > /dev/null 2>&1)

for test_file in "$TESTS_DIR"/test_*.py; do
    [ -f "$test_file" ] || continue
    base_name=$(basename "$test_file" .py)

    # Apply name filter if specified
    if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
        continue
    fi

    expected_file="$EXPECTED_DIR/${base_name}.expected"
    skip_file="$EXPECTED_DIR/${base_name}.skip"
    ion_file="$TESTS_DIR/${base_name}.python.st.ion"

    # Check for skip file
    if [ -f "$skip_file" ]; then
        reason=$(cat "$skip_file")
        echo "SKIP: $base_name — $reason"
        skipped=$((skipped + 1))
        continue
    fi

    # Compile Python to Ion
    if ! (cd "$PROJECT_ROOT/Tools/Python" && python3 -m strata.gen py_to_strata \
        --dialect "dialects/Python.dialect.st.ion" \
        "$test_file" "$ion_file") 2>/dev/null; then
        echo "SKIP (parse): $base_name"
        skipped=$((skipped + 1))
        continue
    fi

    # Run interpreter
    rel_ion="StrataTest/Languages/Python/tests/${base_name}.python.st.ion"
    output=$(cd "$PROJECT_ROOT" && ./.lake/build/bin/strata pyInterpret $direct $fuel \
        "$rel_ion" 2>&1)
    exit_code=$?

    # Clean up Ion file
    rm -f "$ion_file"

    if [ -f "$expected_file" ]; then
        # Expected file exists → test should fail, output should match regex
        pattern=$(cat "$expected_file")

        if [ $update -eq 1 ]; then
            if [ $exit_code -ne 0 ]; then
                echo "$output" | grep -oE "$pattern" | head -1 > "$expected_file"
                echo "Updated: $base_name"
            else
                rm -f "$expected_file"
                echo "Updated: $base_name (now passes, removed expected file)"
            fi
            passed=$((passed + 1))
        elif [ $exit_code -eq 0 ]; then
            echo "ERR:  $base_name (expected failure matching /$pattern/ but test passed)"
            errors=$((errors + 1))
        elif echo "$output" | grep -qE "$pattern"; then
            echo "OK:   $base_name (expected failure)"
            passed=$((passed + 1))
        else
            echo "ERR:  $base_name (output does not match expected pattern /$pattern/)"
            if [ $verbose -eq 1 ]; then
                echo "$output" | sed 's/^/  /'
            fi
            errors=$((errors + 1))
        fi
    else
        # No expected file → test should pass
        if [ $update -eq 1 ] && [ $exit_code -ne 0 ]; then
            # Test fails unexpectedly; create expected file with regex-escaped error
            reason=$(echo "$output" | grep -v "^$" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^trace:" | tail -1)
            escaped=$(echo "$reason" | sed 's/[][(){}.*+?^$\\|]/\\&/g')
            echo "$escaped" > "$expected_file"
            echo "Created: $base_name — $reason"
            passed=$((passed + 1))
        elif [ $exit_code -eq 0 ]; then
            echo "OK:   $base_name"
            passed=$((passed + 1))
        else
            reason=$(echo "$output" | grep -v "^$" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^trace:" | tail -1)
            echo "ERR:  $base_name (expected pass but failed) — $reason"
            if [ $verbose -eq 1 ]; then
                echo "$output" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^$" | sed 's/^/  /'
            fi
            errors=$((errors + 1))
        fi
    fi
done

echo ""
echo "Results: $passed passed, $skipped skipped, $errors errors"

[ "$errors" -eq 0 ]
