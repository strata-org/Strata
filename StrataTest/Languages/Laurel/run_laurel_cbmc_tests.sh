#!/bin/bash
#
# Run all Laurel CBMC pipeline tests and check against expected property outcomes.
# Usage: ./run_laurel_cbmc_tests.sh
#
# The expected file lists per-test CBMC properties with line numbers and
# expected status (SUCCESS/FAILURE). The runner verifies each property
# appears in CBMC output with the correct status.
#
# Environment variables:
#   CBMC   - path to cbmc binary (default: cbmc)

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
EXPECTED="$TESTS_DIR/cbmc_expected.txt"

passed=0
failed=0
skipped=0

get_expected_properties() {
  local target="$1"
  awk -v t="$target" '
    /^[^ #].*\.lr\.st/ { current = $1; next }
    current == t && /^[[:space:]]+\[/ { print }
  ' "$EXPECTED"
}

for lr_file in "$TESTS_DIR"/*.lr.st; do
  [ -f "$lr_file" ] || continue
  bn=$(basename "$lr_file")

  props=$(get_expected_properties "$bn")
  if [ -z "$props" ]; then
    echo "SKIP: $bn (not in cbmc_expected.txt)"
    skipped=$((skipped + 1))
    continue
  fi

  # Run the pipeline
  output=$("$SCRIPT_DIR/laurel_to_cbmc.sh" "$lr_file" 2>&1)
  if [ $? -ne 0 ] && ! echo "$output" | grep -q "VERIFICATION"; then
    echo "ERR:  $bn (pipeline error)"
    echo "$output" | tail -3
    failed=$((failed + 1))
    continue
  fi

  # Check each expected property
  test_ok=true
  while IFS= read -r prop; do
    prop=$(echo "$prop" | sed 's/^[[:space:]]*//')
    [ -z "$prop" ] && continue
    # Parse: [main.N] line L <desc>: <STATUS>
    # Extract property id + line as the match key, e.g. "[main.1] line 6"
    prop_key=$(echo "$prop" | sed 's/^\(\[main\.[0-9]*\] line [0-9]*\).*/\1/')
    expected_status=$(echo "$prop" | grep -o '\(SUCCESS\|FAILURE\)$')
    # Find matching line in CBMC output by property id + line number
    match=$(echo "$output" | grep -F "$prop_key")
    if [ -z "$match" ]; then
      echo "FAIL: $bn — property not found: $prop_key"
      test_ok=false
    else
      actual_status=$(echo "$match" | grep -o '\(SUCCESS\|FAILURE\)$')
      if [ "$actual_status" != "$expected_status" ]; then
        echo "FAIL: $bn — $prop_key: got $actual_status, expected $expected_status"
        test_ok=false
      fi
    fi
  done <<< "$props"

  if $test_ok; then
    echo "OK:   $bn"
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
  fi
done

echo ""
echo "Results: $passed passed, $skipped skipped, $failed failed"

[ "$failed" -eq 0 ]
