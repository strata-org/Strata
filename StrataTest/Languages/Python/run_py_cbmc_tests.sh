#!/bin/bash
#
# Run all Python CBMC pipeline tests and check against expected outcomes.
# Usage: ./run_py_cbmc_tests.sh
#
# Environment variables:
#   CBMC   - path to cbmc binary (default: cbmc)

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
EXPECTED="$TESTS_DIR/cbmc_expected.txt"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
DIALECT="$PROJECT_ROOT/Tools/Python/dialects/Python.dialect.st.ion"
PYTHON=${PYTHON:-python3}

# Generate .py.ion files from .py sources (they are not committed)
echo "Generating .py.ion files from .py sources..."
for py_file in "$TESTS_DIR"/*.py; do
  [ -f "$py_file" ] || continue
  ion_file="${py_file}.ion"
  if ! (cd "$PROJECT_ROOT/Tools/Python" && \
        "$PYTHON" -m strata.gen py_to_strata --dialect "$DIALECT" "$py_file" "$ion_file") 2>/dev/null; then
    echo "  WARN: failed to generate $(basename "$ion_file")"
  fi
done

passed=0
failed=0
skipped=0
errors=0

for ion_file in "$TESTS_DIR"/*.py.ion; do
  [ -f "$ion_file" ] || continue
  bn=$(basename "$ion_file")

  # Look up expected outcome
  expected=$(awk -v f="$bn" '$1 == f {print $2}' "$EXPECTED")
  if [ -z "$expected" ]; then
    echo "WARN: $bn not in cbmc_expected.txt, skipping"
    skipped=$((skipped + 1))
    continue
  fi

  if [ "$expected" = "SKIP" ]; then
    echo "SKIP: $bn"
    skipped=$((skipped + 1))
    continue
  fi

  # Run the pipeline
  output=$("$SCRIPT_DIR/py_ion_to_cbmc.sh" "$ion_file" 2>&1)

  if echo "$output" | grep -q "VERIFICATION SUCCESSFUL"; then
    result="PASS"
  elif echo "$output" | grep -q "VERIFICATION FAILED"; then
    result="FAIL"
  else
    result="ERROR"
  fi

  if [ "$result" = "$expected" ]; then
    echo "OK:   $bn ($result)"
    passed=$((passed + 1))
  elif [ "$result" = "ERROR" ]; then
    echo "ERR:  $bn (pipeline error, expected $expected)"
    echo "$output" | tail -3
    errors=$((errors + 1))
  else
    echo "FAIL: $bn (got $result, expected $expected)"
    errors=$((errors + 1))
  fi
done

echo ""
echo "Results: $passed passed, $skipped skipped, $errors errors"

[ "$errors" -eq 0 ]
