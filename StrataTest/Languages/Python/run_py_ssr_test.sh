#!/bin/bash
# ------------------------------------------------------------------------------
# run_py_ssr_test.sh — Validate the Split-Solve-Aggregate Results workflow for Python.
#
# For each test_*.py file with an expected output, this script:
#   1. Runs the SSR workflow via Scripts/ssr_py.sh (generate → solve → aggregate results)
#   2. Compares the DETAIL/RESULT summary lines against the expected output
#      from direct verification (the expected_laurel/*.expected files)
#
# Usage:
#   ./run_py_ssr_test.sh [--filter <pattern>] [--solver <cmd>]
# ------------------------------------------------------------------------------

set -euo pipefail

filter=""
solver_cmd="cvc5 --produce-models"

while [ $# -gt 0 ]; do
  case "$1" in
    --filter) filter="$2"; shift 2 ;;
    --solver) solver_cmd="$2"; shift 2 ;;
    -h|--help)
      sed -n '3,12p' "$0" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "Unknown argument: $1"; exit 1 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
SSR_SCRIPT="$REPO_ROOT/Scripts/ssr_py.sh"
STRATA="$REPO_ROOT/.lake/build/bin/strata"
DIALECT="$REPO_ROOT/dialects/Python.dialect.st.ion"
# Fall back to the dialect file shipped with the Python tools.
if [ ! -f "$DIALECT" ]; then
  DIALECT="$REPO_ROOT/Tools/Python/dialects/Python.dialect.st.ion"
fi
EXPECTED_DIR="$SCRIPT_DIR/expected_laurel"

# Verify prerequisites.
command -v python3 >/dev/null 2>&1 || { echo "error: python3 not found"; exit 1; }
command -v "${solver_cmd%% *}" >/dev/null 2>&1 || { echo "error: solver '${solver_cmd%% *}' not found"; exit 1; }
[ -x "$STRATA" ] || { echo "error: strata not built. Run 'lake build strata:exe' first."; exit 1; }
[ -f "$SSR_SCRIPT" ] || { echo "error: ssr_py.sh not found at $SSR_SCRIPT"; exit 1; }

passed=0
failed=0
skipped=0

# Extract DETAIL and RESULT lines from output — these summarize the outcome.
extract_summary() {
  grep -E '^(DETAIL|RESULT):' "$1" 2>/dev/null || true
}

for test_file in "$SCRIPT_DIR"/tests/test_*.py; do
  [ -f "$test_file" ] || continue
  base_name=$(basename "$test_file" .py)

  # Apply filter.
  if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
    continue
  fi

  expected_file="$EXPECTED_DIR/${base_name}.expected"
  [ -f "$expected_file" ] || { skipped=$((skipped + 1)); continue; }

  # Skip tests that use non-default check modes (bugFinding etc.) — the
  # aggregate-results command would need matching --check-mode flags.
  extra_args=$(grep '^# strata-args:' "$test_file" | sed 's/^# strata-args://' | head -1)
  if echo "$extra_args" | grep -q "check-mode"; then
    skipped=$((skipped + 1))
    continue
  fi

  # Create a temp directory for this test's SSR artifacts.
  ssr_dir=$(mktemp -d)

  # Run the SSR workflow via ssr_py.sh.
  ssr_output=$("$SSR_SCRIPT" \
    --output-dir "$ssr_dir" \
    --solver "$solver_cmd" \
    --strata "$STRATA" \
    --dialect "$DIALECT" \
    "$test_file" 2>&1) || ssr_rc=$?
  ssr_rc=${ssr_rc:-0}

  if [ "$ssr_rc" -eq 1 ]; then
    # Exit code 1 = user error (e.g., parse failure, missing prerequisites).
    # Check if the expected file documents this as an expected error.
    if grep -qE '^(DETAIL|RESULT):.*\b(error|Error)\b' "$expected_file"; then
      echo "PASS (expected error): $base_name"
      passed=$((passed + 1))
    else
      echo "FAIL (ssr user error): $base_name"
      echo "  Output: $(echo "$ssr_output" | tail -3)"
      failed=$((failed + 1))
    fi
    rm -rf "$ssr_dir"
    continue
  elif [ "$ssr_rc" -eq 3 ]; then
    # Exit code 3 = internal error (generate/solve/aggregate crashed).
    echo "FAIL (ssr internal error): $base_name"
    echo "  Output: $(echo "$ssr_output" | tail -5)"
    failed=$((failed + 1))
    rm -rf "$ssr_dir"
    continue
  fi

  # Compare summary lines.
  expected_summary=$(extract_summary "$expected_file")
  actual_summary=$(echo "$ssr_output" | grep -E '^(DETAIL|RESULT):' || true)

  if [ "$expected_summary" = "$actual_summary" ]; then
    echo "PASS: $base_name"
    passed=$((passed + 1))
  else
    echo "FAIL: $base_name"
    echo "  Expected: $expected_summary"
    echo "  Got:      $actual_summary"
    failed=$((failed + 1))
  fi

  rm -rf "$ssr_dir"
done

echo ""
echo "SSR test summary: $passed passed, $failed failed, $skipped skipped"
[ "$failed" -eq 0 ]
