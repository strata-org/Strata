#!/bin/bash
# ------------------------------------------------------------------------------
# run_py_ssr_test.sh — Validate the Split-Solve-Reconcile workflow for Python.
#
# For each test_*.py file with an expected output, this script:
#   1. Runs `strata pyAnalyzeLaurel --no-solve` to generate manifest + .smt2
#   2. Solves each .smt2 with cvc5
#   3. Runs `strata reconcile` to produce the final report
#   4. Compares the DETAIL/RESULT summary lines against the expected output
#      from direct verification (the expected_laurel/*.expected files)
#
# Usage:
#   ./run_py_ssr_test.sh [--filter <pattern>] [--solver <cmd>]
# ------------------------------------------------------------------------------

set -u

filter=""
solver_cmd="cvc5 --produce-models"

while [ $# -gt 0 ]; do
  case "$1" in
    --filter) filter="$2"; shift 2 ;;
    --solver) solver_cmd="$2"; shift 2 ;;
    -h|--help)
      sed -n '3,14p' "$0" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "Unknown argument: $1"; exit 1 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
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
  # reconcile command would need matching --check-mode flags.
  extra_args=$(grep '^# strata-args:' "$test_file" | sed 's/^# strata-args://' | head -1)
  if echo "$extra_args" | grep -q "check-mode"; then
    skipped=$((skipped + 1))
    continue
  fi

  # Create a temp directory for this test's SSR artifacts.
  ssr_dir=$(mktemp -d)
  trap "rm -rf '$ssr_dir'" EXIT

  # Step 1: Parse Python to Ion.
  ion_file="$ssr_dir/${base_name}.python.st.ion"
  if ! (cd "$REPO_ROOT/Tools/Python" && python3 -m strata.gen py_to_strata \
        --dialect "$DIALECT" "$test_file" "$ion_file") > /dev/null 2>&1; then
    echo "SKIP (parse error): $base_name"
    skipped=$((skipped + 1))
    rm -rf "$ssr_dir"
    continue
  fi

  # Step 2: Generate — run pyAnalyzeLaurel --no-solve.
  # Capture both stdout and stderr; some tests produce expected errors.
  generate_output=$("$STRATA" pyAnalyzeLaurel "$ion_file" \
        --no-solve --vc-directory "$ssr_dir" --quiet 2>&1)
  generate_rc=$?

  if [ "$generate_rc" -ne 0 ]; then
    # Check if the expected output indicates a known limitation or user error.
    # These tests are expected to fail during generation — not an SSR issue.
    if grep -qE 'Known limitation|User error|Internal error' "$expected_file"; then
      echo "SKIP (expected error): $base_name"
      skipped=$((skipped + 1))
      rm -rf "$ssr_dir"
      continue
    fi
    echo "FAIL (generate): $base_name"
    failed=$((failed + 1))
    rm -rf "$ssr_dir"
    continue
  fi

  # Verify manifest was produced.
  if [ ! -f "$ssr_dir/manifest.json" ]; then
    echo "FAIL (no manifest): $base_name"
    failed=$((failed + 1))
    rm -rf "$ssr_dir"
    continue
  fi

  # Step 3: Solve — run solver on each .smt2 file.
  for smt_file in "$ssr_dir"/*.smt2; do
    [ -f "$smt_file" ] || continue
    result_file="${smt_file%.smt2}.result"
    # shellcheck disable=SC2086
    $solver_cmd "$smt_file" > "$result_file" 2>&1
  done

  # Step 4: Reconcile.
  reconcile_output=$("$STRATA" reconcile --vc-directory "$ssr_dir" 2>&1)
  reconcile_rc=$?

  # Step 5: Compare summary lines.
  # Extract DETAIL/RESULT from expected (direct verification) output.
  expected_summary=$(extract_summary "$expected_file")
  # Extract DETAIL/RESULT from reconcile output.
  reconcile_summary=$(echo "$reconcile_output" | grep -E '^(DETAIL|RESULT):' || true)

  if [ "$expected_summary" = "$reconcile_summary" ]; then
    echo "PASS: $base_name"
    passed=$((passed + 1))
  else
    echo "FAIL: $base_name"
    echo "  Expected: $expected_summary"
    echo "  Got:      $reconcile_summary"
    failed=$((failed + 1))
  fi

  rm -rf "$ssr_dir"
done

echo ""
echo "SSR test summary: $passed passed, $failed failed, $skipped skipped"
[ "$failed" -eq 0 ]
