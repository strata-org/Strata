#!/bin/bash
# Copyright Strata Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# Fuzz-test Strata's Python front-end with randomly generated programs.
#
# Usage:
#   ./hypothesmith.sh [N [SEED [MODE [--unrestricted]]]]
#
#   N     Number of programs to generate (default: 10)
#   SEED  Random seed for reproducibility (default: current timestamp)
#   MODE  "syntax" or "semantic" or "both" (default: both)
#   --unrestricted  Include Python constructs beyond what Strata supports today
#
# Requires:
#   - The venv at Tools/Python/.venv with hypothesmith and strata installed
#   - strata built (lake build strata)
#   - The Python dialect file at Tools/Python/dialects/Python.dialect.st.ion
#
# Exit codes:
#   0  All tests passed
#   1  At least one test failed (source code is printed for reproduction)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TOOLS_PY="$REPO_ROOT/Tools/Python"
PYTHON="$TOOLS_PY/.venv/bin/python3"
STRATA="$REPO_ROOT/.lake/build/bin/strata"
DIALECT="$TOOLS_PY/dialects/Python.dialect.st.ion"

N="${1:-10}"
SEED="${2:-$(date +%s)}"
MODE="${3:-both}"
UNRESTRICTED=""
if [ "${4:-}" = "--unrestricted" ]; then
  UNRESTRICTED="--unrestricted"
fi

# Timeouts (seconds)
PARSE_TIMEOUT=30
ANALYZE_TIMEOUT=90

if [ ! -x "$PYTHON" ]; then
  echo "ERROR: Python venv not found at $TOOLS_PY/.venv"
  echo "Run: python3 -m venv $TOOLS_PY/.venv && $TOOLS_PY/.venv/bin/pip install -e $TOOLS_PY -e ~/hypothesmith.git"
  exit 1
fi

if [ ! -f "$STRATA" ]; then
  echo "ERROR: strata not built. Run: lake build strata"
  exit 1
fi

if [ ! -f "$DIALECT" ]; then
  echo "ERROR: Python dialect not found at $DIALECT"
  exit 1
fi

workdir=$(mktemp -d /tmp/strata-fuzz.XXX)
trap 'rm -rf "$workdir"' EXIT

failures=0

run_syntax_tests() {
  local gen_dir="$workdir/syntax"
  echo "=== Syntax mode: generating $N programs (seed=$SEED) ==="
  timeout 120 "$PYTHON" "$SCRIPT_DIR/gen_random_python.py" \
    --mode syntax --output-dir "$gen_dir" \
    --max-examples "$N" --max-nodes 50 --seed "$SEED" 2>&1

  local count=0
  for pyfile in "$gen_dir"/fuzz_syntax_*.py; do
    [ -f "$pyfile" ] || continue
    count=$((count + 1))
    local base
    base=$(basename "$pyfile" .py)
    local ion="$gen_dir/${base}.python.st.ion"
    local ion2="$gen_dir/${base}.python.st.ion2"

    # Step 1: Parse Python -> Ion
    if ! timeout "$PARSE_TIMEOUT" "$PYTHON" -m strata.gen py_to_strata \
        --dialect "$DIALECT" "$pyfile" "$ion" 2>/dev/null; then
      # Parse failure is acceptable — hypothesmith may generate constructs
      # the Strata parser doesn't support yet. Just skip.
      echo "  SKIP (parse): $base"
      continue
    fi

    # Step 2: Ion round-trip
    if ! timeout "$PARSE_TIMEOUT" "$STRATA" toIon \
        --include "$TOOLS_PY/dialects" "$ion" "$ion2" 2>/dev/null; then
      echo "  FAIL (toIon): $base"
      echo "--- Source code ---"
      cat "$pyfile"
      echo "---"
      failures=$((failures + 1))
      continue
    fi

    # Step 3: Diff
    if ! "$STRATA" diff --include "$TOOLS_PY/dialects" "$ion" "$ion2" 2>/dev/null; then
      echo "  FAIL (diff): $base"
      echo "--- Source code ---"
      cat "$pyfile"
      echo "---"
      failures=$((failures + 1))
      continue
    fi

    echo "  OK: $base"
  done
  echo "Syntax tests: $count processed, $failures failures"
}

run_semantic_tests() {
  local gen_dir="$workdir/semantic"
  echo "=== Semantic mode: generating $N programs (seed=$SEED) ==="
  "$PYTHON" "$SCRIPT_DIR/gen_random_python.py" \
    --mode semantic --output-dir "$gen_dir" \
    --max-examples "$N" --seed "$SEED" $UNRESTRICTED 2>&1

  local count=0
  local sem_failures=0
  for pyfile in "$gen_dir"/fuzz_semantic_*.py; do
    [ -f "$pyfile" ] || continue
    count=$((count + 1))
    local base
    base=$(basename "$pyfile" .py)
    local ion="$gen_dir/${base}.python.st.ion"

    # Step 1: Sanity check — run with CPython to confirm assertions pass
    if ! timeout 10 python3 "$pyfile" 2>/dev/null; then
      echo "  BUG (generator): $base fails under CPython!"
      cat "$pyfile"
      sem_failures=$((sem_failures + 1))
      continue
    fi

    # Step 2: Parse Python -> Ion
    if ! timeout "$PARSE_TIMEOUT" "$PYTHON" -m strata.gen py_to_strata \
        --dialect "$DIALECT" "$pyfile" "$ion" 2>/dev/null; then
      echo "  FAIL (parse): $base"
      echo "--- Source code ---"
      cat "$pyfile"
      echo "---"
      sem_failures=$((sem_failures + 1))
      continue
    fi

    # Step 3: Run pyAnalyzeLaurel
    local output
    local ec=0
    output=$(timeout "$ANALYZE_TIMEOUT" "$STRATA" pyAnalyzeLaurel "$ion" 2>&1) || ec=$?

    if [ $ec -eq 124 ] || [ $ec -eq 137 ]; then
      echo "  TIMEOUT: $base"
      continue
    fi

    if [ $ec -ne 0 ]; then
      # Non-zero exit from pyAnalyzeLaurel — could be unsupported construct.
      # Check if it's an internal error vs. expected limitation.
      if echo "$output" | grep -qi "panic\|LEAK"; then
        echo "  FAIL (internal error): $base"
        echo "--- Source code ---"
        cat "$pyfile"
        echo "--- Output ---"
        echo "$output" | head -20
        echo "---"
        sem_failures=$((sem_failures + 1))
        continue
      fi
      # Translation failures and other non-zero exits are unsupported constructs
      echo "  SKIP (unsupported): $base"
      continue
    fi

    # Step 4: Check that all assertions passed (no "failed" in DETAIL line)
    if echo "$output" | grep -qE '[1-9][0-9]* failed'; then
      echo "  FAIL (verification): $base"
      echo "  Strata reports a failing assertion on a program that CPython runs correctly."
      echo "  This indicates a semantic modelling bug in the Python-to-Core pipeline."
      echo "--- Source code ---"
      cat "$pyfile"
      echo "--- pyAnalyzeLaurel output ---"
      echo "$output"
      echo "---"
      sem_failures=$((sem_failures + 1))
      continue
    fi

    echo "  OK: $base"
  done
  failures=$((failures + sem_failures))
  echo "Semantic tests: $count processed, $sem_failures failures"
}

echo "Strata Python front-end fuzz test"
echo "Seed: $SEED  N: $N  Mode: $MODE  Unrestricted: ${UNRESTRICTED:-no}"
echo ""

case "$MODE" in
  syntax)   run_syntax_tests ;;
  semantic) run_semantic_tests ;;
  both)     run_syntax_tests; echo ""; run_semantic_tests ;;
  *)        echo "Unknown mode: $MODE"; exit 1 ;;
esac

echo ""
if [ $failures -ne 0 ]; then
  echo "FAILED: $failures failure(s). Seed was: $SEED"
  exit 1
fi
echo "ALL PASSED. Seed was: $SEED"
