#!/bin/bash
# Copyright Strata Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# =============================================================================
# hypothesmith.sh — Fuzz-test Strata's Python front-end
# =============================================================================
#
# This script generates random Python programs and runs them through Strata's
# Python front-end pipeline to find crashes, round-trip failures, and semantic
# modelling bugs. It is analogous to CBMC's scripts/csmith.sh, which uses
# CSmith to generate random C programs for testing CBMC.
#
# ## Background
#
# The approach is inspired by:
# - CSmith (https://embed.cs.utah.edu/csmith/) for random C program generation
# - hypothesmith (https://github.com/Zac-HD/hypothesmith) for random Python
#   program generation using the Hypothesis property-based testing framework
# - The discussion at https://bugs.python.org/issue42109 about using Hypothesis
#   and hypothesmith for testing CPython itself
#
# ## Modes
#
# **Syntax mode** — Uses hypothesmith's `from_grammar()` strategy to generate
# syntactically valid Python programs from the Python grammar. Each program is:
#   1. Parsed into Strata's Ion format via `python -m strata.gen py_to_strata`
#   2. Round-tripped through `strata toIon`
#   3. Diffed against the original Ion to check for round-trip fidelity
#
# This tests that the parser pipeline doesn't crash or lose information on
# arbitrary valid Python. Programs that fail to parse are SKIPped (hypothesmith
# may generate constructs the Strata parser doesn't support yet).
#
# **Semantic mode** — Uses a custom generator (gen_random_python.py) to produce
# typed Python programs with assertions whose expected values are computed by
# CPython at generation time. This is the CSmith checksum analogy:
#   1. CPython runs the program to confirm all assertions pass (reference)
#   2. The program is parsed into Ion format
#   3. `pyAnalyzeLaurel` verifies the program via the Laurel pipeline
#   4. If Strata reports a failing assertion on a program that CPython runs
#      correctly, that indicates a semantic modelling bug in the
#      Python → Laurel → Core translation pipeline
#
# ## Result classification
#
# Each test program gets one of these outcomes:
#   OK                — Pipeline completed successfully, all checks passed
#   SKIP (parse)      — Strata's parser couldn't handle the syntax (expected)
#   SKIP (unsupported)— pyAnalyzeLaurel hit an unsupported construct (expected)
#   TIMEOUT           — Analysis exceeded the time limit (not counted as failure)
#   FAIL (toIon)      — Ion round-trip produced different output (bug)
#   FAIL (diff)       — Ion diff detected a mismatch (bug)
#   FAIL (internal)   — Strata panicked or leaked memory (bug)
#   FAIL (verification)— Strata says assertion fails but CPython says it passes
#                        (semantic modelling bug)
#   BUG (generator)   — The generated program itself fails under CPython
#                        (bug in our generator, not in Strata)
#
# ## Reproducibility
#
# Every run uses a seed that controls both the Hypothesis engine (syntax mode)
# and Python's random module (semantic mode). Given the same seed, the same
# programs are generated. The seed is printed at the start and end of every
# run. To reproduce a failure:
#
#   cd Tools/Python
#   ./scripts/hypothesmith.sh 10 <SEED> both --unrestricted
#
# ## Usage
#
#   ./hypothesmith.sh [N [SEED [MODE [--unrestricted]]]]
#
#   N              Number of programs to generate per mode (default: 10)
#   SEED           Random seed for reproducibility (default: current timestamp)
#   MODE           "syntax", "semantic", or "both" (default: both)
#   --unrestricted Include generators for Python constructs beyond what Strata
#                  supports today (classes, generators, comprehensions,
#                  try/except, match, async, decorators, etc.)
#
# ## Prerequisites
#
#   - Python venv at Tools/Python/.venv with hypothesmith and strata installed:
#       python3 -m venv Tools/Python/.venv
#       Tools/Python/.venv/bin/pip install -e Tools/Python hypothesmith
#   - Strata built: lake build strata
#   - Python dialect file at Tools/Python/dialects/Python.dialect.st.ion
#
# ## Exit codes
#
#   0  All tests passed (or only SKIPs/TIMEOUTs)
#   1  At least one FAIL detected (source code is printed for reproduction)
#
# =============================================================================

set -euo pipefail

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TOOLS_PY="$REPO_ROOT/Tools/Python"
PYTHON="${PYTHON:-$TOOLS_PY/.venv/bin/python3}"
STRATA="$REPO_ROOT/.lake/build/bin/strata"
DIALECT="$TOOLS_PY/dialects/Python.dialect.st.ion"

# Command-line arguments with defaults.
N="${1:-10}"
SEED="${2:-$(date +%s)}"
MODE="${3:-both}"
UNRESTRICTED=""
if [ "${4:-}" = "--unrestricted" ]; then
  UNRESTRICTED="--unrestricted"
fi

# Timeouts (seconds) for individual pipeline steps.
# Parse timeout covers py_to_strata and toIon; analyse timeout covers
# pyAnalyzeLaurel which invokes the SMT solver.
PARSE_TIMEOUT=30
ANALYZE_TIMEOUT=90

# ---------------------------------------------------------------------------
# Prerequisite checks
# ---------------------------------------------------------------------------

if ! command -v "$PYTHON" &>/dev/null; then
  echo "ERROR: Python venv not found at $TOOLS_PY/.venv"
  echo "Set up with:"
  echo "  python3 -m venv $TOOLS_PY/.venv"
  echo "  $TOOLS_PY/.venv/bin/pip install -e $TOOLS_PY hypothesmith"
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

# ---------------------------------------------------------------------------
# Working directory (cleaned up on exit)
# ---------------------------------------------------------------------------

workdir=$(mktemp -d /tmp/strata-fuzz.XXX)
trap 'rm -rf "$workdir"' EXIT

failures=0

# ---------------------------------------------------------------------------
# Syntax mode
# ---------------------------------------------------------------------------
# Generate random syntactically-valid Python via hypothesmith, then test
# the parse → Ion → round-trip pipeline.

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

    # Step 1: Parse Python → Ion via the external Python tool.
    # Parse failures are acceptable — hypothesmith may generate constructs
    # that the Strata parser doesn't support yet.
    if ! timeout "$PARSE_TIMEOUT" "$PYTHON" -m strata.gen py_to_strata \
        --dialect "$DIALECT" "$pyfile" "$ion" 2>/dev/null; then
      echo "  SKIP (parse): $base"
      continue
    fi

    # Step 2: Round-trip the Ion through strata toIon.
    # This re-serialises the Ion file; a failure here means the Lean-side
    # reader or writer has a bug.
    if ! timeout "$PARSE_TIMEOUT" "$STRATA" toIon \
        --include "$TOOLS_PY/dialects" "$ion" "$ion2" 2>/dev/null; then
      echo "  FAIL (toIon): $base"
      echo "--- Source code ---"
      cat "$pyfile"
      echo "---"
      failures=$((failures + 1))
      continue
    fi

    # Step 3: Diff the original and round-tripped Ion files.
    # Any difference means information was lost or corrupted.
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

# ---------------------------------------------------------------------------
# Semantic mode
# ---------------------------------------------------------------------------
# Generate typed Python programs with known-true assertions, validate them
# with CPython, then verify with pyAnalyzeLaurel. A verification failure
# on a CPython-passing program indicates a semantic modelling bug.

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

    # Step 1: Sanity check — run with CPython to confirm assertions pass.
    # This is the "reference execution" (analogous to CSmith's GCC run
    # that computes the reference checksum). If CPython fails, the bug
    # is in our generator, not in Strata.
    if ! timeout 10 "$PYTHON" "$pyfile" 2>/dev/null; then
      echo "  BUG (generator): $base fails under CPython!"
      cat "$pyfile"
      sem_failures=$((sem_failures + 1))
      continue
    fi

    # Step 2: Parse Python → Ion.
    # Parse failures are acceptable — the generator may produce constructs
    # that the Strata parser doesn't support yet (same as syntax mode).
    if ! timeout "$PARSE_TIMEOUT" "$PYTHON" -m strata.gen py_to_strata \
        --dialect "$DIALECT" "$pyfile" "$ion" 2>/dev/null; then
      echo "  SKIP (parse): $base"
      continue
    fi

    # Step 3: Run pyAnalyzeLaurel — the full Python → Laurel → Core → SMT
    # verification pipeline.
    local output
    local ec=0
    output=$(timeout "$ANALYZE_TIMEOUT" "$STRATA" pyAnalyzeLaurel "$ion" 2>&1) || ec=$?

    # Handle timeouts (exit 124 from timeout, 137 from SIGKILL).
    if [ $ec -eq 124 ] || [ $ec -eq 137 ]; then
      echo "  TIMEOUT: $base"
      continue
    fi

    # Non-zero exit from pyAnalyzeLaurel. Distinguish between:
    # - Internal errors (panics, memory leaks) → real bugs, count as FAIL
    # - Translation failures → unsupported constructs, count as SKIP
    if [ $ec -ne 0 ]; then
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
      if echo "$output" | grep -q "RESULT: Failures found"; then
        echo "  FAIL (verification, exit $ec): $base"
        echo "--- Source code ---"
        cat "$pyfile"
        echo "--- pyAnalyzeLaurel output ---"
        echo "$output"
        echo "---"
        sem_failures=$((sem_failures + 1))
        continue
      fi
      if echo "$output" | grep -q "RESULT: Internal error"; then
        echo "  FAIL (internal error): $base"
        echo "--- Source code ---"
        cat "$pyfile"
        echo "--- Output ---"
        echo "$output" | head -20
        echo "---"
        sem_failures=$((sem_failures + 1))
        continue
      fi
      # Translation failures and other non-zero exits are unsupported
      # constructs — expected when using --unrestricted.
      echo "  SKIP (unsupported): $base"
      continue
    fi

    # Step 4: Check verification results. If pyAnalyzeLaurel reports any
    # failed assertions, but CPython ran the program successfully (Step 1),
    # then Strata's semantic model disagrees with CPython. This is the
    # most interesting kind of bug to find — analogous to CBMC finding a
    # counterexample to the CSmith checksum assertion.
    if echo "$output" | grep -qE '[1-9][0-9]* failed'; then
      echo "  FAIL (verification): $base"
      echo "  Strata reports a failing assertion on a program that CPython"
      echo "  runs correctly. This indicates a semantic modelling bug in"
      echo "  the Python → Laurel → Core translation pipeline."
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

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

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
