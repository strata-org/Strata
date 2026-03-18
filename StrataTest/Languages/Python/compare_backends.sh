#!/bin/bash
#
# Compare verification outcomes across backends for Python test suite.
#
# Backends compared:
#   1. pyAnalyzeLaurel — Strata's SMT-based verifier (cvc5)
#   2. CBMC+z3         — CBMC bounded model checker with Z3 solver
#   3. CBMC+cvc5       — CBMC bounded model checker with cvc5 solver
#      (only if --with-cvc5 is passed)
#
# Prerequisites:
#   - Strata built:  lake build strata:exe
#   - CBMC built with Z3 support (and optionally cvc5)
#   - Python strata.gen available in Tools/Python/
#   - cvc5 on PATH (for pyAnalyzeLaurel and optionally CBMC+cvc5)
#
# Usage:
#   ./compare_backends.sh [--with-cvc5] [--timeout SECS]
#
# Environment variables:
#   CBMC          — path to cbmc binary (default: cbmc)
#   CBMC_TIMEOUT  — per-test timeout in seconds (default: 120)
#
# Example:
#   CBMC=~/AwsArgCBMC/build/bin/cbmc ./compare_backends.sh --with-cvc5
#
set -o pipefail

WITH_CVC5=false
WITH_SLICE=false
WITH_CPROVER=false
CBMC_TIMEOUT=${CBMC_TIMEOUT:-120}

while [ $# -gt 0 ]; do
  case "$1" in
    --with-cvc5)    WITH_CVC5=true; shift ;;
    --with-slice)   WITH_SLICE=true; shift ;;
    --with-cprover) WITH_CPROVER=true; shift ;;
    --timeout)      CBMC_TIMEOUT="$2"; shift 2 ;;
    *)              echo "Unknown option: $1" >&2; exit 1 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
LAUREL_EXPECTED="$SCRIPT_DIR/expected_laurel"
DIALECT="$PROJECT_ROOT/Tools/Python/dialects/Python.dialect.st.ion"
PYTHON=${PYTHON:-python3}
CBMC=${CBMC:-cbmc}
CPROVER=${CPROVER:-cprover}
STRATA="$PROJECT_ROOT/.lake/build/bin/strata"

# --- helpers ---

# Generate .py.ion from .py if needed
gen_ion() {
  local py="$1" ion="${1}.ion"
  [ -f "$ion" ] && return 0
  (cd "$PROJECT_ROOT/Tools/Python" && \
    "$PYTHON" -m strata.gen py_to_strata --dialect "$DIALECT" "$py" "$ion") 2>/dev/null
}

# Run pyAnalyzeLaurel, return: PASS / PASS*(N unknown) / FAIL(N) / SKIP
run_laurel() {
  local ion="$1" name="$2"
  local ef="$LAUREL_EXPECTED/${name}.expected"
  [ -f "$ef" ] || { echo "SKIP"; return; }
  local out
  out=$("$STRATA" pyAnalyzeLaurel "$ion" 2>/dev/null) || { echo "ERROR"; return; }
  local fails unknowns passes
  fails=$(echo "$out" | grep -c '❌' || true)
  unknowns=$(echo "$out" | grep -c '🟡' || true)
  passes=$(echo "$out" | grep -c '✅' || true)
  if [ "$fails" -gt 0 ]; then echo "FAIL($fails)"
  elif [ "$unknowns" -gt 0 ]; then echo "PASS*($unknowns unk)"
  else echo "PASS"; fi
}

# Run CBMC with given solver flag and optional extra flags, return: PASS / FAIL / TIMEOUT / ERROR
run_cbmc() {
  local ion="$1" solver_flag="$2" extra_flags="${3:-} --no-pointer-check"
  local out t0 t1 elapsed
  t0=$(date +%s)
  out=$(CBMC_TIMEOUT="$CBMC_TIMEOUT" CBMC="$CBMC" \
        CBMC_SOLVER_FLAG="$solver_flag" CBMC_EXTRA_FLAGS="$extra_flags" \
        "$SCRIPT_DIR/py_ion_to_cbmc.sh" "$ion" 2>&1)
  local rc=$?
  t1=$(date +%s)
  elapsed=$((t1 - t0))
  local result
  if echo "$out" | grep -q "VERIFICATION SUCCESSFUL"; then
    if echo "$out" | grep -q "Generated 0 VCC"; then result="PASS(0)"
    else result="PASS"; fi
  elif echo "$out" | grep -q "timeout"; then result="TIMEOUT"
  elif echo "$out" | grep -q "VERIFICATION FAILED"; then result="FAIL"
  elif echo "$out" | grep -q "no entry point"; then result="NO_MAIN"
  elif echo "$out" | grep -q "VERIFICATION ERROR"; then result="UNKNOWN"
  else result="ERROR"; fi
  echo "${result}(${elapsed}s)"
}

# Run cprover (CHC-based), return: PASS / FAIL / TIMEOUT / ERROR
run_cprover() {
  local ion="$1"
  local out t0 t1 elapsed
  t0=$(date +%s)
  out=$(CBMC_TIMEOUT="$CBMC_TIMEOUT" CBMC="$CPROVER" \
        CBMC_SOLVER_FLAG="" CBMC_EXTRA_FLAGS="--smt2-solver z3 --no-safety" CBMC_VERBOSITY="" \
        "$SCRIPT_DIR/py_ion_to_cbmc.sh" "$ion" 2>&1)
  local rc=$?
  t1=$(date +%s)
  elapsed=$((t1 - t0))
  local result
  if echo "$out" | grep -q "VERIFICATION SUCCESSFUL"; then
    if echo "$out" | grep -q "Generated 0 VCC"; then result="PASS(0)"
    else result="PASS"; fi
  elif echo "$out" | grep -q "no properties to show"; then result="PASS(0)"
  elif echo "$out" | grep -q "timeout"; then result="TIMEOUT"
  elif echo "$out" | grep -q "VERIFICATION FAILED"; then result="FAIL"
  elif echo "$out" | grep -q "VERIFICATION ERROR"; then result="UNKNOWN"
  elif echo "$out" | grep -q "REFUTED"; then result="FAIL"
  elif echo "$out" | grep -q "SUCCESS"; then result="PASS"
  else result="ERROR"; fi
  echo "${result}(${elapsed}s)"
}

# --- main ---

echo "Generating .py.ion files..."
for py in "$TESTS_DIR"/*.py; do
  [ -f "$py" ] || continue
  gen_ion "$py"
done

# Collect test names
tests=()
for ion in "$TESTS_DIR"/*.py.ion; do
  [ -f "$ion" ] || continue
  tests+=("$ion")
done

# Header
cols=("%-32s" "%-14s" "%-14s")
hdrs=("Test" "pyAnalyzeLaurel" "CBMC+z3")
if $WITH_SLICE; then
  cols+=("%-14s"); hdrs+=("z3+slice")
fi
if $WITH_CVC5; then
  cols+=("%-14s"); hdrs+=("CBMC+cvc5")
  if $WITH_SLICE; then
    cols+=("%-14s"); hdrs+=("cvc5+slice")
  fi
fi
if $WITH_CPROVER; then
  cols+=("%-14s"); hdrs+=("cprover")
fi
hdr=$(IFS='|'; printf " %s " "${cols[*]}" | sed 's/  / | /g')
# shellcheck disable=SC2059
printf "$hdr\n" "${hdrs[@]}"
divider() {
  local w=$(( (${#cols[@]} * 17) ))
  printf '%*s\n' "$w" '' | tr ' ' '-'
}

divider

for ion in "${tests[@]}"; do
  bn=$(basename "$ion")
  name="${bn%.py.ion}"

  laurel=$(run_laurel "$ion" "$name")
  cbmc_z3=$(run_cbmc "$ion" "--z3")
  vals=("$name" "$laurel" "$cbmc_z3")
  if $WITH_SLICE; then
    cbmc_z3_slice=$(run_cbmc "$ion" "--z3" "--slice-formula")
    vals+=("$cbmc_z3_slice")
  fi
  if $WITH_CVC5; then
    cbmc_cvc5=$(run_cbmc "$ion" "--cvc5")
    vals+=("$cbmc_cvc5")
    if $WITH_SLICE; then
      cbmc_cvc5_slice=$(run_cbmc "$ion" "--cvc5" "--slice-formula")
      vals+=("$cbmc_cvc5_slice")
    fi
  fi
  if $WITH_CPROVER; then
    cprover_result=$(run_cprover "$ion")
    vals+=("$cprover_result")
  fi
  # shellcheck disable=SC2059
  printf "$hdr\n" "${vals[@]}"
done

divider
echo "Timeout: ${CBMC_TIMEOUT}s per test"
