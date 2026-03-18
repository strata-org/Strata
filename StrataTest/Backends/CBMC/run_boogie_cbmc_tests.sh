#!/bin/bash
#
# Compare verification outcomes for Boogie benchmarks across backends:
#   1. StrataVerify — Strata's native SMT-based verifier
#   2. CBMC+z3     — CBMC bounded model checker
#   3. cprover     — CHC-based verifier (optional, --with-cprover)
#
# Usage:
#   ./run_boogie_cbmc_tests.sh [--with-cprover] [--timeout SECS] [file.bpl ...]
#
# If no files are given, processes all .bpl files in the boogie/ directory.
#
# Environment variables:
#   CBMC          — path to cbmc binary (default: cbmc)
#   CPROVER       — path to cprover binary (default: cprover)
#   GOTO_CC       — path to goto-cc binary (default: goto-cc)
#   STRATA_TIMEOUT — per-test timeout in seconds (default: 120)

set -o pipefail

WITH_CPROVER=false
STRATA_TIMEOUT=${STRATA_TIMEOUT:-120}

while [ $# -gt 0 ]; do
  case "$1" in
    --with-cprover) WITH_CPROVER=true; shift ;;
    --timeout)      STRATA_TIMEOUT="$2"; shift 2 ;;
    -*)             echo "Unknown option: $1" >&2; exit 1 ;;
    *)              break ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
BOOGIE_DIR="$SCRIPT_DIR/boogie"
STRATA="$PROJECT_ROOT/.lake/build/bin/strata"
STRATA_VERIFY="$PROJECT_ROOT/.lake/build/bin/StrataVerify"
STRATA_CORE_TO_GOTO="$PROJECT_ROOT/.lake/build/bin/StrataCoreToGoto"
BOOGIE_TO_STRATA="$PROJECT_ROOT/Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata.dll"
CBMC=${CBMC:-cbmc}
CPROVER=${CPROVER:-cprover}
GOTO_CC=${GOTO_CC:-goto-cc}

WORK_DIR=$(mktemp -d)
cleanup() { rm -rf "$WORK_DIR"; }
trap cleanup EXIT

# Collect files
if [ $# -gt 0 ]; then
  FILES=("$@")
else
  FILES=("$BOOGIE_DIR"/*.bpl)
fi

# Header
cols="%-40s %-20s %-20s"
hdrs=("Test" "StrataVerify" "CBMC+z3")
if $WITH_CPROVER; then
  cols="$cols %-20s"
  hdrs+=("cprover")
fi
printf "$cols\n" "${hdrs[@]}"
printf '%*s\n' 80 '' | tr ' ' '-'

passed=0
failed=0
errors=0

for bpl_file in "${FILES[@]}"; do
  [ -f "$bpl_file" ] || continue
  bn=$(basename "$bpl_file" .bpl)
  core_file="$WORK_DIR/${bn}.core.st"

  # Step 1: Convert Boogie to Strata Core
  if ! dotnet "$BOOGIE_TO_STRATA" "$bpl_file" > "$core_file" 2>/dev/null; then
    printf "$cols\n" "$bn" "CONVERT_ERR" "-" ${WITH_CPROVER:+"-"}
    errors=$((errors + 1))
    continue
  fi

  # Step 2: StrataVerify
  sv_out=$(perl -e 'alarm shift @ARGV; exec @ARGV' "$STRATA_TIMEOUT" "$STRATA_VERIFY" "$core_file" 2>&1)
  sv_rc=$?
  if [ $sv_rc -eq 124 ]; then
    sv_result="TIMEOUT"
  elif echo "$sv_out" | grep -q "All.*goals passed"; then
    n_goals=$(echo "$sv_out" | grep -oE '[0-9]+ goals passed' | grep -oE '[0-9]+')
    sv_result="PASS($n_goals)"
  elif echo "$sv_out" | grep -q "❌"; then
    n_fail=$(echo "$sv_out" | grep -c '❌')
    sv_result="FAIL($n_fail)"
  else
    sv_result="ERROR"
  fi

  # Step 3: StrataCoreToGoto
  cbmc_result="-"
  cprover_result="-"
  if perl -e 'alarm shift @ARGV; exec @ARGV' "$STRATA_TIMEOUT" "$STRATA_CORE_TO_GOTO" --output-dir "$WORK_DIR" "$core_file" > /dev/null 2>&1; then
    symtab="$WORK_DIR/${bn}.symtab.json"
    gotojson="$WORK_DIR/${bn}.goto.json"
    gb="$WORK_DIR/${bn}.gb"

    if "$GOTO_CC" --function main "$gb" -o "$gb" 2>/dev/null; then
      : # goto-cc succeeded
    fi

    if symtab2gb "$symtab" --goto-functions "$gotojson" --out "$gb" 2>/dev/null; then
      # Find procedures with properties and verify each
      props=$("$CBMC" "$gb" --show-properties 2>&1 | grep '^Property ' | sed 's/Property //' | sed 's/:.*//' | sort -u)
      # Extract function names from properties
      funcs=$(echo "$props" | sed 's/\.[^.]*$//' | sort -u)
      if [ -z "$funcs" ]; then
        cbmc_result="NO_PROPS"
      else
        cbmc_pass=0; cbmc_fail=0; cbmc_err=0
        for func in $funcs; do
          "$GOTO_CC" --function "$func" "$gb" -o "$WORK_DIR/${bn}_entry.gb" 2>/dev/null
          out=$(perl -e 'alarm shift @ARGV; exec @ARGV' "$STRATA_TIMEOUT" "$CBMC" "$WORK_DIR/${bn}_entry.gb" --z3 \
            --no-pointer-check --no-bounds-check --function "$func" 2>&1)
          if echo "$out" | grep -q "VERIFICATION SUCCESSFUL"; then
            cbmc_pass=$((cbmc_pass + 1))
          elif echo "$out" | grep -q "VERIFICATION FAILED"; then
            cbmc_fail=$((cbmc_fail + 1))
          else
            cbmc_err=$((cbmc_err + 1))
          fi
        done
        total=$((cbmc_pass + cbmc_fail + cbmc_err))
        if [ $cbmc_fail -eq 0 ] && [ $cbmc_err -eq 0 ]; then
          cbmc_result="PASS($cbmc_pass)"
        elif [ $cbmc_err -gt 0 ]; then
          cbmc_result="ERR($cbmc_pass/$total)"
        else
          cbmc_result="FAIL($cbmc_fail/$total)"
        fi
      fi

      # Step 5: cprover (optional)
      if $WITH_CPROVER; then
        cp_out=$(perl -e 'alarm shift @ARGV; exec @ARGV' "$STRATA_TIMEOUT" "$CPROVER" "$gb" \
          --smt2-solver z3 --no-safety 2>&1)
        cp_rc=$?
        if [ $cp_rc -eq 124 ]; then
          cprover_result="TIMEOUT"
        elif echo "$cp_out" | grep -q "REFUTED"; then
          cprover_result="FAIL"
        elif echo "$cp_out" | grep -q "SUCCESS"; then
          cprover_result="PASS"
        elif echo "$cp_out" | grep -q "no properties"; then
          cprover_result="PASS(0)"
        else
          cprover_result="ERROR"
        fi
      fi
    else
      cbmc_result="SYMTAB_ERR"
      cprover_result="SYMTAB_ERR"
    fi
  else
    cbmc_result="GOTO_ERR"
    cprover_result="GOTO_ERR"
  fi

  vals=("$bn" "$sv_result" "$cbmc_result")
  if $WITH_CPROVER; then
    vals+=("$cprover_result")
  fi
  printf "$cols\n" "${vals[@]}"
done

printf '%*s\n' 80 '' | tr ' ' '-'
echo "Timeout: ${STRATA_TIMEOUT}s per test"
