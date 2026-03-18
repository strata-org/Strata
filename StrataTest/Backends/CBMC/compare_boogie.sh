#!/bin/bash
# Compare StrataVerify, CBMC+z3, and cprover on Boogie benchmarks.
#
# Usage: ./compare_boogie.sh [file.bpl ...]
# If no files given, processes all .bpl in boogie/ directory.
#
# Environment:
#   CBMC, CPROVER, SYMTAB2GB — tool paths
#   STRATA_TIMEOUT           — per-benchmark wall-clock limit (default: 300s)
#   FUNC_TIMEOUT             — per-function solver timeout (default: 60s)

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
BOOGIE_DIR="$SCRIPT_DIR/boogie"
STRATA_VERIFY="$PROJECT_ROOT/.lake/build/bin/StrataVerify"
STRATA_CORE_TO_GOTO="$PROJECT_ROOT/.lake/build/bin/StrataCoreToGoto"
B2S="$PROJECT_ROOT/Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata.dll"
CBMC=${CBMC:-cbmc}
CPROVER=${CPROVER:-cprover}
SYMTAB2GB=${SYMTAB2GB:-symtab2gb}
TIMEOUT=${STRATA_TIMEOUT:-300}
FUNC_TIMEOUT=${FUNC_TIMEOUT:-60}

WORK=$(mktemp -d)
trap "rm -rf $WORK" EXIT

if [ $# -gt 0 ]; then FILES=("$@"); else FILES=("$BOOGIE_DIR"/*.bpl); fi

# Portable timeout (macOS has no coreutils timeout)
trun() { perl -e 'alarm shift @ARGV; exec @ARGV' "$@" 2>&1; }

printf "%-30s  %-18s  %-18s  %-18s\n" "Benchmark" "StrataVerify" "CBMC+z3" "cprover"
printf '%s\n' "$(printf '%.0s-' {1..90})"

sv_total=0; sv_pass=0
cbmc_total=0; cbmc_pass=0
cp_total=0; cp_pass=0

for bpl in "${FILES[@]}"; do
  [ -f "$bpl" ] || continue
  bn=$(basename "$bpl" .bpl)
  core="$WORK/${bn}.core.st"
  bench_start=$SECONDS

  # Step 1: Boogie → Strata Core
  if ! dotnet "$B2S" "$bpl" > "$core" 2>/dev/null; then
    printf "%-30s  %-18s  %-18s  %-18s\n" "$bn" "CONVERT_ERR" "-" "-"
    continue
  fi

  # Step 2: StrataVerify
  sv_out=$(trun "$TIMEOUT" "$STRATA_VERIFY" "$core")
  sv_rc=$?
  if [ $sv_rc -eq 142 ] || [ $sv_rc -eq 137 ]; then
    sv_result="TIMEOUT"
  elif echo "$sv_out" | grep -q "All.*goals passed"; then
    n=$(echo "$sv_out" | grep -oE '[0-9]+ goals passed' | grep -oE '[0-9]+')
    sv_result="PASS($n)"
    sv_pass=$((sv_pass+1))
  elif echo "$sv_out" | grep -q "❌"; then
    n=$(echo "$sv_out" | grep -c '❌')
    sv_result="FAIL($n)"
  else
    sv_result="ERROR"
  fi
  sv_total=$((sv_total+1))

  # Step 3: StrataCoreToGoto
  cbmc_result="-"; cp_result="-"
  goto_out=$(trun "$TIMEOUT" "$STRATA_CORE_TO_GOTO" --output-dir "$WORK" "$core")
  if [ $? -ne 0 ]; then
    cbmc_result="GOTO_ERR"; cp_result="GOTO_ERR"
  else
    symtab="$WORK/${bn}.symtab.json"
    gotojson="$WORK/${bn}.goto.json"
    gb="$WORK/${bn}.gb"

    if ! "$SYMTAB2GB" "$symtab" --goto-functions "$gotojson" --out "$gb" 2>/dev/null; then
      cbmc_result="SYMTAB_ERR"; cp_result="SYMTAB_ERR"
    else
      funcs=$("$CBMC" "$gb" --show-properties 2>&1 \
        | grep '  line .* function ' | sed 's/.* function //' | sort -u)

      # Helper: verify all functions with a given tool, respecting wall-clock cap
      # Usage: verify_funcs TOOL ARGS...
      # Sets: _ok _fail _err _n
      verify_funcs() {
        local tool="$1"; shift
        _ok=0; _fail=0; _err=0; _n=0
        for func in $funcs; do
          # Wall-clock cap per benchmark
          if [ $((SECONDS - bench_start)) -ge "$TIMEOUT" ]; then
            _err=$(( _err + $(echo "$funcs" | wc -w) - _n ))
            _n=$(echo "$funcs" | wc -w)
            break
          fi
          out=$(trun "$FUNC_TIMEOUT" "$tool" "$@" --function "$func" 2>&1)
          if echo "$out" | grep -q "VERIFICATION SUCCESSFUL\|^SUCCESS"; then
            _ok=$((_ok+1))
          elif echo "$out" | grep -q "VERIFICATION FAILED\|REFUTED"; then
            _fail=$((_fail+1))
          elif echo "$out" | grep -q "no properties"; then
            _ok=$((_ok+1))
          else
            _err=$((_err+1))
          fi
          _n=$((_n+1))
        done
      }

      fmt_result() {
        if [ "$_n" -eq 0 ]; then echo "NO_PROPS"
        elif [ "$_fail" -eq 0 ] && [ "$_err" -eq 0 ]; then echo "PASS($_ok)"
        elif [ "$_fail" -gt 0 ]; then echo "FAIL($_fail/$_n)"
        else echo "ERR($_err/$_n)"
        fi
      }

      # Step 4: CBMC
      verify_funcs "$CBMC" "$gb" --z3 --no-pointer-check --no-undefined-shift-check
      cbmc_result=$(fmt_result)
      [ "$_fail" -eq 0 ] && [ "$_err" -eq 0 ] && [ "$_n" -gt 0 ] && cbmc_pass=$((cbmc_pass+1))
      cbmc_total=$((cbmc_total+1))

      # Step 5: cprover
      verify_funcs "$CPROVER" "$gb" --no-safety --smt2-solver z3
      cp_result=$(fmt_result)
      [ "$_fail" -eq 0 ] && [ "$_err" -eq 0 ] && [ "$_n" -gt 0 ] && cp_pass=$((cp_pass+1))
      cp_total=$((cp_total+1))
    fi
  fi

  elapsed=$((SECONDS - bench_start))
  printf "%-30s  %-18s  %-18s  %-18s  %3ds\n" "$bn" "$sv_result" "$cbmc_result" "$cp_result" "$elapsed"
done

printf '%s\n' "$(printf '%.0s-' {1..90})"
printf "%-30s  %-18s  %-18s  %-18s\n" "Summary" \
  "$sv_pass/$sv_total pass" "$cbmc_pass/$cbmc_total pass" "$cp_pass/$cp_total pass"
printf "Timeouts: %ss/benchmark, %ss/function\n" "$TIMEOUT" "$FUNC_TIMEOUT"
