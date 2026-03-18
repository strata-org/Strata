#!/bin/bash
# Batch evaluation of Boogie benchmarks: StrataVerify vs CBMC vs cprover.
#
# Usage: ./eval_boogie_batch.sh [--resume] [--cbmc-only] [--sv-only] [--limit N]
#
# Writes results to boogie/results.csv (append mode with --resume).

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
BOOGIE_DIR="$SCRIPT_DIR/boogie"
RESULTS="$BOOGIE_DIR/results.csv"
STRATA_VERIFY="$PROJECT_ROOT/.lake/build/bin/StrataVerify"
STRATA_CORE_TO_GOTO="$PROJECT_ROOT/.lake/build/bin/StrataCoreToGoto"
B2S="$PROJECT_ROOT/Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata.dll"
CBMC=${CBMC:-cbmc}
CPROVER=${CPROVER:-cprover}
SYMTAB2GB=${SYMTAB2GB:-symtab2gb}
TIMEOUT=${STRATA_TIMEOUT:-120}
FUNC_TIMEOUT=${FUNC_TIMEOUT:-30}

RESUME=false; CBMC_ONLY=false; SV_ONLY=false; LIMIT=0; MAX_SIZE=0; MEM_MB=8192
while [ $# -gt 0 ]; do
  case "$1" in
    --resume) RESUME=true; shift;;
    --cbmc-only) CBMC_ONLY=true; shift;;
    --sv-only) SV_ONLY=true; shift;;
    --limit) LIMIT=$2; shift 2;;
    --max-size) MAX_SIZE=$2; shift 2;;
    --mem) MEM_MB=$2; shift 2;;
    *) echo "Unknown: $1"; exit 1;;
  esac
done

# Memory limit per child process (KB)
MEM_KB=$((MEM_MB * 1024))

WORK=$(mktemp -d)
trap "rm -rf $WORK" EXIT

trun() { local t=$1; shift; bash -c "ulimit -v $MEM_KB 2>/dev/null; exec perl -e 'alarm shift @ARGV; exec @ARGV' $t \"\$@\"" _ "$@" 2>&1; }

# Build done set from existing results
DONE_FILE=$(mktemp)
if $RESUME && [ -f "$RESULTS" ]; then
  tail -n+2 "$RESULTS" | cut -d, -f1 > "$DONE_FILE"
  done_n=$(wc -l < "$DONE_FILE" | tr -d ' ')
  echo "Resuming: $done_n already done"
else
  echo "benchmark,sv_result,sv_goals,cbmc_result,cbmc_ok,cbmc_total,cp_result,cp_ok,cp_total,time_s,size_bytes" > "$RESULTS"
  done_n=0
fi

FILES=("$BOOGIE_DIR"/*.bpl)
total=${#FILES[@]}
n=0

for bpl in "${FILES[@]}"; do
  [ -f "$bpl" ] || continue
  bn=$(basename "$bpl" .bpl)
  grep -qx "$bn" "$DONE_FILE" && continue
  n=$((n+1))
  [ "$LIMIT" -gt 0 ] && [ "$n" -gt "$LIMIT" ] && break

  sz=$(stat -f%z "$bpl" 2>/dev/null || stat -c%s "$bpl" 2>/dev/null)
  [ "$MAX_SIZE" -gt 0 ] && [ "$sz" -gt "$MAX_SIZE" ] && continue
  bench_start=$SECONDS
  core="$WORK/${bn}.core.st"

  # Convert
  if ! dotnet "$B2S" "$bpl" > "$core" 2>/dev/null; then
    echo "$bn,CONVERT_ERR,0,-,-,0,-,-,0,0,$sz" >> "$RESULTS"
    printf "\r[%d/%d] %-40s CONVERT_ERR" $((done_n+n)) "$total" "$bn"
    continue
  fi

  # StrataVerify
  sv_result="SKIP"; sv_goals=0
  if ! $CBMC_ONLY; then
    sv_out=$(trun "$TIMEOUT" "$STRATA_VERIFY" "$core")
    if echo "$sv_out" | grep -q "All.*goals passed"; then
      sv_goals=$(echo "$sv_out" | grep -oE '[0-9]+ goals passed' | grep -oE '[0-9]+')
      sv_result="PASS"
    elif [ $? -eq 142 ] || [ $? -eq 137 ]; then sv_result="TIMEOUT"
    elif echo "$sv_out" | grep -q "❌"; then sv_result="FAIL"
    else sv_result="ERROR"
    fi
  fi

  # GOTO translation + CBMC + cprover
  cbmc_result="SKIP"; cbmc_ok=0; cbmc_total=0
  cp_result="SKIP"; cp_ok=0; cp_total=0
  if ! $SV_ONLY; then
    goto_out=$(trun "$TIMEOUT" "$STRATA_CORE_TO_GOTO" --output-dir "$WORK" "$core" 2>&1)
    if [ $? -ne 0 ]; then
      cbmc_result="GOTO_ERR"; cp_result="GOTO_ERR"
    else
      symtab="$WORK/${bn}.symtab.json"; gotojson="$WORK/${bn}.goto.json"; gb="$WORK/${bn}.gb"
      if ! "$SYMTAB2GB" "$symtab" --goto-functions "$gotojson" --out "$gb" 2>/dev/null; then
        cbmc_result="SYMTAB_ERR"; cp_result="SYMTAB_ERR"
      else
        funcs=$("$CBMC" "$gb" --show-properties 2>&1 | grep '  line .* function ' | sed 's/.* function //' | sort -u)
        # CBMC
        cbmc_ok=0; cbmc_fail=0; cbmc_err=0
        for func in $funcs; do
          [ $((SECONDS - bench_start)) -ge "$TIMEOUT" ] && { cbmc_err=$((cbmc_err+1)); continue; }
          out=$(trun "$FUNC_TIMEOUT" "$CBMC" "$gb" --z3 --no-pointer-check --no-undefined-shift-check --function "$func" 2>&1)
          if echo "$out" | grep -q "VERIFICATION SUCCESSFUL"; then cbmc_ok=$((cbmc_ok+1))
          elif echo "$out" | grep -q "VERIFICATION FAILED"; then cbmc_fail=$((cbmc_fail+1))
          else cbmc_err=$((cbmc_err+1)); fi
          cbmc_total=$((cbmc_total+1))
        done
        [ -z "$funcs" ] && cbmc_result="NO_PROPS" || \
        { [ $cbmc_fail -eq 0 ] && [ $cbmc_err -eq 0 ] && cbmc_result="PASS" || \
          { [ $cbmc_fail -gt 0 ] && cbmc_result="FAIL" || cbmc_result="ERROR"; }; }

        # cprover
        cp_ok=0; cp_fail=0; cp_err=0
        for func in $funcs; do
          [ $((SECONDS - bench_start)) -ge "$TIMEOUT" ] && { cp_err=$((cp_err+1)); continue; }
          out=$(trun "$FUNC_TIMEOUT" "$CPROVER" "$gb" --no-safety --smt2-solver z3 --function "$func" 2>&1)
          if echo "$out" | grep -q "SUCCESS\|no properties"; then cp_ok=$((cp_ok+1))
          elif echo "$out" | grep -q "REFUTED"; then cp_fail=$((cp_fail+1))
          else cp_err=$((cp_err+1)); fi
          cp_total=$((cp_total+1))
        done
        [ -z "$funcs" ] && cp_result="NO_PROPS" || \
        { [ $cp_fail -eq 0 ] && [ $cp_err -eq 0 ] && cp_result="PASS" || \
          { [ $cp_fail -gt 0 ] && cp_result="FAIL" || cp_result="ERROR"; }; }
      fi
    fi
  fi

  elapsed=$((SECONDS - bench_start))
  echo "$bn,$sv_result,$sv_goals,$cbmc_result,$cbmc_ok,$cbmc_total,$cp_result,$cp_ok,$cp_total,$elapsed,$sz" >> "$RESULTS"
  printf "\r[%d/%d] %-40s SV=%-8s CBMC=%-8s CP=%-8s %3ds" \
    $((done_n+n)) "$total" "$bn" "$sv_result" "$cbmc_result" "$cp_result" "$elapsed"
  # Clean up temp files for this benchmark
  rm -f "$WORK/${bn}".*
done

echo ""
echo "Results written to $RESULTS"

# Summary
if [ -f "$RESULTS" ]; then
  echo ""
  echo "=== Summary ==="
  total_done=$(tail -n+2 "$RESULTS" | wc -l)
  sv_pass=$(tail -n+2 "$RESULTS" | awk -F, '$2=="PASS"' | wc -l)
  cbmc_pass=$(tail -n+2 "$RESULTS" | awk -F, '$4=="PASS"' | wc -l)
  cp_pass=$(tail -n+2 "$RESULTS" | awk -F, '$7=="PASS"' | wc -l)
  sv_err=$(tail -n+2 "$RESULTS" | awk -F, '$2=="ERROR" || $2=="TIMEOUT"' | wc -l)
  cbmc_err=$(tail -n+2 "$RESULTS" | awk -F, '$4=="ERROR" || $4=="GOTO_ERR" || $4=="SYMTAB_ERR"' | wc -l)
  printf "Evaluated:     %d benchmarks\n" "$total_done"
  printf "StrataVerify:  %d pass, %d error/timeout\n" "$sv_pass" "$sv_err"
  printf "CBMC+z3:       %d pass, %d error\n" "$cbmc_pass" "$cbmc_err"
  printf "cprover:       %d pass\n" "$cp_pass"
fi
