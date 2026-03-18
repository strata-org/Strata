#!/bin/bash
# Parallel batch evaluation of Boogie benchmarks: StrataVerify vs CBMC vs cprover.
#
# Usage: ./eval_boogie_parallel.sh [OPTIONS]
#
# Options:
#   --max-size BYTES   Only process files up to this size (default: 0 = no limit)
#   --jobs N           Parallel jobs (default: nproc/2)
#   --timeout SECS     Per-benchmark wall-clock limit (default: 120)
#   --func-timeout S   Per-function solver timeout (default: 30)
#   --mem MB           Memory limit per process (default: 8192)
#   --resume           Skip benchmarks already in results.csv
#   --sv-only          Only run StrataVerify
#   --cbmc-only        Only run CBMC (skip StrataVerify)
#   --limit N          Process at most N benchmarks
#   --results FILE     Output CSV file (default: boogie/results.csv)
#
# Prerequisites (must be on PATH or set via env vars):
#   CBMC, CPROVER, SYMTAB2GB, STRATA_VERIFY, STRATA_CORE_TO_GOTO, B2S
#
# To run on a remote host:
#   1. Build: lake build strata:exe StrataVerify StrataCoreToGoto
#   2. Build CBMC: cmake --build build --target cbmc cprover symtab2gb
#   3. Install .NET SDK (for BoogieToStrata)
#   4. Download benchmarks: aws s3 sync s3://strata-equalizer-benchmarks-c96ce85be672495ab39560273c1b2432/boogie-files/ boogie/
#   5. Run: ./eval_boogie_parallel.sh --jobs 16 --max-size 300000

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
BOOGIE_DIR="$SCRIPT_DIR/boogie"

# Tool paths (override via env vars)
STRATA_VERIFY="${STRATA_VERIFY:-$PROJECT_ROOT/.lake/build/bin/StrataVerify}"
STRATA_CORE_TO_GOTO="${STRATA_CORE_TO_GOTO:-$PROJECT_ROOT/.lake/build/bin/StrataCoreToGoto}"
B2S="${B2S:-$PROJECT_ROOT/Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata.dll}"
CBMC="${CBMC:-cbmc}"
CPROVER="${CPROVER:-cprover}"
SYMTAB2GB="${SYMTAB2GB:-symtab2gb}"

# Defaults
JOBS=$(( $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4) / 2 ))
[ "$JOBS" -lt 1 ] && JOBS=1
TIMEOUT=120
FUNC_TIMEOUT=30
MEM_MB=8192
MAX_SIZE=0
RESUME=false
CBMC_ONLY=false
SV_ONLY=false
LIMIT=0
RESULTS="$BOOGIE_DIR/results.csv"

while [ $# -gt 0 ]; do
  case "$1" in
    --jobs) JOBS=$2; shift 2;;
    --timeout) TIMEOUT=$2; shift 2;;
    --func-timeout) FUNC_TIMEOUT=$2; shift 2;;
    --mem) MEM_MB=$2; shift 2;;
    --max-size) MAX_SIZE=$2; shift 2;;
    --resume) RESUME=true; shift;;
    --cbmc-only) CBMC_ONLY=true; shift;;
    --sv-only) SV_ONLY=true; shift;;
    --limit) LIMIT=$2; shift 2;;
    --results) RESULTS=$2; shift 2;;
    -h|--help) head -25 "$0" | tail -23; exit 0;;
    *) echo "Unknown: $1" >&2; exit 1;;
  esac
done

MEM_KB=$((MEM_MB * 1024))

# Portable timeout + memory limit
trun() {
  local t=$1; shift
  bash -c "ulimit -v $MEM_KB 2>/dev/null; exec perl -e 'alarm shift @ARGV; exec @ARGV' $t \"\$@\"" _ "$@" 2>&1
}

# Worker function: evaluate one benchmark, output CSV line to stdout
eval_one() {
  local bpl="$1"
  local bn=$(basename "$bpl" .bpl)
  local work=$(mktemp -d)
  trap "rm -rf $work" RETURN
  local core="$work/${bn}.core.st"
  local sz=$(stat -f%z "$bpl" 2>/dev/null || stat -c%s "$bpl" 2>/dev/null)
  local t0=$SECONDS

  # Convert Boogie → Strata Core
  if ! dotnet "$B2S" "$bpl" > "$core" 2>/dev/null; then
    echo "$bn,CONVERT_ERR,0,-,-,0,-,-,0,$((SECONDS-t0)),$sz"
    return
  fi

  # StrataVerify
  local sv_result="SKIP" sv_goals=0
  if ! $CBMC_ONLY; then
    local sv_out
    sv_out=$(trun "$TIMEOUT" "$STRATA_VERIFY" "$core")
    local sv_rc=$?
    if echo "$sv_out" | grep -q "All.*goals passed"; then
      sv_goals=$(echo "$sv_out" | grep -oE '[0-9]+ goals passed' | grep -oE '[0-9]+')
      sv_result="PASS"
    elif [ $sv_rc -eq 142 ] || [ $sv_rc -eq 137 ]; then sv_result="TIMEOUT"
    elif echo "$sv_out" | grep -q "❌"; then sv_result="FAIL"
    else sv_result="ERROR"
    fi
  fi

  # GOTO + CBMC + cprover
  local cbmc_result="SKIP" cbmc_ok=0 cbmc_total=0
  local cp_result="SKIP" cp_ok=0 cp_total=0
  if ! $SV_ONLY; then
    local goto_out
    goto_out=$(trun "$TIMEOUT" "$STRATA_CORE_TO_GOTO" --output-dir "$work" "$core" 2>&1)
    if [ $? -ne 0 ]; then
      cbmc_result="GOTO_ERR"; cp_result="GOTO_ERR"
    else
      local symtab="$work/${bn}.symtab.json" gotojson="$work/${bn}.goto.json" gb="$work/${bn}.gb"
      if ! "$SYMTAB2GB" "$symtab" --goto-functions "$gotojson" --out "$gb" 2>/dev/null; then
        cbmc_result="SYMTAB_ERR"; cp_result="SYMTAB_ERR"
      else
        local funcs
        funcs=$("$CBMC" "$gb" --show-properties 2>&1 | grep '  line .* function ' | sed 's/.* function //' | sort -u)

        # CBMC
        local c_ok=0 c_fail=0 c_err=0
        for func in $funcs; do
          [ $((SECONDS-t0)) -ge "$TIMEOUT" ] && { c_err=$((c_err+1)); continue; }
          local out
          out=$(trun "$FUNC_TIMEOUT" "$CBMC" "$gb" --z3 --no-pointer-check --no-undefined-shift-check --function "$func" 2>&1)
          if echo "$out" | grep -q "VERIFICATION SUCCESSFUL"; then c_ok=$((c_ok+1))
          elif echo "$out" | grep -q "VERIFICATION FAILED"; then c_fail=$((c_fail+1))
          else c_err=$((c_err+1)); fi
          cbmc_total=$((cbmc_total+1))
        done
        cbmc_ok=$c_ok
        [ -z "$funcs" ] && cbmc_result="NO_PROPS" || \
        { [ $c_fail -eq 0 ] && [ $c_err -eq 0 ] && cbmc_result="PASS" || \
          { [ $c_fail -gt 0 ] && cbmc_result="FAIL" || cbmc_result="ERROR"; }; }

        # cprover
        local p_ok=0 p_fail=0 p_err=0
        for func in $funcs; do
          [ $((SECONDS-t0)) -ge "$TIMEOUT" ] && { p_err=$((p_err+1)); continue; }
          local out
          out=$(trun "$FUNC_TIMEOUT" "$CPROVER" "$gb" --no-safety --smt2-solver z3 --function "$func" 2>&1)
          if echo "$out" | grep -q "SUCCESS\|no properties"; then p_ok=$((p_ok+1))
          elif echo "$out" | grep -q "REFUTED"; then p_fail=$((p_fail+1))
          else p_err=$((p_err+1)); fi
          cp_total=$((cp_total+1))
        done
        cp_ok=$p_ok
        [ -z "$funcs" ] && cp_result="NO_PROPS" || \
        { [ $p_fail -eq 0 ] && [ $p_err -eq 0 ] && cp_result="PASS" || \
          { [ $p_fail -gt 0 ] && cp_result="FAIL" || cp_result="ERROR"; }; }
      fi
    fi
  fi

  echo "$bn,$sv_result,$sv_goals,$cbmc_result,$cbmc_ok,$cbmc_total,$cp_result,$cp_ok,$cp_total,$((SECONDS-t0)),$sz"
}
export -f eval_one trun
export STRATA_VERIFY STRATA_CORE_TO_GOTO B2S CBMC CPROVER SYMTAB2GB
export TIMEOUT FUNC_TIMEOUT MEM_KB CBMC_ONLY SV_ONLY

# Header
if ! $RESUME || [ ! -f "$RESULTS" ]; then
  echo "benchmark,sv_result,sv_goals,cbmc_result,cbmc_ok,cbmc_total,cp_result,cp_ok,cp_total,time_s,size_bytes" > "$RESULTS"
fi

# Build file list
DONE_FILE=$(mktemp)
if $RESUME && [ -f "$RESULTS" ]; then
  tail -n+2 "$RESULTS" | cut -d, -f1 > "$DONE_FILE"
  echo "Resuming: $(wc -l < "$DONE_FILE" | tr -d ' ') already done"
fi

FILE_LIST=$(mktemp)
n=0
for bpl in "$BOOGIE_DIR"/*.bpl; do
  [ -f "$bpl" ] || continue
  bn=$(basename "$bpl" .bpl)
  grep -qx "$bn" "$DONE_FILE" && continue
  if [ "$MAX_SIZE" -gt 0 ]; then
    sz=$(stat -f%z "$bpl" 2>/dev/null || stat -c%s "$bpl" 2>/dev/null)
    [ "$sz" -gt "$MAX_SIZE" ] && continue
  fi
  echo "$bpl" >> "$FILE_LIST"
  n=$((n+1))
  [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && break
done
rm -f "$DONE_FILE"

total=$(wc -l < "$FILE_LIST" | tr -d ' ')
echo "Evaluating $total benchmarks with $JOBS parallel jobs (timeout=${TIMEOUT}s, func_timeout=${FUNC_TIMEOUT}s, mem=${MEM_MB}MB)"

# Run in parallel, append results
if command -v parallel >/dev/null 2>&1; then
  parallel -j "$JOBS" --bar --halt never eval_one {} < "$FILE_LIST" >> "$RESULTS"
else
  # Fallback: xargs-based parallelism
  cat "$FILE_LIST" | xargs -P "$JOBS" -I{} bash -c 'eval_one "$@"' _ {} >> "$RESULTS"
fi
rm -f "$FILE_LIST"

# Summary
echo ""
echo "=== Results ==="
total_done=$(tail -n+2 "$RESULTS" | wc -l | tr -d ' ')
sv_pass=$(tail -n+2 "$RESULTS" | awk -F, '$2=="PASS"' | wc -l | tr -d ' ')
sv_fail=$(tail -n+2 "$RESULTS" | awk -F, '$2=="FAIL"' | wc -l | tr -d ' ')
sv_err=$(tail -n+2 "$RESULTS" | awk -F, '$2=="ERROR" || $2=="TIMEOUT"' | wc -l | tr -d ' ')
cbmc_pass=$(tail -n+2 "$RESULTS" | awk -F, '$4=="PASS"' | wc -l | tr -d ' ')
cbmc_fail=$(tail -n+2 "$RESULTS" | awk -F, '$4=="FAIL"' | wc -l | tr -d ' ')
cbmc_err=$(tail -n+2 "$RESULTS" | awk -F, '$4=="ERROR" || $4=="GOTO_ERR" || $4=="SYMTAB_ERR"' | wc -l | tr -d ' ')
cp_pass=$(tail -n+2 "$RESULTS" | awk -F, '$7=="PASS"' | wc -l | tr -d ' ')
both=$(tail -n+2 "$RESULTS" | awk -F, '$2=="PASS" && $4=="PASS"' | wc -l | tr -d ' ')
printf "Evaluated:     %s benchmarks\n" "$total_done"
printf "StrataVerify:  %s pass, %s fail, %s error/timeout\n" "$sv_pass" "$sv_fail" "$sv_err"
printf "CBMC+z3:       %s pass, %s fail, %s error\n" "$cbmc_pass" "$cbmc_fail" "$cbmc_err"
printf "cprover:       %s pass\n" "$cp_pass"
printf "Both SV+CBMC:  %s pass\n" "$both"
echo "Results: $RESULTS"
