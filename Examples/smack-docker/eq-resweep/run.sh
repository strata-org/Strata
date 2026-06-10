#!/bin/bash
# EQ end-to-end re-sweep of the 16 #1331-cleared files, split-procs (fair) measure.
# DURABLE + RESUMABLE: all artifacts live under this dir (in the repo tree), NOT /tmp.
# Re-invoking resumes — already-verified procedures are skipped.
#
# Memory caution (per smt-test-memory-pressure note): single-thread Z3, bounded
# concurrency (xargs -P 4), gtimeout per proc. Serial translate already done.
#
# Usage: bash run.sh            # run/resume the SMT sweep
#        bash run.sh tally      # just recompute the tally from existing proc-out
set -u

# Derive the repo root from this script's location (.../Examples/smack-docker/eq-resweep/run.sh).
OUT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$OUT/../../.." && pwd)"
STRATA="$ROOT/.lake/build/bin/strata"
DOTNET="${DOTNET:-$(command -v dotnet || echo "$HOME/.dotnet/dotnet")}"
POST="$ROOT/Tools/BoogieToStrata/Source/bin/Debug/net8.0/BoogieToStrata.dll"
BF="$ROOT/Examples/smack-docker/boogie-files"
export Z3_NUM_THREADS=1

mkdir -p "$OUT/core-st" "$OUT/proc-out"

# ---- Stage 1: translate (idempotent) ----
translate() {
  while IFS= read -r b; do
    [ -z "$b" ] && continue
    st="$OUT/core-st/$b.core.st"
    [ -s "$st" ] && continue
    "$DOTNET" "$POST" --smack "$BF/$b.bpl" > "$st" 2> "$OUT/core-st/$b.translate.err" || rm -f "$st"
  done < "$OUT/files.txt"
}

# ---- Stage 2: enumerate procedures (idempotent) ----
enumerate() {
  : > "$OUT/proc-worklist.tsv"
  while IFS= read -r b; do
    [ -z "$b" ] && continue
    st="$OUT/core-st/$b.core.st"
    [ -s "$st" ] || continue
    grep -oE '^procedure +[A-Za-z_$][A-Za-z0-9_$.]*\(' "$st" \
      | sed -E 's/^procedure +//; s/\($//' \
      | while IFS= read -r p; do
          [ -z "$p" ] && continue
          printf '%s\t%s\n' "$b" "$p"
        done
  done < "$OUT/files.txt" >> "$OUT/proc-worklist.tsv"
}

# ---- safe per-proc output filename (hash long mangled Java names) ----
procfile() {
  local b="$1" p="$2"
  local h
  h=$(printf '%s' "$p" | shasum | cut -c1-16)
  printf '%s/proc-out/%s__%s.out' "$OUT" "$b" "$h"
}

# ---- Stage 3: verify one procedure (skips if already done) ----
verify_one() {
  local b="$1" p="$2"
  local st="$OUT/core-st/$b.core.st"
  local pf; pf=$(procfile "$b" "$p")
  # resume: skip if a COMPLETE output already exists (has ### RC: trailer)
  if [ -s "$pf" ] && grep -qE '^### RC:' "$pf"; then return 0; fi
  # memory throttle: if system free memory drops below ~12%, pause before launching
  # another strata (worst case is two 12 GB big-file procs colliding).
  local waited=0
  while :; do
    local freepct
    freepct=$(memory_pressure 2>/dev/null | awk -F: '/free percentage/{gsub(/[^0-9]/,"",$2); print $2; exit}')
    [ -z "$freepct" ] && break                 # can't read -> don't block
    [ "$freepct" -ge 12 ] && break             # enough headroom
    [ "$waited" -ge 120 ] && break             # cap the wait at 2 min, then proceed
    sleep 5; waited=$((waited+5))
  done
  # record the proc name on line 1 so analysis can recover it from the hashed filename
  printf '### PROC: %s\n### FILE: %s\n' "$p" "$b" > "$pf"
  gtimeout 60 "$STRATA" verify "$st" \
    --procedures "$p" \
    --check-mode deductive --check-level full \
    --call-policy bodyOrContract --inline-fuel 100 \
    --solver-timeout 10 >> "$pf" 2>&1
  local rc=$?
  printf '### RC: %d\n' "$rc" >> "$pf"
}
# ---- worker: process one chunk file serially ----
run_chunk() {
  local chunk="$1"
  while IFS=$'\t' read -r b p; do
    [ -z "$b" ] && continue
    verify_one "$b" "$p"
  done < "$chunk"
}

# ---- classify one proc output ----
classify() {
  local pf="$1"
  local rc; rc=$(grep -E '^### RC:' "$pf" | tail -1 | awk '{print $3}')
  if [ "$rc" = "124" ]; then echo TIMEOUT
  elif grep -qE 'file name too long' "$pf"; then echo ERR_FNAME
  elif grep -qE 'Subexpressions must have the same type' "$pf"; then echo ERR_HEAPTYPE
  elif grep -qiE 'SMT Solver Crash' "$pf"; then echo ERR_SOLVERCRASH
  elif grep -qE 'Cannot find this fvar in the context! old' "$pf"; then echo OLDFVAR_REGRESS
  elif grep -qE 'modifies variables it is not allowed' "$pf"; then echo MODIFIES_BLOCK
  elif grep -qE 'All 0 goals passed' "$pf"; then echo PASS_0
  elif grep -qE 'All [0-9]+ goals passed' "$pf"; then
    if grep -qE 'path unreachable' "$pf"; then echo PASSQ; else echo PASS; fi
  elif grep -qE 'goals passed' "$pf" && grep -qE 'failed' "$pf"; then echo PARTIAL
  elif grep -qiE 'error|exception|PANIC' "$pf"; then echo ERROR
  else echo UNKNOWN
  fi
}

# ---- Stage 4: program-level + aggregate tally ----
tally() {
  : > "$OUT/proc-results.tsv"          # file<TAB>proc<TAB>class
  : > "$OUT/program-results.tsv"       # file<TAB>nprocs<TAB>pass<TAB>passq<TAB>partial<TAB>err<TAB>to<TAB>verdict
  while IFS= read -r b; do
    [ -z "$b" ] && continue
    p_pass=0; p_passq=0; p_part=0; p_err=0; p_to=0; n=0
    while IFS=$'\t' read -r f p; do
      [ "$f" = "$b" ] || continue
      n=$((n+1))
      pf=$(procfile "$b" "$p")
      cls=$( [ -s "$pf" ] && classify "$pf" || echo MISSING )
      printf '%s\t%s\t%s\n' "$b" "$p" "$cls" >> "$OUT/proc-results.tsv"
      case "$cls" in
        PASS|PASS_0) p_pass=$((p_pass+1)) ;;
        PASSQ) p_passq=$((p_passq+1)) ;;
        PARTIAL) p_part=$((p_part+1)) ;;
        TIMEOUT) p_to=$((p_to+1)) ;;
        *) p_err=$((p_err+1)) ;;
      esac
    done < "$OUT/proc-worklist.tsv"
    if [ "$p_err" -eq 0 ] && [ "$p_to" -eq 0 ] && [ "$p_part" -eq 0 ]; then
      [ "$p_passq" -gt 0 ] && verdict=PASS-\? || verdict=PASS
    elif [ $((p_pass+p_passq)) -gt 0 ]; then verdict=PARTIAL
    elif [ "$p_to" -gt 0 ]; then verdict=TIMEOUT
    else verdict=ERROR; fi
    printf '%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s\n' "$b" "$n" "$p_pass" "$p_passq" "$p_part" "$p_err" "$p_to" "$verdict" >> "$OUT/program-results.tsv"
  done < "$OUT/files.txt"

  echo "=== PROGRAM-LEVEL (file  nprocs  pass  pass?  partial  err  timeout  verdict) ==="
  column -t -s$'\t' "$OUT/program-results.tsv"
  echo ""
  echo "=== AGGREGATE proc-level ==="
  awk -F'\t' '{c[$3]++} END{for(k in c) printf "  %-16s %d\n", k, c[k]}' "$OUT/proc-results.tsv" | sort -k2 -rn
  echo "  TOTAL procs: $(wc -l < "$OUT/proc-results.tsv" | tr -d ' ')"
  echo ""
  echo "=== #1331 REGRESSION CHECK (old-fvar) ==="
  echo "  proc-outs with old-fvar error: $(grep -lE 'Cannot find this fvar in the context! old' "$OUT"/proc-out/*.out 2>/dev/null | wc -l | tr -d ' ')  (expect 0)"
}

# ---- main ----
if [ "${1:-}" = "tally" ]; then tally; exit 0; fi

echo "[1/4] translate"; translate
echo "[2/4] enumerate"; enumerate
echo "    worklist: $(wc -l < "$OUT/proc-worklist.tsv" | tr -d ' ') procs"
echo "[3/4] verify (2 parallel workers, single-thread Z3, gtimeout 60/proc, resumable)"
# Split worklist into round-robin chunks (round-robin balances big/small files
# across workers). No xargs -> no arg-length limit on long mangled Java proc names.
# NW=2: a single 172-proc file's strata can hit ~12 GB RSS; 2-way keeps the
# worst case ~24 GB, under the documented 28.5 GB thrash threshold. (4-way risked it.)
NW=${NW_OVERRIDE:-2}
for i in $(seq 0 $((NW-1))); do : > "$OUT/chunk.$i.tsv"; done
awk -F'\t' -v nw="$NW" -v out="$OUT" '{print > (out "/chunk." (NR % nw) ".tsv")}' "$OUT/proc-worklist.tsv"
pids=()
for i in $(seq 0 $((NW-1))); do
  run_chunk "$OUT/chunk.$i.tsv" &
  pids+=($!)
done
# wait for all workers
for pid in "${pids[@]}"; do wait "$pid"; done
echo "[4/4] tally"; tally
