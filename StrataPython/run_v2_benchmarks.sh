#!/bin/bash
# Run pyAnalyzeV2 (--solver z3, bugFinding) over the StrataInternalBenchmarks corpus.
# Raw per-file output -> /tmp/v2_bench_raw.txt. Tally computed from raw via awk (bash-3.2
# safe; no `declare -A`). Usage: run_v2_benchmarks.sh [sample_per_set]  (0/empty = all).
cd "$(dirname "$0")" || exit 1
BIN=.lake/build/bin/pyAnalyzeV2
BENCH=/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/StrataInternalBenchmarks
RAW=/tmp/v2_bench_raw.txt
SAMPLE="${1:-0}"
: > "$RAW"
total=0

for set in aws_samples ecc_examples bash_party_examples service_benchmarks; do
  ions=$(find "$BENCH/$set" -name "*.python.st.ion" 2>/dev/null | sort)
  [ "$SAMPLE" -gt 0 ] 2>/dev/null && ions=$(echo "$ions" | head -"$SAMPLE")
  for ion in $ions; do
    [ -f "$ion" ] || continue
    total=$((total+1))
    out=$(timeout 90 "$BIN" --solver z3 --check-mode bugFinding --check-level full "$ion" 2>&1)
    code=$?
    echo "===== [$set] $(basename "$ion") (exit $code) =====" >> "$RAW"
    echo "$out" | grep -E '^DETAIL:|^RESULT:' | tail -2 >> "$RAW"
    [ $code -ne 0 ] && ! echo "$out" | grep -q '^RESULT:' && echo "  -> CRASH/timeout $code" >> "$RAW"
  done
done

echo ""
echo "============ pyAnalyzeV2 over StrataInternalBenchmarks (sample=$SAMPLE, total run=$total) ============"
echo "--- overall ---"
grep '^RESULT:' "$RAW" | sort | uniq -c | sort -rn
echo "crash/timeout (no RESULT): $(grep -c 'CRASH/timeout' "$RAW")"
echo "--- per set ---"
awk '/^===== \[/ { l=$0; sub(/^===== \[/,"",l); sub(/\].*/,"",l); s=l; next }
     /^RESULT:/ { r=$0; sub(/^RESULT: /,"",r); print s"\t"r }' "$RAW" | sort | uniq -c
echo "TOTAL benchmarks run: $total"
echo "Raw: $RAW"
