#!/bin/bash
# Differential harness: run BOTH pyAnalyzeV2 (the port) and pyAnalyzeLaurel (proven
# oracle) on all 220 unit tests with the SAME flags, and compare the RESULT line.
# The honest correctness metric for the port is: does v2 match the oracle?
cd "$(dirname "$0")" || exit 1
V2=.lake/build/bin/pyAnalyzeV2
PAL=.lake/build/bin/pyAnalyzeLaurel
RAW=/tmp/v2_diff_raw.txt
: > "$RAW"

match=0; mismatch=0; both_err=0; total=0
mismatch_files=""

for ion in StrataPythonTest/tests/*.python.st.ion; do
  [ -f "$ion" ] || continue
  total=$((total+1))
  base=$(basename "$ion" .python.st.ion)
  pyf="StrataPythonTest/tests/${base}.py"
  extra=""
  [ -f "$pyf" ] && extra=$(grep '^# strata-args:' "$pyf" | sed 's/^# strata-args://' | head -1)

  v2out=$(timeout 180 "$V2"  --solver z3 $extra "$ion" 2>&1)
  palout=$(timeout 180 "$PAL" --solver z3 $extra "$ion" 2>&1)
  v2r=$(echo "$v2out"  | grep '^RESULT:' | tail -1)
  palr=$(echo "$palout" | grep '^RESULT:' | tail -1)
  # also compare the DETAIL pass/fail/inconclusive tally when both are "Analysis"/"Inconclusive"
  v2d=$(echo "$v2out"  | grep '^DETAIL:' | tail -1)
  pald=$(echo "$palout" | grep '^DETAIL:' | tail -1)

  echo "===== $base =====" >> "$RAW"
  echo "  v2 : $v2r | $v2d"  >> "$RAW"
  echo "  pal: $palr | $pald" >> "$RAW"

  if [ "$v2r" == "$palr" ] && [ "$v2d" == "$pald" ]; then
    match=$((match+1))
  elif echo "$v2r" | grep -q "Internal error" && echo "$palr" | grep -q "Internal error"; then
    both_err=$((both_err+1))
    echo "  -> BOTH internal error" >> "$RAW"
  else
    mismatch=$((mismatch+1)); mismatch_files="$mismatch_files $base"
    echo "  -> MISMATCH" >> "$RAW"
  fi
done

echo ""
echo "============ pyAnalyzeV2 vs pyAnalyzeLaurel (oracle) over $total tests ============"
echo "  EXACT MATCH (result+detail) : $match"
echo "  both internal error         : $both_err"
echo "  MISMATCH                    : $mismatch"
echo "  ----"
echo "  agreement: $((match+both_err)) / $total"
[ -n "$mismatch_files" ] && echo "  mismatch files:$mismatch_files"
echo "Raw: $RAW"
