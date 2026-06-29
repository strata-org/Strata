#!/bin/bash
# Run pyAnalyzeV2 over all 220 unit-test .python.st.ion files and tally RESULT lines.
# Raw per-file output goes to /tmp/v2_suite_raw.txt; this prints the tally + any
# crashes/errors so nothing is hidden.
cd "$(dirname "$0")" || exit 1
BIN=.lake/build/bin/pyAnalyzeV2
RAW=/tmp/v2_suite_raw.txt
: > "$RAW"

total=0; success=0; failures=0; inconclusive=0; usererr=0; internalerr=0; known=0; crash=0; other=0
crashed_files=""

for ion in StrataPythonTest/tests/*.python.st.ion; do
  [ -f "$ion" ] || continue
  total=$((total+1))
  base=$(basename "$ion" .python.st.ion)
  # honor per-file strata-args (e.g. bugFinding) from the paired .py, like run_py_analyze.sh
  pyf="StrataPythonTest/tests/${base}.py"
  extra=""
  [ -f "$pyf" ] && extra=$(grep '^# strata-args:' "$pyf" | sed 's/^# strata-args://' | head -1)
  out=$(timeout 180 "$BIN" --solver z3 $extra "$ion" 2>&1)
  code=$?
  echo "===== $base (exit $code) =====" >> "$RAW"
  echo "$out" >> "$RAW"
  result=$(echo "$out" | grep '^RESULT:' | tail -1)
  if [ $code -ne 0 ] && [ -z "$result" ]; then
    crash=$((crash+1)); crashed_files="$crashed_files $base(exit$code)"
    echo "  -> CRASH/timeout exit $code" >> "$RAW"
    continue
  fi
  case "$result" in
    *"Analysis success"*) success=$((success+1)) ;;
    *"Failures found"*)   failures=$((failures+1)) ;;
    *"Inconclusive"*)     inconclusive=$((inconclusive+1)) ;;
    *"User error"*)       usererr=$((usererr+1)) ;;
    *"Internal error"*)   internalerr=$((internalerr+1)) ;;
    *"Known limitation"*) known=$((known+1)) ;;
    *)                    other=$((other+1)); crashed_files="$crashed_files $base(noRESULT)" ;;
  esac
done

echo ""
echo "================ pyAnalyzeV2 over $total unit tests ================"
echo "  Analysis success : $success"
echo "  Failures found   : $failures"
echo "  Inconclusive     : $inconclusive"
echo "  User error       : $usererr"
echo "  Internal error   : $internalerr"
echo "  Known limitation : $known"
echo "  CRASH/timeout    : $crash"
echo "  No RESULT/other  : $other"
echo "  ----"
echo "  TOTAL            : $((success+failures+inconclusive+usererr+internalerr+known+crash+other)) / $total"
[ -n "$crashed_files" ] && echo "  problem files:$crashed_files"
echo "Raw output: $RAW"
