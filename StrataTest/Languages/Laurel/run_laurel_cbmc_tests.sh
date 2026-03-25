#!/bin/bash
# Run Laurel .lr.st files through GOTO + CBMC verification.
# Usage: ./run_laurel_cbmc_tests.sh [file.lr.st ...]
# If no files given, runs all .lr.st in tests/ directory.

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
STRATA="${STRATA:-$PROJECT_ROOT/.lake/build/bin/strata}"
CBMC="${CBMC:-cbmc}"
SYMTAB2GB="${SYMTAB2GB:-symtab2gb}"

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if [ $# -gt 0 ]; then
  FILES=("$@")
else
  FILES=("$SCRIPT_DIR"/tests/*.lr.st)
fi

passed=0; errors=0

for lr in "${FILES[@]}"; do
  [ -f "$lr" ] || continue
  bn=$(basename "$lr" .lr.st)
  lr_abs="$(cd "$(dirname "$lr")" && pwd)/$(basename "$lr")"

  # Step 1: Laurel → GOTO JSON (run from WORK dir so output lands there)
  if ! (cd "$WORK" && "$STRATA" laurelAnalyzeToGoto "$lr_abs") > "$WORK/${bn}.translate.log" 2>&1; then
    echo "SKIP: $bn (translation failed)"
    cat "$WORK/${bn}.translate.log"
    errors=$((errors+1)); continue
  fi

  # Step 2: symtab2gb
  "$SYMTAB2GB" "$WORK/${bn}.lr.symtab.json" \
    --goto-functions "$WORK/${bn}.lr.goto.json" \
    --out "$WORK/${bn}.gb" 2>/dev/null || {
    echo "SKIP: $bn (symtab2gb failed)"; errors=$((errors+1)); continue; }

  # Step 3: Find functions with properties and verify each
  funcs=$("$CBMC" "$WORK/${bn}.gb" --show-properties 2>&1 | \
    grep ' function ' | grep -v 'Removal of' | sed 's/.* function //' | sort -u)

  if [ -z "$funcs" ]; then
    echo "SKIP: $bn (no properties)"; errors=$((errors+1)); continue
  fi

  ok=0; fail=0; err=0; total=0
  for func in $funcs; do
    result=$("$CBMC" "$WORK/${bn}.gb" --z3 --no-pointer-check \
      --no-undefined-shift-check --function "$func" 2>&1 || true)
    total=$((total+1))
    if echo "$result" | grep -q "VERIFICATION SUCCESSFUL"; then ok=$((ok+1))
    elif echo "$result" | grep -q "VERIFICATION FAILED"; then fail=$((fail+1))
    else err=$((err+1)); fi
  done

  if [ $err -eq 0 ]; then
    echo "OK:   $bn (${ok} pass, ${fail} fail of ${total} functions)"
    passed=$((passed+1))
  else
    echo "ERR:  $bn (${ok} pass, ${fail} fail, ${err} error of ${total})"
    errors=$((errors+1))
  fi
done

echo ""
echo "Results: $passed passed, $errors errors"
exit $((errors > 0 ? 1 : 0))
