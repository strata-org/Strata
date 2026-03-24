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
PYTHON="${PYTHON:-python3}"

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
  if ! (cd "$WORK" && "$STRATA" laurelAnalyzeToGoto "$lr_abs") >/dev/null 2>&1; then
    echo "SKIP: $bn (translation failed)"; errors=$((errors+1)); continue
  fi

  # Step 2: Wrap symtab for symtab2gb
  "$PYTHON" -c "
import json, sys
with open('$WORK/${bn}.lr.symtab.json') as f: data = json.load(f)
data['__CPROVER_initialize'] = {'baseName':'__CPROVER_initialize','mode':'C','module':'','name':'__CPROVER_initialize','prettyName':'__CPROVER_initialize','type':{'id':'code','namedSub':{'parameters':{'sub':[]},'return_type':{'id':'empty'}}},'value':{'id':'nil'}}
data['__CPROVER_rounding_mode'] = {'baseName':'__CPROVER_rounding_mode','isLvalue':True,'isStaticLifetime':True,'isStateVar':True,'mode':'C','module':'','name':'__CPROVER_rounding_mode','prettyName':'__CPROVER_rounding_mode','type':{'id':'signedbv','namedSub':{'width':{'id':'32'}}},'value':{'id':'nil'}}
with open('$WORK/${bn}.wrapped.json','w') as f: json.dump({'symbolTable':data},f)
" || { echo "SKIP: $bn (wrap failed)"; errors=$((errors+1)); continue; }

  # Step 3: symtab2gb
  "$SYMTAB2GB" "$WORK/${bn}.wrapped.json" \
    --goto-functions "$WORK/${bn}.lr.goto.json" \
    --out "$WORK/${bn}.gb" 2>/dev/null || {
    echo "SKIP: $bn (symtab2gb failed)"; errors=$((errors+1)); continue; }

  # Step 4: Find functions with properties and verify each
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
