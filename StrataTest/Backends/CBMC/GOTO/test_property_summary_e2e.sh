#!/bin/bash
# E2E test: property summary metadata flows from Laurel through GOTO to CBMC output.
#
# Verifies that Laurel `assert ... summary "..."` annotations appear in
# CBMC's verification output as property descriptions.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
STRATA="$PROJECT_ROOT/.lake/build/bin/strata"
CBMC=${CBMC:-cbmc}
SYMTAB2GB=${SYMTAB2GB:-symtab2gb}

WORK=$(mktemp -d)
trap "rm -rf $WORK" EXIT

# Step 1: Create Laurel program with property summaries
cat > "$WORK/test.lr.st" << 'LAUREL'
procedure main() {
    var x: int := 5;
    var y: int := 3;
    assert x + y == 8 summary "addition equals eight";
    assert x - y == 2 summary "difference equals two"
};
LAUREL

# Step 2: Translate to GOTO
cd "$WORK"
"$STRATA" laurelAnalyzeToGoto test.lr.st 2>&1 | grep -q "Written"

# Step 3: Verify GOTO JSON contains property summaries
python3 -c "
import json, sys
with open('test.lr.goto.json') as f:
    data = json.load(f)
summaries = []
for fn in data['functions']:
    for inst in fn['instructions']:
        if inst.get('instructionId') == 'ASSERT':
            summaries.append(inst.get('sourceLocation', {}).get('comment', ''))
assert 'addition equals eight' in summaries, f'Missing summary in GOTO JSON: {summaries}'
assert 'difference equals two' in summaries, f'Missing summary in GOTO JSON: {summaries}'
print('GOTO JSON: property summaries present')
"

# Step 4: Wrap symtab and add CBMC default symbols
python3 -c "
import json
with open('test.lr.symtab.json') as f:
    data = json.load(f)
# Add minimal __CPROVER_initialize symbol required by CBMC
data['__CPROVER_initialize'] = {
    'baseName': '__CPROVER_initialize',
    'mode': 'C',
    'module': '',
    'name': '__CPROVER_initialize',
    'prettyName': '__CPROVER_initialize',
    'type': {'id': 'code', 'namedSub': {'parameters': {'sub': []}, 'return_type': {'id': 'empty'}}},
    'value': {'id': 'nil'}
}
data['__CPROVER_rounding_mode'] = {
    'baseName': '__CPROVER_rounding_mode',
    'isLvalue': True,
    'isStaticLifetime': True,
    'isStateVar': True,
    'mode': 'C',
    'module': '',
    'name': '__CPROVER_rounding_mode',
    'prettyName': '__CPROVER_rounding_mode',
    'type': {'id': 'signedbv', 'namedSub': {'width': {'id': '32'}}},
    'value': {'id': 'nil'}
}
with open('wrapped.symtab.json', 'w') as f:
    json.dump({'symbolTable': data}, f)
"

# Step 5: Convert to GOTO binary and run CBMC
"$SYMTAB2GB" wrapped.symtab.json --goto-functions test.lr.goto.json --out test.gb 2>/dev/null

cbmc_out=$("$CBMC" test.gb --z3 --no-pointer-check --function main 2>&1 || true)

# Step 6: Verify CBMC output contains property summaries
if echo "$cbmc_out" | grep -q "addition equals eight"; then
  echo "CBMC output: 'addition equals eight' found"
else
  echo "FAIL: 'addition equals eight' not in CBMC output"
  echo "$cbmc_out"
  exit 1
fi

if echo "$cbmc_out" | grep -q "difference equals two"; then
  echo "CBMC output: 'difference equals two' found"
else
  echo "FAIL: 'difference equals two' not in CBMC output"
  echo "$cbmc_out"
  exit 1
fi

# Step 7: Verify CBMC says SUCCESSFUL
if echo "$cbmc_out" | grep -q "VERIFICATION SUCCESSFUL"; then
  echo "CBMC: VERIFICATION SUCCESSFUL"
else
  echo "FAIL: CBMC did not report VERIFICATION SUCCESSFUL"
  echo "$cbmc_out"
  exit 1
fi

echo "PASS: property summaries flow end-to-end from Laurel to CBMC"
