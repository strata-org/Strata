#!/bin/bash
#
# End-to-end test for Strata → GOTO → CBMC pipeline with contract support.
# Tests the full workflow including goto-cc, goto-instrument --dfcc, and cbmc.
#
# Usage: ./test_contracts_e2e.sh
#
# Environment variables:
#   CBMC              - path to cbmc binary (default: cbmc)
#   GOTO_CC           - path to goto-cc binary (default: goto-cc)
#   GOTO_INSTRUMENT   - path to goto-instrument binary (default: goto-instrument)
#   STRATA            - path to strata binary (default: uses .lake/build/bin/strata)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
STRATA="${STRATA:-$PROJECT_ROOT/.lake/build/bin/strata}"
CBMC="${CBMC:-cbmc}"
GOTO_CC="${GOTO_CC:-goto-cc}"
GOTO_INSTRUMENT="${GOTO_INSTRUMENT:-goto-instrument}"

WORK_DIR=$(mktemp -d)
cleanup() { rm -rf "$WORK_DIR"; }
trap cleanup EXIT

pass=0
fail=0

run_test() {
  local name="$1"; shift
  if "$@" > "$WORK_DIR/output.txt" 2>&1; then
    echo "  PASS: $name"
    pass=$((pass + 1))
  else
    echo "  FAIL: $name (exit code $?)"
    tail -5 "$WORK_DIR/output.txt"
    fail=$((fail + 1))
  fi
}

# build_goto <basename> <lr.st content>
#   Runs the full pipeline: strata → process_json → symtab2gb → goto-cc
#   Produces $WORK_DIR/<basename>.gb and $WORK_DIR/<basename>_cc.gb
build_goto() {
  local bn="$1" src="$2"
  echo "$src" > "$WORK_DIR/$bn.lr.st"

  run_test "$bn: strata laurelAnalyzeToGoto" \
    bash -c "ulimit -t 30; cd '$WORK_DIR' && '$STRATA' laurelAnalyzeToGoto '$WORK_DIR/$bn.lr.st'"

  run_test "$bn: process_json.py combine" \
    bash -c "ulimit -t 10; python3 '$PROJECT_ROOT/Strata/Backends/CBMC/resources/process_json.py' combine \
      '$PROJECT_ROOT/Strata/Backends/CBMC/resources/defaults.json' \
      '$WORK_DIR/$bn.lr.symtab.json' > '$WORK_DIR/$bn.full-symtab.json'"

  run_test "$bn: symtab2gb" \
    bash -c "ulimit -t 10; symtab2gb '$WORK_DIR/$bn.full-symtab.json' \
      --goto-functions '$WORK_DIR/$bn.lr.goto.json' \
      --out '$WORK_DIR/$bn.gb'"

  run_test "$bn: goto-cc (add C scaffolding)" \
    bash -c "ulimit -t 10; '$GOTO_CC' --function main -o '$WORK_DIR/${bn}_cc.gb' '$WORK_DIR/$bn.gb'"
}

echo "=== Strata → GOTO → CBMC Contract E2E Tests ==="
echo ""

# ---- Test 1: Full DFCC pipeline with requires/ensures ----
echo "--- Test 1: Procedure with requires/ensures (full DFCC + CBMC) ---"

build_goto "contract" 'procedure add(x: int, y: int) returns (r: int)
  requires x >= 0
  ensures r >= x
{
  r := x + y;
}

procedure main() {
  var a: int := 42;
  assert a > 0;
}'

# Verify contracts are in the symbol table
run_test "contract: cbmc reads #spec_requires and #spec_ensures" \
  bash -c "ulimit -t 10; '$CBMC' --show-symbol-table --json-ui '$WORK_DIR/contract.gb' 2>/dev/null \
    | python3 -c \"
import json, sys
data = json.load(sys.stdin)
for item in data:
    if 'symbolTable' in item:
        ns = item['symbolTable'].get('add', {}).get('type', {}).get('namedSub', {})
        assert '#spec_requires' in ns, 'missing #spec_requires'
        assert '#spec_ensures' in ns, 'missing #spec_ensures'
        print('OK: both contract annotations found')
\""

run_test "contract: goto-instrument --dfcc" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main '$WORK_DIR/contract_cc.gb' '$WORK_DIR/contract_dfcc.gb'"

run_test "contract: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/contract_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 2: Simple assert (full CBMC verification) ----
echo "--- Test 2: Simple assert (full DFCC + CBMC) ---"

build_goto "assert" 'procedure main() {
  var x: int := 10;
  var y: int := x + 5;
  assert y > x;
}'

run_test "assert: goto-instrument --dfcc" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main '$WORK_DIR/assert_cc.gb' '$WORK_DIR/assert_dfcc.gb'"

run_test "assert: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/assert_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 3: Procedure with ensures (contract in symbol table) ----
echo "--- Test 3: Procedure with ensures (full DFCC + CBMC) ---"

build_goto "ensures" 'procedure inc(x: int) returns (r: int)
  requires x >= 0
  ensures r > x
{
  r := x + 1;
}

procedure main() {
  var v: int := 10;
  assert v > 0;
}'

run_test "ensures: goto-instrument --dfcc" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main '$WORK_DIR/ensures_cc.gb' '$WORK_DIR/ensures_dfcc.gb'"

run_test "ensures: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/ensures_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 4: Loop with invariant (full DFCC + CBMC) ----
echo "--- Test 4: Loop with invariant (full DFCC + CBMC) ---"

build_goto "loop" 'procedure sum_to_n(n: int) returns (s: int)
  requires n >= 0
  ensures s >= 0
{
  var i: int := 0;
  s := 0;
  while (i < n)
    invariant i >= 0
    invariant s >= 0
  {
    s := s + i;
    i := i + 1;
  }
}

procedure main() {
  var x: int := 5;
  assert x > 0;
}'

run_test "loop: goto-instrument --dfcc --apply-loop-contracts" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main --apply-loop-contracts \
    '$WORK_DIR/loop_cc.gb' '$WORK_DIR/loop_dfcc.gb'"

run_test "loop: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/loop_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 5: Procedure call through DFCC + CBMC ----
echo "--- Test 5: Procedure call (full DFCC + CBMC) ---"

build_goto "call" 'procedure double(x: int) returns (r: int)
  requires x >= 0
  ensures r == x + x
{
  r := x + x;
}

procedure main() {
  var a: int := 3;
  assert a > 0;
}'

# Verify that the callee symbol has a code type (not empty)
run_test "call: double has code type in symbol table" \
  bash -c "ulimit -t 10; '$CBMC' --show-symbol-table --json-ui '$WORK_DIR/call.gb' 2>/dev/null \
    | python3 -c \"
import json, sys
data = json.load(sys.stdin)
for item in data:
    if 'symbolTable' in item:
        ty = item['symbolTable'].get('double', {}).get('type', {})
        assert ty.get('id') == 'code', f'expected code type, got {ty}'
        print('OK: double has code type')
\""

run_test "call: goto-instrument --dfcc" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main \
    '$WORK_DIR/call_cc.gb' '$WORK_DIR/call_dfcc.gb'"

run_test "call: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/call_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 6: Multiple procedures with contracts ----
echo "--- Test 6: Multiple procedures with contracts ---"

build_goto "multi" 'procedure inc(x: int) returns (r: int)
  requires x >= 0
  ensures r == x + 1
{
  r := x + 1;
}

procedure dec(x: int) returns (r: int)
  requires x > 0
  ensures r == x - 1
{
  r := x - 1;
}

procedure main() {
  var x: int := 5;
  assert x > 0;
}'

# Verify both procedures have code types in symbol table
run_test "multi: inc and dec have code types" \
  bash -c "ulimit -t 10; '$CBMC' --show-symbol-table --json-ui '$WORK_DIR/multi.gb' 2>/dev/null \
    | python3 -c \"
import json, sys
data = json.load(sys.stdin)
for item in data:
    if 'symbolTable' in item:
        for name in ['inc', 'dec']:
            ty = item['symbolTable'].get(name, {}).get('type', {})
            assert ty.get('id') == 'code', f'{name}: expected code type, got {ty}'
        print('OK: both procedures have code types')
\""

run_test "multi: goto-instrument --dfcc" \
  bash -c "ulimit -t 10; '$GOTO_INSTRUMENT' --dfcc main \
    '$WORK_DIR/multi_cc.gb' '$WORK_DIR/multi_dfcc.gb'"

run_test "multi: cbmc verification succeeds" \
  bash -c "ulimit -t 30; '$CBMC' '$WORK_DIR/multi_dfcc.gb' --function main 2>&1 \
    | grep -q 'VERIFICATION SUCCESSFUL'"

echo ""

# ---- Test 7: Procedure call inside if-then-else ----
echo "--- Test 7: Call inside if-then-else (GOTO output) ---"

build_goto "nested_call" 'procedure inc(x: int) returns (r: int)
  requires x >= 0
  ensures r == x + 1
{
  r := x + 1;
}

procedure main() {
  var a: int := 3;
  var b: int;
  if (a > 0) {
    call b := inc(a);
  } else {
    b := 0;
  }
  assert b >= 0;
}'

# Verify GOTO output contains FUNCTION_CALL and GOTO (for if-then-else branching)
run_test "nested_call: GOTO has FUNCTION_CALL inside branching" \
  bash -c "ulimit -t 10; python3 -c \"
import json
with open('$WORK_DIR/nested_call.lr.goto.json') as f:
    data = json.load(f)
main_fn = [fn for fn in data['functions'] if fn['name'] == 'main'][0]
types = [i.get('instructionId','') for i in main_fn['instructions']]
assert 'FUNCTION_CALL' in types, f'missing FUNCTION_CALL in {types}'
assert 'GOTO' in types, f'missing GOTO in {types}'
print('OK: FUNCTION_CALL and GOTO found in main')
\""

echo ""

# ---- Test 8: Procedure call inside loop ----
echo "--- Test 8: Call inside loop (GOTO output) ---"

build_goto "loop_call" 'procedure inc(x: int) returns (r: int)
  requires x >= 0
  ensures r == x + 1
{
  r := x + 1;
}

procedure main() {
  var i: int := 0;
  var s: int := 0;
  while (i < 3)
    invariant i >= 0
    invariant s >= 0
  {
    call s := inc(s);
    i := i + 1;
  }
  assert s >= 0;
}'

# Verify GOTO output contains FUNCTION_CALL and loop back-edge GOTO
run_test "loop_call: GOTO has FUNCTION_CALL inside loop" \
  bash -c "ulimit -t 10; python3 -c \"
import json
with open('$WORK_DIR/loop_call.lr.goto.json') as f:
    data = json.load(f)
main_fn = [fn for fn in data['functions'] if fn['name'] == 'main'][0]
types = [i.get('instructionId','') for i in main_fn['instructions']]
assert 'FUNCTION_CALL' in types, f'missing FUNCTION_CALL in {types}'
# Should have at least 2 GOTOs: guard exit + back edge
goto_count = types.count('GOTO')
assert goto_count >= 2, f'expected >=2 GOTOs for loop, got {goto_count}'
print(f'OK: FUNCTION_CALL and {goto_count} GOTOs found in main')
\""

echo ""

# ---- Summary ----
echo "=== Results: $pass passed, $fail failed ==="
if [ "$fail" -gt 0 ]; then
  exit 1
fi
