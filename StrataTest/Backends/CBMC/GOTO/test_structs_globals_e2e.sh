#!/bin/bash
# E2E test: hand-built GOTO with structs, pointers, a global, a
# struct-returning call and sized arrays
# (StrataTest/Backends/CBMC/GOTO/E2E_StructsGlobals.lean) goes through
# symtab2gb and cbmc with the expected verdict per assertion, and CBMC's bounds
# check accepts the array reads inside the bounds and rejects the ones outside.
#
# Requires symtab2gb and cbmc on PATH; prints SKIP and exits 0 without them.

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
MODULE="StrataTest.Backends.CBMC.GOTO.E2E_StructsGlobals"

for tool in symtab2gb cbmc; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "SKIP: $MODULE ($tool not on PATH)"
    exit 0
  fi
done

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

lake -d "$PROJECT_ROOT" build "$MODULE" >/dev/null

cat > "$WORK/Driver.lean" << EOF
import $MODULE
def main (args : List String) : IO Unit :=
  CProverGOTO.E2E_StructsGlobals.writeFiles args[0]!
EOF
lake -d "$PROJECT_ROOT" env lean --run "$WORK/Driver.lean" "$WORK"

symtab2gb "$WORK/symtab.json" --goto-functions "$WORK/goto.json" --out "$WORK/e2e.gb"
main_out=$(cbmc "$WORK/e2e.gb" --function main --no-standard-checks \
  --validate-goto-model 2>&1 || true)
# The `arrays` entry, with CBMC's own bounds check on: it compares each index
# with the array's size as CBMC read it.
bounds_out=$(cbmc "$WORK/e2e.gb" --function arrays --no-standard-checks --bounds-check \
  --validate-goto-model 2>&1 || true)

fail=0
# check <cbmc output> <property description> <verdict>
check() {
  local out="$1" description="$2" verdict="$3"
  if echo "$out" | grep -qF -- "$description: $verdict"; then
    echo "CBMC: '$description' $verdict"
  else
    echo "FAIL: expected '$description: $verdict'"
    fail=1
  fi
}
# no_failure <cbmc output> <array access>: no bounds check on the access fails
# (a check on a constant index inside the bounds leaves no property at all).
no_failure() {
  local out="$1" access="$2"
  if echo "$out" | grep -F -- " in $access: " | grep -q FAILURE; then
    echo "FAIL: a bounds check on $access fails"
    fail=1
  else
    echo "CBMC: no bounds check on $access fails"
  fi
}

check "$main_out" "g is 0 on entry" SUCCESS
check "$main_out" "p->a is 3" SUCCESS
check "$main_out" "p->a is 4" FAILURE
check "$main_out" "get_g returns 5" SUCCESS
check "$main_out" "mk(7).y is 8" SUCCESS

# a : unsignedbv 32[10], indexed with signedbv 64; its size is written as `A`.
check "$bounds_out" "array 'a' lower bound in a[i9]" SUCCESS
check "$bounds_out" "array 'a' upper bound in a[i9]" SUCCESS
check "$bounds_out" "array 'a' upper bound in a[i10]" FAILURE
# b : unsignedbv 32[10], indexed with integer; its size is written as `10`.
no_failure "$bounds_out" "b[9]"
check "$bounds_out" "array 'b' upper bound in b[10]" FAILURE
# c : unsignedbv 32[infinity]: no upper bound, a negative index still fails.
no_failure "$bounds_out" "c[9]"
check "$bounds_out" "array 'c' lower bound in c[-1]" FAILURE

if [ "$fail" -ne 0 ]; then
  echo "$main_out"
  echo "$bounds_out"
  exit 1
fi
echo "PASS: structs, globals, struct-typed call results and sized arrays through CBMC"
