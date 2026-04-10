#!/bin/bash

# Test that --keep-all-files emits the expected intermediate files.
# Usage: ./run_keep_all_files_test.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
STRATA="$PROJECT_ROOT/.lake/build/bin/strata"
DIALECT="$PROJECT_ROOT/Tools/Python/dialects/Python.dialect.st.ion"

[[ -x "$STRATA" ]] || { echo "strata binary not found: $STRATA"; exit 1; }

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

ION_FILE="$TMPDIR/test_arithmetic.python.st.ion"
KEEP_DIR="$TMPDIR/keep-test-output"

python3 -m strata.gen py_to_strata --dialect "$DIALECT" \
    "$SCRIPT_DIR/tests/test_arithmetic.py" "$ION_FILE"
"$STRATA" pyAnalyzeLaurel --keep-all-files "$KEEP_DIR" "$ION_FILE" > /dev/null

expected_laurel="test_arithmetic.0.Initial.laurel.st
test_arithmetic.1.Resolve.laurel.st
test_arithmetic.10.EliminateReturns.laurel.st
test_arithmetic.11.ConstrainedTypeElim.laurel.st
test_arithmetic.2.FilterNonCompositeModifies.laurel.st
test_arithmetic.3.HeapParameterization.laurel.st
test_arithmetic.4.TypeHierarchyTransform.laurel.st
test_arithmetic.5.ModifiesClausesTransform.laurel.st
test_arithmetic.6.InferHoleTypes.laurel.st
test_arithmetic.7.EliminateHoles.laurel.st
test_arithmetic.8.DesugarShortCircuit.laurel.st
test_arithmetic.9.LiftExpressionAssignments.laurel.st"

expected_core="test_arithmetic.1.FilterProcedures.core.st
test_arithmetic.2.CallElim.core.st
test_arithmetic.3.PrecondElim.core.st
test_arithmetic.4.FilterProcedures.core.st
test_arithmetic.5.LoopElim.core.st"

actual_laurel=$(ls -1 "$KEEP_DIR"/*.laurel.st 2>/dev/null | xargs -I{} basename {} | sort)
actual_core=$(ls -1 "$KEEP_DIR"/*.core.st 2>/dev/null | xargs -I{} basename {} | sort)

failed=0
if [ "$actual_laurel" != "$expected_laurel" ]; then
    echo "FAIL: Laurel intermediate files mismatch"
    diff <(echo "$expected_laurel") <(echo "$actual_laurel")
    failed=1
fi
if [ "$actual_core" != "$expected_core" ]; then
    echo "FAIL: Core intermediate files mismatch"
    diff <(echo "$expected_core") <(echo "$actual_core")
    failed=1
fi

if [ $failed -eq 1 ]; then exit 1; fi
echo "PASS: --keep-all-files test"
