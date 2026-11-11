#!/bin/bash
#
# Translate one Laurel .lr.st file through the Strata pipeline to CBMC verification.
# Usage: ./laurel_to_cbmc.sh <file.lr.st>
#
# Thin wrapper around the compiled `laurelToCBMC` executable
# (StrataLaurel/Scripts/LaurelToCBMC.lean). run_laurel_cbmc_tests.sh runs the
# same pipeline interpreted (`lake env lean --run`), not through this wrapper.
# The pipeline inlines procedures into `main` before emitting GOTO, then runs
# symtab2gb, goto-cc, goto-instrument --dfcc and cbmc --z3.
#
# The previous version of this script drove `strataLaurel laurelAnalyzeToGoto`
# directly. That route emits the whole Laurel prelude as GOTO functions and
# `goto-instrument --dfcc` aborts on them (to_code_type precondition); it is
# exercised by StrataTest/Backends/CBMC/contracts/test_contracts_e2e.sh instead.
#
# Environment variables (passed through to the Lean pipeline):
#   CBMC              - path to cbmc binary (default: cbmc)
#   GOTO_CC           - path to goto-cc binary (default: goto-cc)
#   GOTO_INSTRUMENT   - path to goto-instrument binary (default: goto-instrument)
#   CBMC_ARGS         - extra arguments appended to the cbmc invocation

set -euo pipefail

if [ -z "${1:-}" ]; then
  echo "Usage: $0 <file.lr.st>" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
LAUREL="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

cd "$PROJECT_ROOT"
exec lake exe laurelToCBMC "$LAUREL"
