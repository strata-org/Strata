#!/bin/bash
#
# Runs every CBMC test suite (the SUITES array below). Exit code 0 when every
# suite passes, otherwise the number of failed suites.
#
# Requires cbmc, goto-cc, goto-instrument, symtab2gb and z3 on PATH, and
# `lake build strataLaurel laurelToCBMC` done.
#
# With CBMC_TESTS_SKIP_IF_MISSING=1, exit 0 with a SKIP notice when any of
# those tools is not on PATH.
#
# Usage: StrataTest/Backends/CBMC/run_cbmc_tests.sh

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$PROJECT_ROOT"

for tool in cbmc goto-cc goto-instrument symtab2gb z3; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    if [ "${CBMC_TESTS_SKIP_IF_MISSING:-0}" = "1" ]; then
      echo "SKIP: CBMC tests ($tool not on PATH)"
      exit 0
    fi
    echo "ERROR: $tool not on PATH" >&2
    exit 1
  fi
done

echo "cbmc: $(command -v cbmc) ($(cbmc --version))"
echo "z3:   $(command -v z3) ($(z3 --version))"

# To add a test, add it to one of these suites or add a suite here.
SUITES=(
  "StrataLaurel/Tests/CBMC/run_laurel_cbmc_tests.sh"
  "StrataTest/Backends/CBMC/GOTO/test_property_summary_e2e.sh"
  "StrataTest/Backends/CBMC/contracts/test_contracts_e2e.sh"
)

failed=0
for suite in "${SUITES[@]}"; do
  echo
  echo "=== $suite"
  if bash "$suite"; then
    echo "=== PASS: $suite"
  else
    echo "=== FAIL: $suite (exit $?)"
    failed=$((failed + 1))
  fi
done

echo
echo "CBMC tests: ${#SUITES[@]} suites, $failed failed"
exit "$failed"
