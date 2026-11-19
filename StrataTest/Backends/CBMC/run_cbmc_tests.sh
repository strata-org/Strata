#!/bin/bash
#
# Runs every CBMC test suite (the SUITES array below). Exit code 0 when every
# suite passes, otherwise the number of failed suites.
#
# Requires cbmc, goto-cc, goto-instrument, symtab2gb and z3 on PATH, and
# `lake build strataLaurel laurelToCBMC` done. The cbmc on PATH must be the
# version named in patches/CBMC_VERSION (see README.md).
#
# With CBMC_TESTS_SKIP_IF_MISSING=1, exit 0 with a SKIP notice when any of
# those tools is not on PATH or cbmc is not the expected version.
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

# The CBMC version required by every test environment.
expected_cbmc="$(sed 's/^cbmc-//' "$SCRIPT_DIR/patches/CBMC_VERSION")"
actual_cbmc="$(cbmc --version | awk 'NR == 1 { print $1 }')"
if [ "$actual_cbmc" != "$expected_cbmc" ]; then
  if [ "${CBMC_TESTS_SKIP_IF_MISSING:-0}" = "1" ]; then
    echo "SKIP: CBMC tests (cbmc is $actual_cbmc, patches/CBMC_VERSION expects $expected_cbmc)"
    exit 0
  fi
  echo "ERROR: cbmc is $actual_cbmc, but $SCRIPT_DIR/patches/CBMC_VERSION expects $expected_cbmc" >&2
  exit 1
fi

# To add a test, add it to one of these suites or add a suite here.
SUITES=(
  "StrataLaurel/Tests/CBMC/run_laurel_cbmc_tests.sh"
  "StrataTest/Backends/CBMC/GOTO/test_property_summary_e2e.sh"
  "StrataTest/Backends/CBMC/GOTO/test_structs_globals_e2e.sh"
  "StrataTest/Backends/CBMC/contracts/test_contracts_e2e.sh"
)

failed=0
for suite in "${SUITES[@]}"; do
  echo
  echo "=== $suite"
  start=$SECONDS
  if bash "$suite"; then
    echo "=== PASS: $suite ($((SECONDS - start)) s)"
  else
    echo "=== FAIL: $suite (exit $?, $((SECONDS - start)) s)"
    failed=$((failed + 1))
  fi
done

echo
echo "CBMC tests: ${#SUITES[@]} suites, $failed failed"
exit "$failed"
