#!/bin/bash
# E2E test: property summary metadata flows from Laurel through GOTO to CBMC output.
#
# Verifies that Laurel `assert ... summary "..."` annotations appear in
# CBMC's verification output as property descriptions.

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
LAUREL_TO_CBMC="$PROJECT_ROOT/StrataTest/Languages/Laurel/laurel_to_cbmc.sh"

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# Create Laurel program with property summaries
cat > "$WORK/test.lr.st" << 'LAUREL'
procedure main()
  opaque
{
    var x: int := 5;
    var y: int := 3;
    assert x + y == 8 summary "addition equals eight";
    assert x - y == 2 summary "difference equals two"
};
LAUREL

# Run the full pipeline (strata → symtab2gb → goto-cc → goto-instrument → cbmc)
cbmc_out=$("$LAUREL_TO_CBMC" "$WORK/test.lr.st" 2>&1 || true)

# Verify CBMC output contains property summaries
for summary in "addition equals eight" "difference equals two"; do
  if echo "$cbmc_out" | grep -q "$summary"; then
    echo "CBMC output: '$summary' found"
  else
    echo "FAIL: '$summary' not in CBMC output"
    echo "$cbmc_out"
    exit 1
  fi
done

# Verify CBMC says SUCCESSFUL
if echo "$cbmc_out" | grep -q "VERIFICATION SUCCESSFUL"; then
  echo "CBMC: VERIFICATION SUCCESSFUL"
else
  echo "FAIL: CBMC did not report VERIFICATION SUCCESSFUL"
  echo "$cbmc_out"
  exit 1
fi

echo "PASS: property summaries flow end-to-end from Laurel to CBMC"
