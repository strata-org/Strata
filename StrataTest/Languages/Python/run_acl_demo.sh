#!/bin/bash
# Demo: access control contract verification via custom PySpecs.
# Run from the repo root: ./StrataTest/Languages/Python/run_acl_demo.sh

set -e
cd "$(git rev-parse --show-toplevel)"

SPEC_SRC=StrataTest/Languages/Python/Specs/dispatch_test
WORK="$(pwd)/Examples/tmp/acl_demo"
rm -rf "$WORK"
mkdir -p "$WORK"
SPEC_OUT="$WORK/specs"
ION_OUT="$WORK/test_acl_demo.python.st.ion"
mkdir -p "$SPEC_OUT"
cp "$SPEC_SRC/test_acl_demo.py" "$WORK/test_acl_demo.py"

echo "=== 1. Compile PySpec contracts ==="
.lake/build/bin/strata pySpecs "$SPEC_SRC" "$SPEC_OUT" \
  --module acl --module acl.AccessControl

echo ""
echo "=== 2. Translate Python to Ion ==="
(cd Tools/Python && python3 -m strata.gen py_to_strata \
  --dialect "dialects/Python.dialect.st.ion" \
  "../../$SPEC_SRC/test_acl_demo.py" "$ION_OUT")

echo ""
echo "=== 3. Verify ==="
.lake/build/bin/strata pyAnalyzeLaurel \
  --check-level full \
  --dispatch acl \
  --pyspec acl \
  --spec-dir "$SPEC_OUT" \
  --hide-boilerplate \
  --keep-all-files "$WORK" \
  "$ION_OUT" || true

echo ""
echo "=== Intermediate files ==="
ls -1 "$WORK"
