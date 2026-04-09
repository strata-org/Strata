#!/bin/bash
# Demo: access control contract verification via custom PySpecs.
# Run from the repo root: ./Examples/Python/acl_demo/run.sh

set -e
cd "$(git rev-parse --show-toplevel)"

DEMO_DIR=Examples/Python/acl_demo
WORK="$(pwd)/Examples/tmp/acl_demo"
rm -rf "$WORK"
mkdir -p "$WORK"
SPEC_OUT="$WORK/specs"
ION_OUT="$WORK/test_acl_demo.python.st.ion"
mkdir -p "$SPEC_OUT"
cp "$DEMO_DIR/test_acl_demo.py" "$WORK/test_acl_demo.py"

echo "=== 1. Compile PySpec contracts ==="
.lake/build/bin/strata pySpecs "$DEMO_DIR" "$SPEC_OUT" \
  --module acl --module acl.AccessControl

echo ""
echo "=== 2. Translate Python to Ion ==="
(cd Tools/Python && python3 -m strata.gen py_to_strata \
  --dialect "dialects/Python.dialect.st.ion" \
  "../../$DEMO_DIR/test_acl_demo.py" "$ION_OUT")

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
