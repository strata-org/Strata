#!/bin/bash
# Demo: access control contract verification via custom PySpecs.
# Usage: ./Examples/Python/acl_demo/run.sh [test_file.py]
# Default: test_acl_demo.py

set -e
cd "$(git rev-parse --show-toplevel)"

DEMO_DIR=Examples/Python/acl_demo
TEST_FILE="${1:-user_code.py}"
BASE_NAME=$(basename "$TEST_FILE" .py)

WORK="$(pwd)/Examples/tmp/acl_demo"
rm -rf "$WORK"
mkdir -p "$WORK"
SPEC_OUT="$WORK/specs"
ION_OUT="$WORK/${BASE_NAME}.python.st.ion"
mkdir -p "$SPEC_OUT"
cp "$DEMO_DIR/$TEST_FILE" "$WORK/$TEST_FILE"

echo "=== 1. Compile PySpec contracts ==="
.lake/build/bin/strata pySpecs "$DEMO_DIR" "$SPEC_OUT" \
  --module acl --module acl.AccessControl

echo ""
echo "=== 2. Translate Python to Ion ==="
(cd Tools/Python && python3 -m strata.gen py_to_strata \
  --dialect "dialects/Python.dialect.st.ion" \
  "../../$DEMO_DIR/$TEST_FILE" "$ION_OUT")

echo ""
echo "=== 3. Verify ==="
.lake/build/bin/strata pyAnalyzeLaurel \
  --check-level full \
  --dispatch acl \
  --pyspec acl \
  --spec-dir "$SPEC_OUT" \
  --hide-boilerplate \
  --trust-solver \
  --keep-all-files "$WORK" \
  "$ION_OUT" || true
