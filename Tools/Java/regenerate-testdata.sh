#!/bin/bash
# Regenerate Java roundtrip test data
set -e
cd "$(dirname "$0")"

STRATA_ROOT="$(cd ../.. && pwd)"
TESTDATA="$STRATA_ROOT/StrataTest/DDM/Integration/Java/testdata"
GEN_DIR="src/main/java/com/strata/simple"

echo "=== Generating Java classes from dialect ==="
(cd "$STRATA_ROOT" && lake exe strata javaGen "$TESTDATA/Simple.dialect.st" com.strata.simple "$STRATA_ROOT/Tools/Java/src/main/java")

echo "=== Building and running test data generator ==="
./gradlew run -PmainClass=com.strata.test.GenerateTestData --args="$TESTDATA/comprehensive.ion" --quiet

echo "=== Cleaning up generated classes ==="
rm -rf "$GEN_DIR"

echo "=== Verifying with Lean ==="
(cd "$STRATA_ROOT" && lake exe strata print --include "$TESTDATA" "$TESTDATA/comprehensive.ion" 2>&1 | tail -1)

echo ""
echo "Done! Regenerated $TESTDATA/comprehensive.ion"
