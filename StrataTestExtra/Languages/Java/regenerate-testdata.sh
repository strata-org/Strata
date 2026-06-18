#!/bin/bash
# Regenerate Java roundtrip test data
set -e
cd "$(dirname "$0")"

STRATA_ROOT="$(cd ../../.. && pwd)"
TESTDATA="testdata"
GEN_DIR="testdata/generated"
JAR="testdata/ion-java-1.11.11.jar"


echo "=== Generating Java classes from dialect ==="
(cd "$STRATA_ROOT" && lake env lean --run Scripts/JavaGenTestData.lean javaGen "$STRATA_ROOT/StrataTestExtra/Languages/Java/$TESTDATA/Simple.dialect.st" com.strata.simple "$STRATA_ROOT/StrataTestExtra/Languages/Java/$GEN_DIR")

echo "=== Compiling Java ==="
javac -cp "$JAR" $GEN_DIR/com/strata/simple/*.java $TESTDATA/GenerateTestData.java

echo "=== Generating test data ==="
java -cp "$JAR:$GEN_DIR:$TESTDATA" GenerateTestData "$TESTDATA/comprehensive.ion" "$TESTDATA/comprehensive-files.ion"

echo "=== Cleaning up ==="
rm -rf "$GEN_DIR"
rm -f $TESTDATA/*.class

echo "=== Verifying with Lean ==="
(cd "$STRATA_ROOT" && lake env lean --run Scripts/JavaGenTestData.lean print --include "$STRATA_ROOT/StrataTestExtra/Languages/Java/$TESTDATA" "$STRATA_ROOT/StrataTestExtra/Languages/Java/$TESTDATA/comprehensive.ion" 2>&1 | tail -1)

echo ""
echo "Done! Regenerated $TESTDATA/comprehensive.ion and $TESTDATA/comprehensive-files.ion"
