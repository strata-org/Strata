#!/bin/bash
# Regenerate Java roundtrip test data
set -e
cd "$(dirname "$0")"

STRATA_ROOT="$(cd ../../../.. && pwd)"
TESTDATA="testdata"
GEN_DIR="testdata/generated"
JAR="testdata/ion-java-1.11.11.jar"

# Download ion-java if needed
if [ ! -f "$JAR" ]; then
  echo "=== Downloading ion-java ==="
  curl -sLo "$JAR" "https://github.com/amazon-ion/ion-java/releases/download/v1.11.11/ion-java-1.11.11.jar"
fi

echo "=== Generating Java classes from dialect ==="
(cd "$STRATA_ROOT" && lake exe strata javaGen "$STRATA_ROOT/StrataTestExtra/DDM/Integration/Java/$TESTDATA/Simple.dialect.st" com.strata.simple "$STRATA_ROOT/StrataTestExtra/DDM/Integration/Java/$GEN_DIR")

echo "=== Compiling Java ==="
javac -cp "$JAR" $GEN_DIR/com/strata/simple/*.java $TESTDATA/GenerateTestData.java

echo "=== Generating test data ==="
java -cp "$JAR:$GEN_DIR:$TESTDATA" GenerateTestData "$TESTDATA/comprehensive.ion" "$TESTDATA/comprehensive-files.ion"

echo "=== Cleaning up ==="
rm -rf "$GEN_DIR"
rm -f $TESTDATA/*.class

echo "=== Verifying with Lean ==="
(cd "$STRATA_ROOT" && lake exe strata print --include "$STRATA_ROOT/StrataTestExtra/DDM/Integration/Java/$TESTDATA" "$STRATA_ROOT/StrataTestExtra/DDM/Integration/Java/$TESTDATA/comprehensive.ion" 2>&1 | tail -1)

echo ""
echo "Done! Regenerated $TESTDATA/comprehensive.ion and $TESTDATA/comprehensive-files.ion"
