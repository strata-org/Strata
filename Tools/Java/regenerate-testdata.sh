#!/bin/bash
# Regenerate Java roundtrip test data
set -e
cd "$(dirname "$0")"

STRATA_ROOT="$(cd ../.. && pwd)"
TESTDATA="$STRATA_ROOT/StrataTest/DDM/Integration/Java/testdata"
GEN_DIR="src/main/java/com/strata/simple"
JAR="ion-java-1.11.9.jar"

# Download ion-java if needed
if [ ! -f "$JAR" ]; then
  echo "=== Downloading ion-java ==="
  curl -sLO "https://repo1.maven.org/maven2/com/amazon/ion/ion-java/1.11.9/$JAR"
fi

echo "=== Generating Java classes from dialect ==="
(cd "$STRATA_ROOT" && lake exe strata javaGen "$TESTDATA/Simple.dialect.st" com.strata.simple "$STRATA_ROOT/Tools/Java/src/main/java")

echo "=== Compiling Java ==="
javac -cp "$JAR" $GEN_DIR/*.java src/main/java/com/strata/test/*.java

echo "=== Generating test data ==="
java -cp "$JAR:src/main/java" com.strata.test.GenerateTestData "$TESTDATA/comprehensive.ion"

echo "=== Cleaning up ==="
rm -rf "$GEN_DIR"
rm -f src/main/java/com/strata/test/*.class

echo "=== Verifying with Lean ==="
(cd "$STRATA_ROOT" && lake exe strata print --include "$TESTDATA" "$TESTDATA/comprehensive.ion" 2>&1 | tail -1)

echo ""
echo "Done! Regenerated $TESTDATA/comprehensive.ion and $TESTDATA/comprehensive-files.ion"
