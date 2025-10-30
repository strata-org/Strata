#!/bin/bash
# Complete pipeline for testing single TypeScript file with debug output
# Usage: ./test_single_file.sh <path_to_ts_file>

set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 <path_to_ts_file>"
  echo "Example: $0 StrataTest/Languages/TypeScript/test_debug_break.ts"
  exit 1
fi

TS_FILE="$1"
BASE_NAME=$(basename "$TS_FILE" .ts)
AST_FILE="${BASE_NAME}_ast.json"
LEAN_FILE="${BASE_NAME}_lean.json"

echo "🔍 Testing TypeScript file: $TS_FILE"
echo "📁 Working directory: $(pwd)"
echo ""

echo "Step 1: Converting TypeScript to AST JSON..."
node conformance_testing/js_to_ast.js "$TS_FILE" > "$AST_FILE"
echo "✅ Generated: $AST_FILE"

echo ""
echo "Step 2: Converting AST JSON to Lean-compatible JSON..."
python3 conformance_testing/babel_to_lean.py "$AST_FILE" > "$LEAN_FILE"
echo "✅ Generated: $LEAN_FILE"

echo ""
echo "Step 3: Running through StrataTypeScriptRunner with debug output..."
echo "🔍 Debug output:"
echo "----------------------------------------"

# Run with debug output and capture both stdout and stderr
lake exe StrataTypeScriptRunner "$LEAN_FILE" 2>&1 | grep "DEBUG" || echo "No DEBUG output found"

echo "----------------------------------------"
echo ""
echo "Step 4: Final execution result..."
lake exe StrataTypeScriptRunner "$LEAN_FILE" 2>&1 | tail -1

echo ""
echo "🧹 Cleaning up temporary files..."
rm -f "$AST_FILE" "$LEAN_FILE"
echo "✅ Cleanup complete"

echo ""
echo "🎯 Pipeline complete!"
