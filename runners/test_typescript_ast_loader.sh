#!/bin/bash
set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 input.ts"
  echo "Tests if a TypeScript file can be converted to AST and loaded into Strata structures"
  exit 1
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
input_ts="$1"
base_name="$(basename "$input_ts" .ts)"
output_json="${base_name}.json"
output_lean_json="${base_name}_lean.json"

echo "=== Testing TypeScript AST Loading Pipeline ==="
echo "Input: $input_ts"
echo

# Step 1: Convert TypeScript to standard AST JSON
echo "Step 1: Converting TypeScript to AST JSON..."
if node "$script_dir/js_to_ast.js" "$input_ts" > "$script_dir/$output_json"; then
    echo "✅ TypeScript to AST conversion succeeded"
    echo "Generated: $script_dir/$output_json"
else
    echo "❌ TypeScript to AST conversion failed"
    exit 1
fi
echo

# Step 2: Convert standard AST to Strata-compatible AST
echo "Step 2: Converting AST to Strata-compatible format..."
if python3 "$script_dir/babel_to_lean.py" "$script_dir/$output_json" > "$script_dir/$output_lean_json"; then
    echo "✅ AST to Strata format conversion succeeded"
    echo "Generated: $script_dir/$output_lean_json"
    echo "Preview of Strata-compatible AST:"
    head -20 "$script_dir/$output_lean_json"
    echo "..."
else
    echo "❌ AST to Strata format conversion failed"
    exit 1
fi
echo

# Step 3: Test Strata AST loading
echo "Step 3: Testing Strata AST loading..."
cd "$script_dir/.."  # Go to Strata project root
if lake exe StrataTypeScriptASTLoader "$script_dir/$output_lean_json"; then
    echo "✅ Strata AST loading succeeded"
else
    echo "❌ Strata AST loading failed"
    echo "This means the Strata-compatible AST cannot be loaded into Lean structures"
fi

# Cleanup
echo
echo "Cleaning up temporary files..."
rm -f "$script_dir/$output_json"
rm -f "$script_dir/$output_lean_json"
echo "Done!"
