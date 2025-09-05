#!/bin/bash
set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 input.ts"
  exit 1
fi
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
input_ts="$1"
base_name="$(basename "$input_ts" .ts)"
output_json="${base_name}.json"
output_lean_json="${base_name}_lean.json"

node $script_dir/js_to_ast.js "$input_ts" > "$script_dir/$output_json"
python3 $script_dir/babel_to_lean.py $script_dir/$output_json > $script_dir/$output_lean_json
lake --dir /Users/mzwangg/Strata exe TypeScriptUninitializedFieldAccess $script_dir/$output_lean_json

rm $script_dir/$output_json
rm $script_dir/$output_lean_json
