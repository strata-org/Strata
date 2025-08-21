#!/bin/bash
set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 input.py"
  exit 1
fi
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
input_py="$1"
base_name="$(basename "$input_py" .py)"
output_json="${base_name}.json"
output_lean_json="${base_name}_lean.json"

python3 $script_dir/python_to_ast.py "$input_py" > "$script_dir/$output_json"  # Replace with your actual conversion command
python3 $script_dir/python_ast_to_lean.py $script_dir/$output_json > $script_dir/$output_lean_json
lake --dir /Users/mzwangg/Strata exe StrataPythonRunner $script_dir/$output_lean_json


rm $script_dir/$output_json
rm $script_dir/$output_lean_json
# Example commands
#jq '.someField' "$output_json"
