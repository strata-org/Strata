#!/bin/bash
set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 input.js"
  exit 1
fi
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
input_js="$1"
base_name="$(basename "$input_js" .js)"
output_json="${base_name}.json"
output_lean_json="${base_name}_lean.json"

echo "Converting $input_js to $output_json..."
node $script_dir/js_to_ast.js "$input_js" > "$script_dir/$output_json"  # Replace with your actual conversion command
echo "Processing $output_json..."
python3 $script_dir/babel_to_lean.py $script_dir/$output_json > $script_dir/$output_lean_json
#lake exe MIDI_Dyn_TS_to_HOMIDI $script_dir/$output_lean_json
lake_output=$(lake exe MIDI_Dyn_TS_to_HOMIDI $script_dir/$output_lean_json 2>&1)


if [[ "$lake_output" == *"assertion_0 verified"* ]] && [[ "$lake_output" != *"PANIC"* ]]; then
    echo "Conformance test passed!"
else
    echo "Conformance test failed!"
fi
echo "%s\n" "$lake_output"
rm $script_dir/$output_json
rm $script_dir/$output_lean_json
# Example commands
#jq '.someField' "$output_json"
