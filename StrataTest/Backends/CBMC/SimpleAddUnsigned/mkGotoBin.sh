#!/bin/zsh

pushd ../../../../
lake exe BoogieToGoto writeFile
popd

function_file=$(cat ./function.json)
jq --argjson func "$function_file" '.functions += [$func]' simple.goto_scaffold.json > simple.goto_functions.json
echo "Wrote simple.goto_functions.json"

echo "Constructing a GOTO binary..."
~/Code/cbmc/build/bin/write_goto_example

# echo "Running CBMC"
# cbmc simple.recons.gb
