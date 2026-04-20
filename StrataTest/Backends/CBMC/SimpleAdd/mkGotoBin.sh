#!/bin/zsh

echo "Cleaning any previous artifacts"
rm -f *.json
rm -f *.gb

echo "Writing out JSON files from a Strata Core program SimpleAdd"
pushd ../../../../
lake exe StrataCoreToGoto --output-dir StrataTest/Backends/CBMC/SimpleAdd StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.core.st
popd

# The symtab.json now includes CBMC default symbols directly.
echo "Constructing a GOTO binary from the JSON files:"
symtab2gb simpleAdd.symtab.json --goto-functions simpleAdd.goto.json --out newSimpleAdd.gb

echo "Running CBMC on the GOTO binary:"

cbmc --function simpleAdd newSimpleAdd.gb
