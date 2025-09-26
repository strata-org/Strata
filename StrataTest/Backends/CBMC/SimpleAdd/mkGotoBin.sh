#!/bin/zsh

echo "Cleaning any previous artifacts:"
rm -f *.json
rm -f *.gb

echo "Writing out JSON files from a Strata.Boogie program SimpleAdd"
pushd ../../../../
lake exe BoogieToGoto writeFiles
popd

# Merge generated file ../simpleAdd.symtab.json with symtab_cprover_intrinsics.json.
jq -s '.[0].symbolTable += .[1] | .[0]' ../symtab_cprover_intrinsics.json simpleAdd.symtab.json > simpleAdd.symtab.full.json

ls -l *.json

echo "Constructing a GOTO binary from the JSON files:"
symtab2gb simpleAdd.symtab.full.json --goto-functions simpleAdd.goto.json --out newSimpleAdd.gb

echo "Running CBMC on the GOTO binary:"

cbmc --function simpleAdd newSimpleAdd.gb
