#!/bin/zsh

# To run this script, define `CBMC_DIR`. E.g.,
#`export CBMC_DIR=$HOME/Development/cbmc/build/bin/`

lake exe StrataToCBMC $1 > foo.json
python3 Strata/Backends/CBMC/resources/process_json.py combine Strata/Backends/CBMC/resources/defaults.json foo.json > full.json

$CBMC_DIR/symtab2gb full.json --out full.goto


$CBMC_DIR/goto-harness --function simpleTest --harness-function-name harness --harness-type call-function full.goto b.out
$CBMC_DIR/goto-cc b.out --function harness -o c.out
$CBMC_DIR/goto-instrument --dfcc harness --enforce-contract simpleTest c.out d.out
$CBMC_DIR/cbmc d.out

rm foo.json full.json full.goto b.out c.out d.out
