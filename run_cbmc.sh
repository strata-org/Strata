#!/bin/zsh

# To run this script, define `CBMC_DIR`. E.g.,
#`export CBMC_DIR=$HOME/Development/cbmc/build/bin/`


lake exe StrataToCBMC test > foo.json
python3 Strata/Backends/CBMC/resources/process_json.py combine Strata/Backends/CBMC/resources/defaults.json foo.json > full.json
python3 Strata/Backends/CBMC/resources/process_json.py compare StrataTest/Backends/CBMC/simple_test_goto.json full.json

$CBMC_DIR/symtab2gb full.json --out full.goto
$CBMC_DIR/goto-instrument --enforce-contract simpleTest full.goto full_checking.goto
$CBMC_DIR/cbmc full_checking.goto --function simpleTest --trace


rm foo.json full.json full.goto full_checking.goto