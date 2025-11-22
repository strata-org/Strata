#!/bin/bash

# To run this script, define `CBMC_DIR`. E.g.,
#`export CBMC_DIR=$HOME/Development/cbmc/build/bin/`

lake exe StrataToCBMC $1 > foo.json
python3 Strata/Backends/CBMC/resources/process_json.py combine Strata/Backends/CBMC/resources/defaults.json foo.json > full.json

$CBMC_DIR/symtab2gb full.json --out full.goto
$CBMC_DIR/goto-instrument --enforce-contract simpleTest full.goto full_checking.goto
OUTPUT=$($CBMC_DIR/cbmc full_checking.goto --function simpleTest --trace)
echo "$OUTPUT"

if [[ "$OUTPUT" == *"VERIFICATION SUCCESSFUL" ]]; then
    EXIT_CODE=0
else
    EXIT_CODE=1
fi

rm foo.json full.json full.goto full_checking.goto
exit $EXIT_CODE