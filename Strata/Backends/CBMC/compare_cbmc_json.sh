#!/bin/zsh

# This is useful if e.g., you ask Claude to refactor your code and want it to test the refactoring doesn't change the test file.

lake exe StrataToCBMC Strata/Backends/CBMC/tests/simpleTest.csimp.st > foo.json
python3 Strata/Backends/CBMC/resources/process_json.py combine Strata/Backends/CBMC/resources/defaults.json foo.json > full.json
python3 Strata/Backends/CBMC/resources/process_json.py compare StrataTest/Backends/CBMC/simple_test_goto.json full.json

rm foo.json full.json