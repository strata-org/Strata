#!/bin/zsh
lake exe StrataToCBMC test > foo.json
python3 Strata/Backends/CBMC/resources/main.py combine Strata/Backends/CBMC/resources/defaults.json foo.json > full.json
python3 Strata/Backends/CBMC/resources/main.py compare StrataTest/Backends/CBMC/simple_test_goto.json full.json


