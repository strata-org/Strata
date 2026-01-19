echo "Running all Strata-CBMC related tests..."

echo "######################################################################"
echo "First: tests for the C-like AST interface."

pushd ../../../

echo "Strata Core -> CBMC: illustrates verification fail."
echo "----------------------------------------------------------------------"
Strata/Backends/CBMC/run_strata_cbmc.sh Strata/Backends/CBMC/tests/simpleTest.core.st

echo "######################################################################"

echo "C_Simp -> CBMC: illustrates verification success."
echo "----------------------------------------------------------------------"
Strata/Backends/CBMC/run_strata_cbmc.sh Strata/Backends/CBMC/tests/simpleTest.csimp.st

echo "######################################################################"

popd

echo "Now, tests for the GOTO assembly instructions interface."

pushd SimpleAdd
./mkGotoBin.sh
popd

echo "######################################################################"
