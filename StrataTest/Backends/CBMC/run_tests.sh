echo "Running all Strata-CBMC related tests..."

echo "######################################################################"
echo "First: tests for the C-like AST interface."

echo "Tests for the GOTO assembly instructions interface."

pushd SimpleAdd
./mkGotoBin.sh
popd

echo "######################################################################"
