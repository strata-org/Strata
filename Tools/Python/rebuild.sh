#!/bin/sh
set -e

pip install .
# Rebuild dialects
PYTHON_GIL=0 python -m strata.gen dialect PythonAST test_results/dialects
PYTHON_GIL=0 python -m strata.gen dialect PythonSSA test_results/dialects
