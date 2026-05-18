#!/bin/bash
# Regenerate Java roundtrip test data
#
# Note: The Java code generator now uses the `getIonSerializer%` elaborator
# which works with Lean types instead of DDM dialect files. The roundtrip
# test in TestGen.lean generates and verifies test data on the fly.
#
# This script is kept for reference but the test data files are no longer
# needed for the current test suite.
set -e
echo "The Java code generator now uses getIonSerializer% with Lean types."
echo "Roundtrip tests are run automatically during 'lake build StrataTestExtra'."
echo "No manual regeneration needed."
