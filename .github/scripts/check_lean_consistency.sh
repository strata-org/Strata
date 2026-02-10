#!/bin/bash
# This checks that the version of Lean in the main package
# matches the version in the Verso documentation package.
set -e

if cmp --silent "lean-toolchain" "docs/verso/lean-toolchain"; then
  exit 0
else
  echo "Strata and StrataDoc lean versions do not match."
  exit 1
fi