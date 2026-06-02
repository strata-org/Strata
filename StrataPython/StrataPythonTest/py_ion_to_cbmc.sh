#!/bin/bash
#
# Translate a Python .ion file through the Strata pipeline to CBMC verification.
# Usage: ./py_ion_to_cbmc.sh <file.py.ion>
#
# Environment variables:
#   CBMC   - path to cbmc binary (default: cbmc)

if [ -z "$1" ]; then
  echo "Usage: $0 <file.py.ion>" >&2
  exit 1
fi

if [ ! -f "$1" ]; then
  echo "Error: file not found: $1" >&2
  exit 1
fi

ION="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
BN=$(basename "$ION")
BN="${BN%.py.ion}"
BN="${BN%.python.st.ion}"
BN="${BN%.st.ion}"

# StrataPython package directory (two levels up from this script)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
STRATA_PYTHON_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Use a temporary directory for intermediate files
WORK_DIR=$(mktemp -d)
cleanup() { rm -rf "$WORK_DIR" "$STRATA_PYTHON_DIR/$BN.symtab.json" "$STRATA_PYTHON_DIR/$BN.goto.json"; }
trap cleanup EXIT

run() {
  local step="$1"; shift
  "$@"
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "Error: $step failed (exit code $rc)" >&2
    exit 1
  fi
}

# Run PyAnalyzeLaurelToGoto from StrataPython
(cd "$STRATA_PYTHON_DIR" && run "PyAnalyzeLaurelToGoto" lake exe PyAnalyzeLaurelToGoto "$ION") || exit $?

# Intermediate files are created in cwd with basename
run "symtab2gb" symtab2gb "$STRATA_PYTHON_DIR/$BN.symtab.json" \
  --goto-functions "$STRATA_PYTHON_DIR/$BN.goto.json" \
  --out "$WORK_DIR/$BN.gb"

CBMC=${CBMC:-cbmc}
run "cbmc verification" "$CBMC" "$WORK_DIR/$BN.gb" --function main --z3 --verbosity 9
