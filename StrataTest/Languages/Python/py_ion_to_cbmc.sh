#!/bin/bash
#
# Translate a Python .ion file through the Strata pipeline to CBMC verification.
# Usage: ./py_ion_to_cbmc.sh <file.py.ion>
#
# Environment variables:
#   CBMC     - path to cbmc binary (default: cbmc)
#   STRATA   - path to strata binary (default: uses lake exe strata)

if [ -z "$1" ]; then
  echo "Usage: $0 <file.py.ion>" >&2
  exit 1
fi

if [ ! -f "$1" ]; then
  echo "Error: file not found: $1" >&2
  exit 1
fi

ION="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
# Mirror deriveBaseName in StrataMain.lean
BN=$(basename "$ION")
BN="${BN%.py.ion}"
BN="${BN%.python.st.ion}"
BN="${BN%.st.ion}"

# Locate project root (three levels up from this script's directory)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"

# Use a temporary directory for intermediate files
WORK_DIR=$(mktemp -d)
cleanup() { rm -rf "$WORK_DIR" "$PROJECT_ROOT/$BN.symtab.json" "$PROJECT_ROOT/$BN.goto.json"; }
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

# Run Strata pipeline
if [ -n "$STRATA" ]; then
  run "strata pyAnalyzeLaurelToGoto" "$STRATA" pyAnalyzeLaurelToGoto "$ION"
else
  (cd "$PROJECT_ROOT" && run "lake exe strata pyAnalyzeLaurelToGoto" lake exe strata pyAnalyzeLaurelToGoto "$ION") || exit $?
fi

# Intermediate files are created in cwd with basename
run "process_json.py combine" python3 "$PROJECT_ROOT/Strata/Backends/CBMC/resources/process_json.py" \
  combine "$PROJECT_ROOT/Strata/Backends/CBMC/resources/defaults.json" \
  "$PROJECT_ROOT/$BN.symtab.json" > "$WORK_DIR/$BN.full-symtab.json"

run "symtab2gb" symtab2gb "$WORK_DIR/$BN.full-symtab.json" \
  --goto-functions "$PROJECT_ROOT/$BN.goto.json" \
  --out "$WORK_DIR/$BN.gb"

CBMC=${CBMC:-cbmc}
run "cbmc verification" "$CBMC" "$WORK_DIR/$BN.gb" --function main --z3 --verbosity 9
