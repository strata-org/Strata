#!/bin/bash
#
# Translate a Laurel .lr.st file through the Strata pipeline to CBMC verification.
# Usage: ./laurel_to_cbmc.sh <file.lr.st>
#
# Environment variables:
#   CBMC              - path to cbmc binary (default: cbmc)
#   GOTO_CC           - path to goto-cc binary (default: goto-cc)
#   GOTO_INSTRUMENT   - path to goto-instrument binary (default: goto-instrument)
#   STRATA            - path to strata binary (default: uses lake exe strata)

if [ -z "$1" ]; then
  echo "Usage: $0 <file.lr.st>" >&2
  exit 1
fi

if [ ! -f "$1" ]; then
  echo "Error: file not found: $1" >&2
  exit 1
fi

LAUREL="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
# deriveBaseName in StrataMain.lean strips .st from the filename
BN=$(basename "$LAUREL" .st)

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
  run "strata laurelAnalyzeToGoto" "$STRATA" laurelAnalyzeToGoto "$LAUREL"
else
  (cd "$PROJECT_ROOT" && run "lake exe strata laurelAnalyzeToGoto" lake exe strata laurelAnalyzeToGoto "$LAUREL") || exit $?
fi

# Intermediate files are created in cwd with basename
run "process_json.py combine" python3 "$PROJECT_ROOT/Strata/Backends/CBMC/resources/process_json.py" \
  combine "$PROJECT_ROOT/Strata/Backends/CBMC/resources/defaults.json" \
  "$PROJECT_ROOT/$BN.symtab.json" > "$WORK_DIR/$BN.full-symtab.json"

run "symtab2gb" symtab2gb "$WORK_DIR/$BN.full-symtab.json" \
  --goto-functions "$PROJECT_ROOT/$BN.goto.json" \
  --out "$WORK_DIR/$BN.gb"

GOTO_CC=${GOTO_CC:-goto-cc}
run "goto-cc (add C scaffolding)" "$GOTO_CC" --function main -o "$WORK_DIR/${BN}_cc.gb" "$WORK_DIR/$BN.gb"

GOTO_INSTRUMENT=${GOTO_INSTRUMENT:-goto-instrument}
run "goto-instrument --dfcc" "$GOTO_INSTRUMENT" --dfcc main "$WORK_DIR/${BN}_cc.gb" "$WORK_DIR/${BN}_dfcc.gb"

CBMC=${CBMC:-cbmc}
run "cbmc verification" "$CBMC" "$WORK_DIR/${BN}_dfcc.gb" --function main --z3 --verbosity 9
