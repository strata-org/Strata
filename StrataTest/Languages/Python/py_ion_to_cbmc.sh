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
run "symtab2gb" symtab2gb "$PROJECT_ROOT/$BN.symtab.json" \
  --goto-functions "$PROJECT_ROOT/$BN.goto.json" \
  --out "$WORK_DIR/$BN.gb"

# Set entry point via goto-cc (works for both cbmc and cprover)
GOTO_CC=${GOTO_CC:-goto-cc}
run "goto-cc (set entry point)" "$GOTO_CC" --function main \
  "$WORK_DIR/$BN.gb" -o "$WORK_DIR/$BN.gb"

CBMC=${CBMC:-cbmc}
CBMC_TIMEOUT=${CBMC_TIMEOUT:-120}
CBMC_SOLVER_FLAG=${CBMC_SOLVER_FLAG-"--z3"}
CBMC_EXTRA_FLAGS=${CBMC_EXTRA_FLAGS-"--no-pointer-check"}
CBMC_VERBOSITY=${CBMC_VERBOSITY-"--verbosity 9"}
# Run CBMC/cprover with a timeout (portable: works on macOS and Linux)
"$CBMC" "$WORK_DIR/$BN.gb" $CBMC_SOLVER_FLAG $CBMC_EXTRA_FLAGS $CBMC_VERBOSITY &
cbmc_pid=$!
# Timer: write sleep PID so we can kill it directly
TIMER_SLEEP_PID_FILE=$(mktemp)
(
  sleep "$CBMC_TIMEOUT" &
  echo $! > "$TIMER_SLEEP_PID_FILE"
  wait $!
  kill "$cbmc_pid" 2>/dev/null
) &
timer_pid=$!
wait "$cbmc_pid" 2>/dev/null
cbmc_rc=$?
# Kill the timer: both the subshell and the sleep
kill "$timer_pid" 2>/dev/null
sleep_pid=$(cat "$TIMER_SLEEP_PID_FILE" 2>/dev/null)
[ -n "$sleep_pid" ] && kill "$sleep_pid" 2>/dev/null
rm -f "$TIMER_SLEEP_PID_FILE"
wait "$timer_pid" 2>/dev/null
# Exit codes: 0=safe, 10=unsafe, 6=error, 137/143=killed by timeout
if [ "$cbmc_rc" -eq 137 ] || [ "$cbmc_rc" -eq 143 ] || [ "$cbmc_rc" -eq 15 ] || [ "$cbmc_rc" -eq 9 ]; then
  echo "VERIFICATION ERROR (timeout after ${CBMC_TIMEOUT}s)"
  exit 0
fi
if [ "$cbmc_rc" -ne 0 ] && [ "$cbmc_rc" -ne 10 ] && [ "$cbmc_rc" -ne 6 ]; then
  echo "Error: cbmc verification failed (exit code $cbmc_rc)" >&2
  exit 1
fi
