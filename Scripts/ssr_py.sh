#!/usr/bin/env bash
# ------------------------------------------------------------------------------
# ssr_py.sh — Split-Solve-Reconcile workflow for Python analysis.
#
# Runs the three phases of cloud-compatible SMT solving for a Python file:
#
#   1. Generate — convert .py to Strata Ion, run `strata pyAnalyzeLaurel
#      --no-solve` to produce a manifest + .smt2 files.
#   2. Solve    — run an SMT solver on every .smt2 file (in parallel).
#   3. Reconcile — run `strata reconcile` against the manifest + .result
#      files and produce the final report.
#
# By default, everything runs locally (the Solve phase fans out over
# `xargs -P`). To wire in a real cloud solver, override the SOLVER_CMD
# environment variable or edit the `solve_phase` function.
#
# Prerequisites:
#   - strata executable available (default: ./.lake/build/bin/strata)
#   - Python 3.13+ with the strata package installed
#     (`cd Tools/Python && pip install .`)
#   - An SMT solver on PATH (cvc5 by default; Z3 works too)
#   - The Python dialect file at ./dialects/Python.dialect.st.ion
#     (regenerate with `python -m strata.gen dialect dialects`)
#
# Usage:
#   ./ssr_py.sh [options] <input.py>
#
# Options:
#   -o, --output-dir <dir>   Where to place the manifest, .smt2, .result files
#                            (default: ./ssr_out/<basename>)
#   -s, --solver <cmd>       SMT solver command. Receives the .smt2 path as
#                            the first arg; its stdout becomes the .result.
#                            (default: "cvc5 --produce-models")
#   -j, --jobs <N>           Number of parallel solver processes (default: 4)
#   -c, --check-mode <mode>  Strata check mode: deductive, bugFinding,
#                            bugFindingAssumingCompleteSpec (default: deductive)
#   -l, --check-level <lev>  Strata check level: minimal, minimalVerbose, full
#                            (default: minimal)
#      --spec-dir <dir>      Directory with compiled PySpec Ion files
#                            (default: ".")
#      --sarif               Also emit reconcile.sarif in <output-dir>
#      --strict              Fail if any .result file is missing
#      --keep                Keep intermediate files even on failure
#      --skip-generate       Skip phase 1 (reuse existing <output-dir>)
#      --skip-solve          Skip phase 2 (reuse existing .result files)
#      --skip-reconcile      Skip phase 3 (only generate + solve)
#      --strata <path>       Path to the strata binary
#                            (default: ./.lake/build/bin/strata)
#      --dialect <path>      Path to Python dialect Ion file
#                            (default: ./dialects/Python.dialect.st.ion)
#      --dispatch <module>   Dispatch module name (may be repeated)
#      --pyspec <module>     PySpec module name (may be repeated)
#   -h, --help               Show this help
#
# Exit codes:
#   0  — all goals passed
#   1  — user error (missing prerequisites, bad args)
#   2  — failures found during reconcile
#   3  — internal error (generate/solve/reconcile crashed)
# ------------------------------------------------------------------------------

set -u  # Treat unset variables as errors. We handle non-zero ourselves.

# -------- defaults --------
OUTPUT_DIR=""
SOLVER_CMD="${SOLVER_CMD:-cvc5 --produce-models}"
JOBS=4
CHECK_MODE="deductive"
CHECK_LEVEL="minimal"
SPEC_DIR="."
EMIT_SARIF=0
STRICT=0
KEEP=0
SKIP_GENERATE=0
SKIP_SOLVE=0
SKIP_RECONCILE=0
STRATA_BIN="./.lake/build/bin/strata"
DIALECT_FILE="./dialects/Python.dialect.st.ion"
DISPATCH_MODULES=()
PYSPEC_MODULES=()
INPUT_PY=""

# -------- helpers --------
err()   { printf '\033[1;31merror:\033[0m %s\n' "$*" >&2; }
warn()  { printf '\033[1;33mwarn:\033[0m %s\n'  "$*" >&2; }
info()  { printf '\033[1;34m==>\033[0m %s\n'   "$*" >&2; }
step()  { printf '\033[1;32m-->\033[0m %s\n'   "$*" >&2; }

usage() {
  sed -n '3,62p' "$0" | sed 's/^# \{0,1\}//'
}

die_user() {
  err "$*"
  exit 1
}

die_internal() {
  err "$*"
  exit 3
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die_user "'$1' not found on PATH"
}

# -------- arg parsing --------
while [ $# -gt 0 ]; do
  case "$1" in
    -o|--output-dir)   OUTPUT_DIR="$2"; shift 2 ;;
    -s|--solver)       SOLVER_CMD="$2"; shift 2 ;;
    -j|--jobs)         JOBS="$2"; shift 2 ;;
    -c|--check-mode)   CHECK_MODE="$2"; shift 2 ;;
    -l|--check-level)  CHECK_LEVEL="$2"; shift 2 ;;
    --spec-dir)        SPEC_DIR="$2"; shift 2 ;;
    --sarif)           EMIT_SARIF=1; shift ;;
    --strict)          STRICT=1; shift ;;
    --keep)            KEEP=1; shift ;;
    --skip-generate)   SKIP_GENERATE=1; shift ;;
    --skip-solve)      SKIP_SOLVE=1; shift ;;
    --skip-reconcile)  SKIP_RECONCILE=1; shift ;;
    --strata)          STRATA_BIN="$2"; shift 2 ;;
    --dialect)         DIALECT_FILE="$2"; shift 2 ;;
    --dispatch)        DISPATCH_MODULES+=("$2"); shift 2 ;;
    --pyspec)          PYSPEC_MODULES+=("$2"); shift 2 ;;
    -h|--help)         usage; exit 0 ;;
    --)                shift; INPUT_PY="${1:-}"; break ;;
    -*)                die_user "unknown option: $1" ;;
    *)                 INPUT_PY="$1"; shift ;;
  esac
done

# -------- validate args --------
[ -z "$INPUT_PY" ] && { usage; exit 1; }
[ -f "$INPUT_PY" ] || die_user "input file '$INPUT_PY' does not exist"

case "$INPUT_PY" in
  *.py|*.python.st.ion) ;;
  *) warn "input file '$INPUT_PY' is not a .py or .python.st.ion file; proceeding anyway" ;;
esac

# Derive output directory if not provided.
if [ -z "$OUTPUT_DIR" ]; then
  base="$(basename "$INPUT_PY")"
  base="${base%.py}"
  base="${base%.python.st.ion}"
  OUTPUT_DIR="./ssr_out/${base}"
fi

[ -x "$STRATA_BIN" ] || die_user "strata binary not found at '$STRATA_BIN'. Run 'lake build strata:exe' first, or pass --strata <path>."

mkdir -p "$OUTPUT_DIR"

# -------- phase 1: generate --------
# Compiles the Python source to an Ion file (if needed) and runs
# `strata pyAnalyzeLaurel --no-solve` to emit manifest.json + *.smt2.

ION_FILE="$OUTPUT_DIR/input.python.st.ion"

generate_phase() {
  step "Phase 1: generate"

  # If the input is already an Ion file, just symlink it into place.
  if [ "${INPUT_PY##*.}" = "ion" ] || [ "${INPUT_PY: -14}" = ".python.st.ion" ]; then
    info "Input is already a Python Ion file; copying into place"
    cp -f "$INPUT_PY" "$ION_FILE"
  else
    [ -f "$DIALECT_FILE" ] || die_user "dialect file '$DIALECT_FILE' not found. Regenerate with 'python -m strata.gen dialect dialects'."
    require_cmd python3
    info "Converting $INPUT_PY -> $ION_FILE"
    if ! python3 -m strata.gen py_to_strata --dialect "$DIALECT_FILE" "$INPUT_PY" "$ION_FILE"; then
      die_internal "py_to_strata failed on '$INPUT_PY'. Is the strata Python package installed? Try 'cd Tools/Python && pip install .'"
    fi
  fi

  info "Running strata pyAnalyzeLaurel --no-solve"
  local py_args=(
    pyAnalyzeLaurel "$ION_FILE"
    --no-solve
    --vc-directory "$OUTPUT_DIR"
    --spec-dir "$SPEC_DIR"
    --check-mode "$CHECK_MODE"
    --check-level "$CHECK_LEVEL"
  )
  for m in "${DISPATCH_MODULES[@]}"; do py_args+=( --dispatch "$m" ); done
  for m in "${PYSPEC_MODULES[@]}";  do py_args+=( --pyspec "$m" );  done

  if ! "$STRATA_BIN" "${py_args[@]}" > "$OUTPUT_DIR/generate.log" 2>&1; then
    err "strata pyAnalyzeLaurel --no-solve failed (see $OUTPUT_DIR/generate.log)"
    tail -n 30 "$OUTPUT_DIR/generate.log" >&2 || true
    exit 3
  fi
  info "Generate phase complete. Log: $OUTPUT_DIR/generate.log"

  [ -f "$OUTPUT_DIR/manifest.json" ] || die_internal "strata did not produce $OUTPUT_DIR/manifest.json"
}

# -------- phase 2: solve --------
# Runs the SMT solver on every .smt2 file, in parallel, capturing stdout
# (and stderr) into matching .result files.

solve_one() {
  local smt="$1"
  local base="${smt%.smt2}"
  local result="${base}.result"
  # shellcheck disable=SC2086  # we *want* word splitting on $SOLVER_CMD
  $SOLVER_CMD "$smt" > "$result" 2>&1
}
export -f solve_one

solve_phase() {
  step "Phase 2: solve"
  local solver_bin="${SOLVER_CMD%% *}"
  require_cmd "$solver_bin"

  local smt2_count
  smt2_count=$(find "$OUTPUT_DIR" -maxdepth 1 -name '*.smt2' -type f | wc -l)
  if [ "$smt2_count" -eq 0 ]; then
    info "No .smt2 files to solve (all obligations resolved by evaluator)."
    return
  fi
  info "Solving $smt2_count .smt2 files with $JOBS parallel workers"
  info "Solver: $SOLVER_CMD"

  export SOLVER_CMD
  # Use xargs for portable parallelism. `-P $JOBS` runs up to $JOBS in
  # parallel; `-I {}` implies one argument per invocation.
  find "$OUTPUT_DIR" -maxdepth 1 -name '*.smt2' -type f -print0 \
    | xargs -0 -P "$JOBS" -I {} bash -c 'solve_one "$@"' _ {}
  info "Solve phase complete."
}

# -------- phase 3: reconcile --------
# Runs `strata reconcile` to classify results and produce the final report.

reconcile_phase() {
  step "Phase 3: reconcile"
  local rec_args=(
    reconcile
    --vc-directory "$OUTPUT_DIR"
    --check-mode "$CHECK_MODE"
    --check-level "$CHECK_LEVEL"
  )
  [ "$EMIT_SARIF" -eq 1 ] && rec_args+=( --sarif )
  [ "$STRICT"     -eq 1 ] && rec_args+=( --strict )

  "$STRATA_BIN" "${rec_args[@]}" | tee "$OUTPUT_DIR/reconcile.log"
  local rc="${PIPESTATUS[0]}"
  info "Reconcile phase complete. Log: $OUTPUT_DIR/reconcile.log"
  return "$rc"
}

# -------- drive the workflow --------
[ "$SKIP_GENERATE"  -eq 0 ] && generate_phase
[ "$SKIP_SOLVE"     -eq 0 ] && solve_phase
if [ "$SKIP_RECONCILE" -eq 0 ]; then
  reconcile_phase
  rc=$?
  if [ "$KEEP" -eq 0 ] && [ "$rc" -eq 0 ]; then
    info "Success. Artifacts kept in $OUTPUT_DIR (pass --keep or rerun with --skip-* to reuse)."
  fi
  exit "$rc"
fi
