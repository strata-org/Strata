#!/bin/bash
# Verify Python user code against icontract specs using Strata.
#
# Usage: ./verify_icontract.sh [--spec extra_spec.py]... <file.py> [user_file]
#
# If user_file is omitted, file.py is used as both spec and user code.
# Use --spec to add additional spec files (e.g., stdlib contracts).
#
# Examples:
#   ./verify_icontract.sh withdraw.py                          # single file
#   ./verify_icontract.sh --spec builtins_spec.py user_code.py # stdlib spec + user code

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
STRATA_DIR="${STRATA_DIR:-$(dirname "$SCRIPT_DIR")}"
STRATA_BIN="$STRATA_DIR/.lake/build/bin/strata"
STRATA_PYTHON="$STRATA_DIR/Tools/Python"
DIALECT="$STRATA_PYTHON/dialects/Python.dialect.st.ion"

# Ensure strata Python package is importable
export PYTHONPATH="${STRATA_PYTHON}:${PYTHONPATH:-}"
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
if command -v mise &>/dev/null; then
    eval "$(mise activate bash 2>/dev/null)" || true
fi

# Parse --spec flags
EXTRA_SPECS=()
while [[ $# -gt 0 && "$1" == "--spec" ]]; do
    shift
    EXTRA_SPECS+=("$(realpath "$1")")
    shift
done

if [ $# -lt 1 ]; then
    echo "Usage: $0 [--spec extra_spec.py]... <spec_file> [user_file]"
    exit 1
fi

SPEC_FILE="$(realpath "$1")"
USER_FILE="$(realpath "${2:-$1}")"
ORIG_USER_FILE="${2:-$1}"
MODULE_NAME="$(basename "$USER_FILE" .py)"

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

# Collect all spec files into a temporary directory for pySpecs
SPEC_SRC_DIR="$TMPDIR/specs"
mkdir -p "$SPEC_SRC_DIR"
cp "$SPEC_FILE" "$SPEC_SRC_DIR/"
for EXTRA in "${EXTRA_SPECS[@]+"${EXTRA_SPECS[@]}"}"; do
    cp "$EXTRA" "$SPEC_SRC_DIR/"
done

# Step 1: Convert icontract specs to pyspec Ion using pySpecs (Lean)
PYSPEC_DIR="$TMPDIR/pyspec"
SPEC_MODULE="$(basename "$SPEC_FILE" .py)"
"$STRATA_BIN" pySpecs "$SPEC_SRC_DIR" "$PYSPEC_DIR" --quiet --module "$SPEC_MODULE" 2>/dev/null || {
    echo "Error converting icontract specs to pyspec Ion" >&2
    exit 1
}

# Build --pyspec args
PYSPEC_ARGS="--pyspec $SPEC_MODULE"
for EXTRA in "${EXTRA_SPECS[@]+"${EXTRA_SPECS[@]}"}"; do
    EXTRA_MOD="$(basename "$EXTRA" .py)"
    PYSPEC_ARGS="$PYSPEC_ARGS --pyspec $EXTRA_MOD"
done

# Step 2: Convert user code to Python Ion
USER_ION="$TMPDIR/${MODULE_NAME}.python.st.ion"
(cd "$STRATA_PYTHON" && python3 -m strata.gen py_to_strata --dialect "$DIALECT" "$USER_FILE" "$USER_ION") 2>/dev/null || {
    echo "Error converting $USER_FILE to Python Ion" >&2
    exit 1
}

# Step 3: Run Strata verification
RAW_OUTPUT=$("$STRATA_BIN" pyAnalyzeLaurel \
    --spec-dir "$PYSPEC_DIR" \
    $PYSPEC_ARGS \
    "$USER_ION" 2>&1) || true

# Step 4: Format results
ALL_SPECS="$SPEC_FILE"
for EXTRA in "${EXTRA_SPECS[@]+"${EXTRA_SPECS[@]}"}"; do
    ALL_SPECS="$ALL_SPECS:$EXTRA"
done
echo "$RAW_OUTPUT" | python3 -m strata.format_results "$ALL_SPECS" "$USER_FILE" "$ORIG_USER_FILE"
