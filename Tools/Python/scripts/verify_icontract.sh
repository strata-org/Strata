#!/bin/bash
# Verify Python user code against icontract specs using Strata.
#
# Usage: ./verify.sh [--spec extra_spec.py]... <file.py> [user_file]
#
# If user_file is omitted, file.py is used as both spec and user code.
# Use --spec to add additional spec files (e.g., stdlib contracts).
#
# Examples:
#   ./verify.sh withdraw.py                                # single file
#   ./verify.sh --spec builtins_spec.py user_code.py       # stdlib spec + user code

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
STRATA_DIR="${STRATA_DIR:-$(dirname "$SCRIPT_DIR")/Strata}"
STRATA_BIN="$STRATA_DIR/.lake/build/bin/strata"
STRATA_PYTHON="$STRATA_DIR/Tools/Python"
DIALECT="$STRATA_PYTHON/dialects/Python.dialect.st.ion"

# Ensure tools are on PATH
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
# Use mise Python if available
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

# Auto-include builtins_spec.py only if user code calls min/max/abs
BUILTINS_SPEC="$SCRIPT_DIR/builtins_spec.py"

if [ $# -lt 1 ]; then
    echo "Usage: $0 [--spec extra_spec.py]... <spec_file> [user_file]"
    exit 1
fi

SPEC_FILE="$(realpath "$1")"
USER_FILE="$(realpath "${2:-$1}")"
ORIG_USER_FILE="${2:-$1}"

if [ -f "$BUILTINS_SPEC" ] && grep -q '\bmin\b\|\bmax\b\|\babs\b' "$USER_FILE"; then
    EXTRA_SPECS+=("$(realpath "$BUILTINS_SPEC")")
fi
MODULE_NAME="$(basename "$USER_FILE" .py)"

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

PYSPEC_ION="$TMPDIR/${MODULE_NAME}.pyspec.st.ion"
USER_ION="$TMPDIR/${MODULE_NAME}.python.st.ion"

# Step 1: Convert main icontract specs to pyspec Ion
ONLY_DECORATED=""
if [ "$SPEC_FILE" = "$USER_FILE" ]; then
    ONLY_DECORATED="--only-decorated"
fi
python3 -m strata.icontract "$SPEC_FILE" "$PYSPEC_ION" --module "$MODULE_NAME" $ONLY_DECORATED >/dev/null 2>&1

# Step 1b: Convert extra spec files to pyspec Ion
PYSPEC_ARGS="--pyspec $MODULE_NAME"
for EXTRA in "${EXTRA_SPECS[@]+"${EXTRA_SPECS[@]}"}"; do
    EXTRA_MOD="$(basename "$EXTRA" .py)"
    EXTRA_ION="$TMPDIR/${EXTRA_MOD}.pyspec.st.ion"
    python3 -m strata.icontract "$EXTRA" "$EXTRA_ION" --module "$EXTRA_MOD" >/dev/null 2>&1
    PYSPEC_ARGS="$PYSPEC_ARGS --pyspec $EXTRA_MOD"
done

# Step 2: Convert user code to Python Ion
(cd "$STRATA_PYTHON" && python3 -m strata.gen py_to_strata --dialect "$DIALECT" "$USER_FILE" "$USER_ION") 2>/dev/null || {
    echo "Error converting $USER_FILE to Python Ion" >&2
    exit 1
}

# Step 3: Run Strata verification
RAW_OUTPUT=$("$STRATA_BIN" pyAnalyzeLaurel \
    --spec-dir "$TMPDIR" \
    $PYSPEC_ARGS \
    "$USER_ION" 2>&1) || true

# Step 4: Format results — pass all spec files so call sites from extra specs are found
ALL_SPECS="$SPEC_FILE"
for EXTRA in "${EXTRA_SPECS[@]+"${EXTRA_SPECS[@]}"}"; do
    ALL_SPECS="$ALL_SPECS:$EXTRA"
done
echo "$RAW_OUTPUT" | python3 -m strata.format_results "$ALL_SPECS" "$USER_FILE" "$ORIG_USER_FILE"
