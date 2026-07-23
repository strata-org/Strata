#!/bin/bash
# Full StrataAgent setup — runs all sub-setup scripts and installs deps
# Usage: ./StrataAgent/setup.sh
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
VENV="$SCRIPT_DIR/.venv"
LEAN_VERSION=$(cat "$PROJECT_ROOT/lean-toolchain" | sed 's|leanprover/lean4:v||')

echo "=== StrataAgent Full Setup ==="
echo

# ─── 1. Venv + Python deps ───────────────────────────────────────────────────
echo "1. Python dependencies..."
source "$VENV/bin/activate"
uv pip install claude-agent-sdk jinja2 pydantic fastapi "uvicorn[standard]" 2>&1 | tail -3
uv pip install itp-interface==1.9.0 --no-deps 2>&1 | tail -1
echo

# ─── 2. ripgrep ──────────────────────────────────────────────────────────────
echo "2. ripgrep..."
"$SCRIPT_DIR/install_ripgrep.sh"
echo

# ─── 3. lean-lsp-mcp ─────────────────────────────────────────────────────────
echo "3. lean-lsp-mcp..."
"$SCRIPT_DIR/lean_mcp_setup.sh"
echo

# ─── 4. itp-interface tactic parser ──────────────────────────────────────────
echo "4. itp-interface tactic parser (Lean $LEAN_VERSION)..."
export LEAN_VERSION="$LEAN_VERSION"
install-itp-interface
echo

# ─── 5. SwarmAgentTools ───────────────────────────────────────────────────────
echo "5. SwarmAgentTools (Lean binary)..."
cd "$PROJECT_ROOT"
BUILD_LOG="$(mktemp)"
if lake build SwarmAgentTools > "$BUILD_LOG" 2>&1; then
  tail -3 "$BUILD_LOG"
  rm -f "$BUILD_LOG"
else
  tail -15 "$BUILD_LOG"
  echo
  echo "════════════════════════════════════════════════════════════════════════"
  echo " ERROR: 'lake build SwarmAgentTools' failed."
  echo "════════════════════════════════════════════════════════════════════════"
  if grep -q "not in manifest" "$BUILD_LOG"; then
    echo " This is a Lake manifest/lakefile mismatch in your project (a 'require'"
    echo " in lakefile.toml is missing from lake-manifest.json). It is NOT caused"
    echo " by StrataAgent — the build inherits your project's dependencies."
    echo
    echo " Fix it by syncing the manifest, then re-run setup:"
    echo
    echo "     cd $PROJECT_ROOT"
    echo "     lake update"
    echo "     ./StrataAgent/setup.sh"
  else
    echo " Fix the errors above, then re-run:"
    echo
    echo "     ./StrataAgent/setup.sh"
    echo
    echo " Full build log: $BUILD_LOG"
  fi
  echo "════════════════════════════════════════════════════════════════════════"
  exit 1
fi
echo

# ─── 6. repl (optional — enables lean_multi_attempt) ─────────────────────────
# Built STANDALONE in StrataAgent/.repl, never as a dependency of the host
# project. repl has no external requires, so a plain `lake build` works with no
# `lake update` — this avoids touching the host lakefile/manifest entirely and
# stays robust when the project's dependencies live outside .lake/packages (in
# which case a `lake update` on the host would fail).
#
# start_dashboard.sh reads StrataAgent/.repl/.lake/build/bin/repl and exports
# LEAN_REPL / LEAN_REPL_PATH so lean-lsp-mcp enables lean_multi_attempt.
echo "6. repl (optional, for lean_multi_attempt)..."
REPL_URL="https://github.com/leanprover-community/repl"
REPL_DIR="$SCRIPT_DIR/.repl"

# Match a repl tag to the project's Lean toolchain (repl tags one per release;
# fall back to the same major.minor .0 tag, e.g. 4.29.1 -> v4.29.0).
REPL_TAGS=$(git ls-remote --tags "$REPL_URL" 2>/dev/null | grep -oP 'refs/tags/\Kv[^\^]+$')
REPL_REV=""
if printf '%s\n' "$REPL_TAGS" | grep -qx "v$LEAN_VERSION"; then
  REPL_REV="v$LEAN_VERSION"
else
  MAJ_MIN=$(echo "$LEAN_VERSION" | cut -d. -f1,2)
  printf '%s\n' "$REPL_TAGS" | grep -qx "v$MAJ_MIN.0" && REPL_REV="v$MAJ_MIN.0"
fi

if [ -z "$REPL_REV" ]; then
  echo "  [SKIP] No repl tag matches Lean '$LEAN_VERSION' — lean_multi_attempt unavailable."
else
  # Clone (or reuse) repl at the matched rev.
  if [ ! -d "$REPL_DIR/.git" ]; then
    rm -rf "$REPL_DIR"
    git clone --quiet --depth 1 --branch "$REPL_REV" "$REPL_URL" "$REPL_DIR" 2>/dev/null || \
      git clone --quiet "$REPL_URL" "$REPL_DIR"
  fi
  git -C "$REPL_DIR" fetch --quiet --depth 1 origin "$REPL_REV" 2>/dev/null || true
  git -C "$REPL_DIR" checkout --quiet "$REPL_REV" 2>/dev/null || true
  # Force the SAME toolchain as the host project so oleans are compatible.
  cp "$PROJECT_ROOT/lean-toolchain" "$REPL_DIR/lean-toolchain"

  REPL_LOG="$(mktemp)"
  if (cd "$REPL_DIR" && lake build repl) > "$REPL_LOG" 2>&1; then
    echo "  [OK] repl $REPL_REV built at $REPL_DIR/.lake/build/bin/repl"
    echo "       lean_multi_attempt will be enabled by start_dashboard.sh."
    rm -f "$REPL_LOG"
  else
    tail -8 "$REPL_LOG"
    echo "  [WARN] repl build failed — lean_multi_attempt unavailable (everything else works)."
    echo "         Full log: $REPL_LOG"
  fi
fi
echo

echo "=== Setup complete ==="
