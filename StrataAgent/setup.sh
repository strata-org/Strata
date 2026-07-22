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
lake build SwarmAgentTools 2>&1 | tail -3
echo

# ─── 6. repl (optional — enables lean_multi_attempt) ─────────────────────────
# Added AFTER the core build so a repl/plausible dependency conflict can never
# block SwarmAgentTools. The rev is matched to this project's Lean toolchain;
# if anything fails, the lakefile is restored to its pre-repl state.
LAKEFILE="$PROJECT_ROOT/lakefile.toml"
if [ -f "$LAKEFILE" ] && ! grep -q 'name = "repl"' "$LAKEFILE"; then
  echo "6. repl (optional, for lean_multi_attempt)..."
  REPL_URL="https://github.com/leanprover-community/repl"
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
    cp "$LAKEFILE" "$LAKEFILE.strata_bak"
    printf '\n[[require]]\nname = "repl"\ngit = "%s"\nrev = "%s"\n' "$REPL_URL" "$REPL_REV" >> "$LAKEFILE"
    if lake update repl >/dev/null 2>&1 && lake build repl >/dev/null 2>&1; then
      echo "  [OK] repl $REPL_REV built (matched to Lean $LEAN_VERSION)."
      rm -f "$LAKEFILE.strata_bak"
    else
      echo "  [WARN] repl setup failed — reverting lakefile. lean_multi_attempt unavailable."
      mv "$LAKEFILE.strata_bak" "$LAKEFILE"
    fi
  fi
  echo
fi

echo "=== Setup complete ==="
