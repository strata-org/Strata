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

echo "=== Setup complete ==="
