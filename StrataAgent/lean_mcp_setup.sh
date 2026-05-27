#!/bin/bash
# Setup script for lean-lsp-mcp (Lean 4 Language Server MCP)
# This MCP provides: lean_verify, lean_goal, lean_build, lean_local_search,
# lean_multi_attempt, leansearch, loogle, and more.
#
# Run this once before using the LeanSwarm with MCP-enabled agents.

set -e

echo "=== lean-lsp-mcp setup ==="
echo ""

# 1. Check uv/uvx
if command -v uvx &> /dev/null; then
    echo "[OK] uvx found: $(uvx --version)"
else
    echo "[INSTALLING] uv (includes uvx)..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$PATH"
    if command -v uvx &> /dev/null; then
        echo "[OK] uvx installed: $(uvx --version)"
    else
        echo "[FAIL] uvx installation failed. Please install manually:"
        echo "  curl -LsSf https://astral.sh/uv/install.sh | sh"
        exit 1
    fi
fi

# 2. Check ripgrep
if command -v rg &> /dev/null; then
    echo "[OK] ripgrep found: $(rg --version | head -1)"
else
    echo "[WARN] ripgrep (rg) not found. Attempting to install..."
    SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
    if [ -x "$SCRIPT_DIR/install_ripgrep.sh" ]; then
        "$SCRIPT_DIR/install_ripgrep.sh"
    else
        echo "       Run: ./StrataAgent/install_ripgrep.sh"
    fi
fi

# 3. Pre-fetch lean-lsp-mcp so first run is fast
echo ""
echo "[SETUP] Pre-fetching lean-lsp-mcp package..."
uvx --quiet lean-lsp-mcp --help > /dev/null 2>&1 || true
echo "[OK] lean-lsp-mcp cached"

# 4. Check Lean project builds
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
echo ""
echo "[CHECK] Verifying Lean project at: $PROJECT_ROOT"

if [ ! -f "$PROJECT_ROOT/lean-toolchain" ]; then
    echo "[FAIL] No lean-toolchain found at project root."
    echo "       lean-lsp-mcp requires a valid Lake project."
    exit 1
fi

if [ ! -f "$PROJECT_ROOT/lakefile.lean" ] && [ ! -f "$PROJECT_ROOT/lakefile.toml" ]; then
    echo "[FAIL] No lakefile found at project root."
    exit 1
fi

echo "[OK] Lake project found"

# 5. Optional: check if project is built
if [ -d "$PROJECT_ROOT/.lake/build" ]; then
    echo "[OK] Project appears to be built (.lake/build exists)"
else
    echo "[WARN] Project may not be built yet. Run 'lake build' first for"
    echo "       fast LSP startup. Without it, first lean_verify call will be slow."
fi

# 6. Optional: REPL setup for lean_multi_attempt
echo ""
echo "=== Optional: REPL for fast multi-attempt ==="
if grep -q "leanprover-community/repl" "$PROJECT_ROOT/lakefile.lean" 2>/dev/null || \
   grep -q "leanprover-community/repl" "$PROJECT_ROOT/lakefile.toml" 2>/dev/null; then
    echo "[OK] REPL dependency found in lakefile"
else
    echo "[INFO] REPL not configured. lean_multi_attempt will not be available."
    echo "       To enable, add to lakefile.lean:"
    echo "         require repl from git \"https://github.com/leanprover-community/repl\" @ \"master\""
    echo "       Then run: lake build repl"
fi

echo ""
echo "=== Setup complete ==="
echo ""
echo "Usage in LeanSwarm YAML:"
echo "  mcp_servers:"
echo "    lean_lsp:"
echo "      command: uvx"
echo "      args: [lean-lsp-mcp]"
echo "      type: stdio"
echo ""
echo "The MCP server will start 'lake serve' automatically when the agent connects."
