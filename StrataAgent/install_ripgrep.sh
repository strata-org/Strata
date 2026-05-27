#!/bin/bash
# Install ripgrep (rg) — required for lean-lsp-mcp's lean_local_search and lean_verify.
# Tries multiple methods in order of preference.

set -e

echo "=== Installing ripgrep ==="

# Check if already available
if command -v rg &> /dev/null; then
    echo "[OK] ripgrep already installed: $(rg --version | head -1)"
    exit 0
fi

# Method 1: Package manager (yum/dnf/apt)
if command -v yum &> /dev/null; then
    echo "[TRY] yum install ripgrep..."
    if sudo yum install -y ripgrep 2>/dev/null; then
        echo "[OK] Installed via yum"
        exit 0
    fi
    echo "[SKIP] yum failed"
elif command -v apt-get &> /dev/null; then
    echo "[TRY] apt install ripgrep..."
    if sudo apt-get install -y ripgrep 2>/dev/null; then
        echo "[OK] Installed via apt"
        exit 0
    fi
    echo "[SKIP] apt failed"
elif command -v brew &> /dev/null; then
    echo "[TRY] brew install ripgrep..."
    if brew install ripgrep 2>/dev/null; then
        echo "[OK] Installed via brew"
        exit 0
    fi
    echo "[SKIP] brew failed"
fi

# Method 2: cargo (Rust package manager)
if command -v cargo &> /dev/null; then
    echo "[TRY] cargo install ripgrep..."
    if cargo install ripgrep 2>/dev/null; then
        echo "[OK] Installed via cargo"
        exit 0
    fi
    echo "[SKIP] cargo failed"
fi

# Method 3: Download pre-built binary
echo "[TRY] Downloading pre-built binary..."
ARCH=$(uname -m)
OS=$(uname -s | tr '[:upper:]' '[:lower:]')
if [ "$ARCH" = "x86_64" ] && [ "$OS" = "linux" ]; then
    RG_VERSION="14.1.1"
    URL="https://github.com/BurntSushi/ripgrep/releases/download/${RG_VERSION}/ripgrep-${RG_VERSION}-x86_64-unknown-linux-musl.tar.gz"
    TMPDIR=$(mktemp -d)
    if curl -sSL "$URL" | tar xz -C "$TMPDIR" 2>/dev/null; then
        mkdir -p "$HOME/.local/bin"
        cp "$TMPDIR"/ripgrep-*/rg "$HOME/.local/bin/rg"
        chmod +x "$HOME/.local/bin/rg"
        rm -rf "$TMPDIR"
        echo "[OK] Installed to ~/.local/bin/rg"
        echo "     Make sure ~/.local/bin is in your PATH"
        exit 0
    fi
    rm -rf "$TMPDIR"
    echo "[SKIP] Download failed"
fi

# Method 4: Symlink from VS Code's bundled copy
echo "[TRY] Looking for VS Code's bundled ripgrep..."
VSCODE_RG=$(find "$HOME/.vscode-server" -name "rg" -path "*/ripgrep/bin/rg" -type f 2>/dev/null | head -1)
if [ -n "$VSCODE_RG" ] && [ -x "$VSCODE_RG" ]; then
    mkdir -p "$HOME/.local/bin"
    ln -sf "$VSCODE_RG" "$HOME/.local/bin/rg"
    echo "[OK] Symlinked from VS Code: $VSCODE_RG -> ~/.local/bin/rg"
    echo "     Make sure ~/.local/bin is in your PATH"
    exit 0
fi

# Method 5: pip (Python wrapper, slower but works)
if command -v pip &> /dev/null || command -v pip3 &> /dev/null; then
    echo "[TRY] pip install ripgrep-bin..."
    if pip install ripgrep-bin 2>/dev/null || pip3 install ripgrep-bin 2>/dev/null; then
        echo "[OK] Installed via pip (ripgrep-bin)"
        exit 0
    fi
    echo "[SKIP] pip failed"
fi

echo ""
echo "[FAIL] Could not install ripgrep automatically."
echo "       Please install manually:"
echo "         - macOS: brew install ripgrep"
echo "         - Ubuntu: sudo apt install ripgrep"
echo "         - Fedora: sudo dnf install ripgrep"
echo "         - Cargo: cargo install ripgrep"
echo "         - Binary: https://github.com/BurntSushi/ripgrep/releases"
exit 1
