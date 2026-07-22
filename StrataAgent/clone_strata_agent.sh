#!/bin/bash
# Install StrataAgent into the current Lean project.
#
# By default, downloads the StrataAgent/ folder from GitHub:
#   https://github.com/strata-org/Strata (branch: amitayush/strata-agent)
# and copies it into the current directory ($PWD), then sets it up.
#
# Optionally, pass a local path to an existing StrataAgent folder to copy from
# instead of downloading.
#
# Usage:
#   ./clone_strata_agent.sh                       # download from GitHub
#   ./clone_strata_agent.sh /path/to/StrataAgent  # copy from a local folder
#
# One-liner (download + run):
#   curl -fsSL https://raw.githubusercontent.com/strata-org/Strata/amitayush/strata-agent/StrataAgent/clone_strata_agent.sh | bash
set -e

REPO_URL="https://github.com/strata-org/Strata"
REPO_BRANCH="amitayush/strata-agent"

TARGET_REPO="$(pwd)"
DEST_DIR="$TARGET_REPO/StrataAgent"

# ─── 0. Sanity: must be a Lean project ───────────────────────────────────────
if [ ! -f "$TARGET_REPO/lakefile.toml" ] && [ ! -f "$TARGET_REPO/lakefile.lean" ]; then
  echo "Error: No lakefile.toml or lakefile.lean found in '$TARGET_REPO'."
  echo "       Run this from the root of a Lean (lake) project."
  exit 1
fi

# ─── 1. Obtain StrataAgent (local copy OR GitHub sparse checkout) ────────────
CLEANUP_TMP=""
if [ -n "$1" ]; then
  # Local source provided
  SOURCE_DIR="$(cd "$1" && pwd)"
  if [ ! -d "$SOURCE_DIR" ]; then
    echo "Error: '$SOURCE_DIR' does not exist or is not a directory."
    exit 1
  fi
  echo "=== Copying StrataAgent from local path: $SOURCE_DIR ==="
else
  # Download from GitHub via sparse checkout (only the StrataAgent/ folder)
  echo "=== Downloading StrataAgent from $REPO_URL ($REPO_BRANCH) ==="
  TMP_CLONE="$(mktemp -d)"
  CLEANUP_TMP="$TMP_CLONE"
  git clone --depth 1 --filter=blob:none --sparse --branch "$REPO_BRANCH" \
    "$REPO_URL" "$TMP_CLONE" >/dev/null 2>&1
  git -C "$TMP_CLONE" sparse-checkout set StrataAgent >/dev/null 2>&1
  SOURCE_DIR="$TMP_CLONE/StrataAgent"
  if [ ! -d "$SOURCE_DIR" ]; then
    echo "Error: StrataAgent folder not found in $REPO_URL@$REPO_BRANCH."
    [ -n "$CLEANUP_TMP" ] && rm -rf "$CLEANUP_TMP"
    exit 1
  fi
fi

# Safety: never operate when source and destination are the same path
if [ "$SOURCE_DIR" = "$DEST_DIR" ]; then
  echo "Error: Source and destination are the same path ($SOURCE_DIR)."
  echo "       Run this script from the TARGET project, not the source."
  exit 1
fi

echo "    into $DEST_DIR"
if [ -d "$DEST_DIR" ]; then
  BACKUP="$TARGET_REPO/StrataAgent.bak.$(date +%s)"
  echo "Moving existing StrataAgent to $BACKUP"
  mv "$DEST_DIR" "$BACKUP"
fi
cp -r "$SOURCE_DIR" "$DEST_DIR"
[ -n "$CLEANUP_TMP" ] && rm -rf "$CLEANUP_TMP"
echo "Copied."
echo

# ─── 2. Add StrataAgent/ to .gitignore ───────────────────────────────────────
GITIGNORE="$TARGET_REPO/.gitignore"
if [ ! -f "$GITIGNORE" ] || ! grep -qx "StrataAgent/" "$GITIGNORE"; then
  echo "StrataAgent/" >> "$GITIGNORE"
  echo "Added StrataAgent/ to .gitignore."
fi
echo

# ─── 3. Add entries to lakefile.toml ─────────────────────────────────────────
LAKEFILE="$TARGET_REPO/lakefile.toml"
if [ -f "$LAKEFILE" ]; then
  LEAN_EXE_ENTRY='[[lean_exe]]
name = "SwarmAgentTools"
root = "StrataAgent.LeanTools.Main"'

  LEAN_LIB_ENTRY='[[lean_lib]]
name = "StrataAgent"
globs = ["StrataAgent.+"]'

  add_if_missing() {
    local name="$1"
    local entry="$2"
    if grep -q "name = \"$name\"" "$LAKEFILE"; then
      echo "lakefile.toml already has '$name' — skipping."
    else
      echo "" >> "$LAKEFILE"
      echo "$entry" >> "$LAKEFILE"
      echo "Added '$name' to lakefile.toml."
    fi
  }

  echo "=== Updating lakefile.toml ==="
  add_if_missing "StrataAgent" "$LEAN_LIB_ENTRY"
  add_if_missing "SwarmAgentTools" "$LEAN_EXE_ENTRY"
  echo
  # NOTE: the optional 'repl' dependency (for lean_multi_attempt) is handled by
  # setup.sh AFTER SwarmAgentTools is built, so a repl failure can't block the
  # core Lean build.
else
  echo "Note: lakefile.lean detected (not lakefile.toml)."
  echo "      Add the StrataAgent lean_lib/lean_exe targets manually."
  echo
fi

# ─── 4. Install uv and create venv ───────────────────────────────────────────
echo "=== Setting up Python environment ==="
if ! command -v uv &> /dev/null; then
  echo "Installing uv..."
  curl -LsSf https://astral.sh/uv/install.sh | sh
  export PATH="$HOME/.local/bin:$PATH"
fi
echo "uv: $(uv --version)"

VENV="$DEST_DIR/.venv"
if [ ! -d "$VENV" ]; then
  echo "Creating venv at $VENV..."
  uv venv "$VENV"
fi
echo "Venv ready."
echo

# ─── 5. Run setup.sh ─────────────────────────────────────────────────────────
echo "=== Running StrataAgent setup ==="
find "$DEST_DIR" -name "*.sh" -exec chmod +x {} \;
if [ -f "$DEST_DIR/setup.sh" ]; then
  "$DEST_DIR/setup.sh"
else
  echo "Warning: No setup.sh found in StrataAgent — skipping setup."
fi

# ─── 6. Next steps ───────────────────────────────────────────────────────────
cat << 'EOF'

=== Done. StrataAgent is installed in this project. ===

Start the dashboard:

    ./StrataAgent/start_dashboard.sh                       # port 8421
    ./StrataAgent/start_dashboard.sh --port 9000           # custom port

Or start it and kick off a proof in one shot:

    ./StrataAgent/start_dashboard.sh --prompt "Prove the sorries in Path/To/YourFile.lean"

Then open http://localhost:8421 (Ctrl-C to stop).

Stop the dashboard:

    ./StrataAgent/kill_dashboard.sh          # default port 8421
    ./StrataAgent/kill_dashboard.sh 9000     # custom port

EOF
