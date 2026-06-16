#!/bin/bash
# Clean all artifacts from previous runs
# Usage: ./clean_run.sh

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "Cleaning previous run artifacts..."

# Sandbox (proof workspace)
rm -rf "$SCRIPT_DIR/Sandbox/"*
echo "  ✓ Sandbox cleared"

# Session logs
rm -rf "$SCRIPT_DIR/strataswarm/temp/sessions/"*
echo "  ✓ Session logs cleared"

# Checkpoints
rm -rf "$SCRIPT_DIR/strataswarm/temp/checkpoints/"*
rm -f "$SCRIPT_DIR/strataswarm/temp/tm_checkpoint.json"
echo "  ✓ Checkpoints cleared"

# Server logs
rm -f "$SCRIPT_DIR/strataswarm/temp/server.log"
rm -f "$SCRIPT_DIR/strataswarm/temp/nohup.log"
rm -f "$SCRIPT_DIR/strataswarm/temp/nohup.out"
echo "  ✓ Log files cleared"

echo "Done. Ready for a fresh run."
