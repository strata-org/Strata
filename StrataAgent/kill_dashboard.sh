#!/bin/bash
# Kill the strataswarm server and all its children
# Usage: ./kill_dashboard.sh

# Find the process listening on port 8421
SERVER_PID=$(lsof -ti :8421 2>/dev/null | head -1)

if [ -z "$SERVER_PID" ]; then
    echo "No process listening on port 8421."
    exit 0
fi

echo "Found server PID: $SERVER_PID (port 8421)"

# Kill all children of the server process (but not the server's parent)
CHILDREN=$(pgrep -P "$SERVER_PID" 2>/dev/null)
if [ -n "$CHILDREN" ]; then
    for CHILD in $CHILDREN; do
        # Recursively kill each child's tree
        pkill -TERM -P "$CHILD" 2>/dev/null
        kill "$CHILD" 2>/dev/null
    done
fi

# Kill the server itself
kill "$SERVER_PID" 2>/dev/null

# Kill orphaned lean/SwarmAgentTools that may have been spawned
pkill -f "SwarmAgentTools" 2>/dev/null
pkill -f "lean-lsp-mcp" 2>/dev/null

echo "Killed server (PID $SERVER_PID) and its children."