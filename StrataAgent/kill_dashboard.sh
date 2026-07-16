#!/bin/bash
# Kill the strataswarm server and all its children
# Usage: ./kill_dashboard.sh [port]

PORT="${1:-8421}"

# Find the process LISTENING on the port (not clients connected to it)
SERVER_PID=$(lsof -ti :"$PORT" -sTCP:LISTEN 2>/dev/null)

if [ -z "$SERVER_PID" ]; then
    echo "No server listening on port $PORT."
else
    echo "Found server PID: $SERVER_PID (port $PORT)"
    # Kill this process and its children
    CHILDREN=$(pstree -p "$SERVER_PID" 2>/dev/null | grep -oP '\(\K[0-9]+' | sort -rn)
    if [ -n "$CHILDREN" ]; then
        echo "  Killing server tree ($(echo "$CHILDREN" | wc -w) processes)..."
        echo "$CHILDREN" | xargs -r kill 2>/dev/null
    else
        echo "  Killing server PID $SERVER_PID..."
        kill "$SERVER_PID" 2>/dev/null
    fi
fi

# Kill orphaned lean/SwarmAgentTools processes
pkill -f "SwarmAgentTools" 2>/dev/null
pkill -f "lean-lsp-mcp" 2>/dev/null

echo "Done."
