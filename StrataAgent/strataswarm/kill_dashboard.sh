#!/bin/bash
# Kill the StrataSwarm v3 dashboard process
PID_FILE="$(dirname "$0")/../temp/dashboard.pid"
PORT=8421

if [ -f "$PID_FILE" ]; then
    PID=$(cat "$PID_FILE")
    kill "$PID" 2>/dev/null && echo "Killed dashboard (PID $PID)" || echo "PID $PID not running"
    rm -f "$PID_FILE"
fi

# Also kill anything on the port
lsof -ti :"$PORT" 2>/dev/null | xargs -r kill 2>/dev/null && echo "Killed processes on port $PORT"
