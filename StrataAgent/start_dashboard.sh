#!/bin/bash
# Start the StrataSwarm dashboard, optionally sending a prompt to the TaskManager.
#
# Usage:
#   ./start_dashboard.sh                         # start on default port 8421, no cheat sheet
#   ./start_dashboard.sh --port 9000             # start on a custom port
#   ./start_dashboard.sh --cheat-sheet PATH      # start with a cheat sheet (relative to repo root)
#   ./start_dashboard.sh --prompt "Please prove the theorem foo in Bar.lean ..."
#
# By default the cheat sheet is DISABLED. Pass --cheat-sheet PATH to enable one.
# When --prompt is given, the dashboard is started, the LeanSwarm config is
# loaded and started, and the message is delivered to the TaskManager.
#
# The dashboard runs in the FOREGROUND — press Ctrl-C to stop it.
set -euo pipefail

# ─── Paths ───────────────────────────────────────────────────────────────────
STRATA_AGENT="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$STRATA_AGENT/.." && pwd)"
VENV="$STRATA_AGENT/.venv"
RUN_DASHBOARD="$STRATA_AGENT/run_dashboard.py"
SESSIONS_DIR="$STRATA_AGENT/strataswarm/temp/sessions"

# ─── Defaults ─────────────────────────────────────────────────────────────────
PORT=8421
CHEAT_SHEET=""       # empty → --no-cheat-sheet
PROMPT=""
SWARM_NAME="swarm"   # agent_specs/swarm.yaml → LeanSwarm (manager: TaskManager)
MANAGER="TaskManager"

# ─── Parse args ───────────────────────────────────────────────────────────────
while [[ $# -gt 0 ]]; do
    case "$1" in
        --port)         PORT="$2";        shift 2 ;;
        --cheat-sheet)  CHEAT_SHEET="$2"; shift 2 ;;
        --prompt)       PROMPT="$2";      shift 2 ;;
        --swarm)        SWARM_NAME="$2";  shift 2 ;;
        --manager)      MANAGER="$2";     shift 2 ;;
        -h|--help)
            # Print the leading doc comment block only (up to the first blank line).
            sed -n '2,/^$/ s/^# \{0,1\}//p' "$0"
            exit 0 ;;
        *)
            echo "ERROR: unknown argument: $1" >&2
            exit 1 ;;
    esac
done

# ─── Verify venv exists ────────────────────────────────────────────────────────
if [[ ! -f "$VENV/bin/activate" ]]; then
    echo "ERROR: virtualenv not found at $VENV" >&2
    echo "       Create it first (e.g. 'cd StrataAgent && uv venv' then './StrataAgent/setup.sh')." >&2
    exit 1
fi

# ─── Activate venv ─────────────────────────────────────────────────────────────
# shellcheck disable=SC1091
source "$VENV/bin/activate"

# ─── Build dashboard args ──────────────────────────────────────────────────────
DASH_ARGS=(--port "$PORT")
if [[ -n "$CHEAT_SHEET" ]]; then
    DASH_ARGS+=(--cheat-sheet "$CHEAT_SHEET")
    echo "[CONFIG] Cheat sheet ENABLED: $CHEAT_SHEET"
else
    DASH_ARGS+=(--no-cheat-sheet)
    echo "[CONFIG] Cheat sheet DISABLED (default)"
fi

BASE_URL="http://localhost:$PORT"

# ─── Launch dashboard (background child of this script) ────────────────────────
# cwd = repo root so relative paths (Sandbox, workspaces) resolve as project root.
cd "$REPO_ROOT"
python "$RUN_DASHBOARD" "${DASH_ARGS[@]}" &
DASH_PID=$!

# Ensure the dashboard is killed when this script exits (Ctrl-C, error, etc).
cleanup() {
    if kill -0 "$DASH_PID" 2>/dev/null; then
        kill "$DASH_PID" 2>/dev/null || true
    fi
}
trap cleanup EXIT INT TERM

# ─── Wait for the server to come up ────────────────────────────────────────────
echo "[WAIT] Waiting for dashboard on $BASE_URL ..."
for _ in $(seq 1 60); do
    if curl -sf -o /dev/null "$BASE_URL/api/state" 2>/dev/null; then
        break
    fi
    if ! kill -0 "$DASH_PID" 2>/dev/null; then
        echo "ERROR: dashboard process exited before becoming ready." >&2
        exit 1
    fi
    sleep 0.5
done

if ! curl -sf -o /dev/null "$BASE_URL/api/state" 2>/dev/null; then
    echo "ERROR: dashboard did not become ready within 30s." >&2
    exit 1
fi
echo "[READY] Dashboard is up."

# ─── Optionally load + start the swarm and message the TaskManager ─────────────
if [[ -n "$PROMPT" ]]; then
    echo "[SWARM] Loading '$SWARM_NAME' ..."
    curl -sf -X POST "$BASE_URL/api/swarm/load" \
        -H 'Content-Type: application/json' \
        -d "{\"name\": \"$SWARM_NAME\"}" >/dev/null

    echo "[SWARM] Starting ..."
    curl -sf -X POST "$BASE_URL/api/swarm/start" >/dev/null

    # Give the swarm a moment to spin up the agent loops before delivering.
    sleep 3

    echo "[SWARM] Sending prompt to $MANAGER ..."
    python - "$BASE_URL" "$MANAGER" "$PROMPT" <<'PY'
import json, sys, urllib.request
base_url, manager, prompt = sys.argv[1], sys.argv[2], sys.argv[3]
req = urllib.request.Request(
    f"{base_url}/api/agents/{manager}/message",
    data=json.dumps({"message": prompt}).encode(),
    headers={"Content-Type": "application/json"},
    method="POST",
)
with urllib.request.urlopen(req, timeout=10) as r:
    print(f"[SWARM] {r.read().decode()}")
PY
fi

# ─── Monitoring hints ──────────────────────────────────────────────────────────
cat <<EOF

────────────────────────────────────────────────────────────────────────────
 StrataSwarm dashboard running at $BASE_URL
────────────────────────────────────────────────────────────────────────────
 To monitor from your laptop, port-forward:
     ssh -N -L $PORT:localhost:$PORT <this-host>
 then open http://localhost:$PORT in your browser.

 Session logs:
     $SESSIONS_DIR
────────────────────────────────────────────────────────────────────────────
 Press Ctrl-C to stop the dashboard.
EOF

# ─── Keep the dashboard in the foreground ──────────────────────────────────────
wait "$DASH_PID"
