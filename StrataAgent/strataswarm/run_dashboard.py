"""Start the StrataSwarm v3 dashboard on port 8421."""

import asyncio
import os
import signal
import sys
from pathlib import Path

# Ensure StrataAgent is importable
sys.path.insert(0, str(Path(__file__).parent.parent))

from strataswarm._claude_backend import ClaudeBackend
from strataswarm._server import SwarmDashboard

PORT = 8421
PID_FILE = Path(__file__).parent.parent / "temp" / "dashboard.pid"


def kill_stale_process():
    """Kill any stale dashboard process using our port or PID file."""
    if PID_FILE.exists():
        try:
            old_pid = int(PID_FILE.read_text().strip())
            os.kill(old_pid, signal.SIGTERM)
            print(f"[CLEANUP] Killed stale process {old_pid} from PID file")
            import time
            time.sleep(1)
        except (ProcessLookupError, ValueError, PermissionError):
            pass
        PID_FILE.unlink(missing_ok=True)

    try:
        import subprocess
        result = subprocess.run(
            ["lsof", "-ti", f":{PORT}"],
            capture_output=True, text=True, timeout=5
        )
        if result.stdout.strip():
            for pid_str in result.stdout.strip().split('\n'):
                try:
                    pid = int(pid_str.strip())
                    if pid != os.getpid():
                        os.kill(pid, signal.SIGTERM)
                        print(f"[CLEANUP] Killed process {pid} holding port {PORT}")
                        import time
                        time.sleep(1)
                except (ValueError, ProcessLookupError, PermissionError):
                    pass
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass


async def main() -> None:
    kill_stale_process()

    pid = os.getpid()
    PID_FILE.parent.mkdir(parents=True, exist_ok=True)
    PID_FILE.write_text(str(pid))
    print(f"StrataSwarm v3 Dashboard PID: {pid}")

    dashboard = SwarmDashboard(
        backend_factory=ClaudeBackend,
        host="0.0.0.0",
        port=PORT,
    )
    await dashboard.start()
    print(f"Dashboard running at http://localhost:{PORT}")
    print(f"Load 'swarm' from the UI to start the LeanSwarm config.")
    try:
        await asyncio.Event().wait()
    finally:
        PID_FILE.unlink(missing_ok=True)


if __name__ == "__main__":
    asyncio.run(main())
