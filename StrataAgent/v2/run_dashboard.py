"""Start the StrataSwarm v2 dashboard on port 8421."""

import asyncio
import os
import sys
from pathlib import Path

# Ensure the StrataAgent directory is on the path so `v2.src` is importable
sys.path.insert(0, str(Path(__file__).parent.parent))

from v2.src._claude_backend import ClaudeBackend
from v2.src._server import SwarmDashboard

PID_FILE = Path(__file__).parent / "temp" / "dashboard.pid"


async def main() -> None:
    pid = os.getpid()
    PID_FILE.parent.mkdir(parents=True, exist_ok=True)
    PID_FILE.write_text(str(pid))
    print(f"StrataSwarm v2 Dashboard PID: {pid} (written to {PID_FILE})")

    dashboard = SwarmDashboard(
        backend_factory=ClaudeBackend,
        host="0.0.0.0",
        port=8421,
    )
    await dashboard.start()
    print(f"StrataSwarm v2 Dashboard running at http://localhost:8421 (PID: {pid})")
    try:
        await asyncio.Event().wait()
    finally:
        PID_FILE.unlink(missing_ok=True)


if __name__ == "__main__":
    asyncio.run(main())
