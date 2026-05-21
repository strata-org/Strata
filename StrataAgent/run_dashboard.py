"""
Launch the StrataSwarm Dashboard.

Open http://localhost:8420 in your browser.
Add agents via the UI, then click Start.
"""

import asyncio
import os
import time

t0 = time.time()
from strataswarm import ClaudeBackend, SwarmDashboard
print(f"[{time.time()-t0:.2f}s] imports done (PID: {os.getpid()})")


async def main():
    t1 = time.time()
    dashboard = SwarmDashboard(
        backend_factory=lambda: ClaudeBackend(),
        port=8420,
    )
    print(f"[{time.time()-t1:.2f}s] dashboard created")
    await dashboard.start()
    print(f"[{time.time()-t1:.2f}s] server started — http://localhost:8420 (PID: {os.getpid()})")
    await asyncio.Event().wait()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nShutdown.")

