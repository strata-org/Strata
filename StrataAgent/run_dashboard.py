"""
Launch the StrataSwarm Dashboard.

Open http://localhost:8420 in your browser.
Add agents via the UI, then click Start.
"""

import asyncio

from strataswarm import ClaudeBackend, SwarmDashboard


async def main():
    dashboard = SwarmDashboard(
        backend_factory=lambda: ClaudeBackend(),
        port=8420,
    )
    await dashboard.start()
    print("StrataSwarm Dashboard running at http://localhost:8420")
    await asyncio.Event().wait()


if __name__ == "__main__":
    asyncio.run(main())
