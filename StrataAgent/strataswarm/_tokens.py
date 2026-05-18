from __future__ import annotations

import asyncio


class CancellationToken:
    def __init__(self) -> None:
        self._event = asyncio.Event()

    @property
    def is_cancelled(self) -> bool:
        return self._event.is_set()

    def cancel(self) -> None:
        self._event.set()

    async def wait(self) -> None:
        await self._event.wait()

    def link(self, other: CancellationToken) -> None:
        async def _propagate() -> None:
            await self._event.wait()
            other.cancel()

        asyncio.ensure_future(_propagate())


class PauseToken:
    def __init__(self) -> None:
        self._gate = asyncio.Event()
        self._gate.set()

    @property
    def is_paused(self) -> bool:
        return not self._gate.is_set()

    def pause(self) -> None:
        self._gate.clear()

    def resume(self) -> None:
        self._gate.set()

    async def wait_if_paused(self) -> None:
        await self._gate.wait()
