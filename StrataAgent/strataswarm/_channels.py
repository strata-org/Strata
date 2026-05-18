from __future__ import annotations

import asyncio
from dataclasses import dataclass
from typing import Any


@dataclass
class ChannelMessage:
    sender: str
    payload: Any
    topic: str = ""


class Channel:
    def __init__(self, name: str, maxsize: int = 0) -> None:
        self.name = name
        self._queue: asyncio.Queue[ChannelMessage] = asyncio.Queue(maxsize)
        self._subscribers: list[asyncio.Queue[ChannelMessage]] = []

    async def send(self, msg: ChannelMessage) -> None:
        await self._queue.put(msg)
        for sub in self._subscribers:
            await sub.put(msg)

    async def receive(self, timeout: float | None = None) -> ChannelMessage | None:
        try:
            if timeout is not None and timeout <= 0:
                return self._queue.get_nowait()
            return await asyncio.wait_for(self._queue.get(), timeout=timeout)
        except (asyncio.TimeoutError, asyncio.QueueEmpty):
            return None

    @property
    def pending_count(self) -> int:
        return self._queue.qsize()

    def peek_summary(self) -> list[tuple[str, str]]:
        """Non-destructive peek: returns (sender, topic) for each pending message."""
        return [(msg.sender, msg.topic) for msg in list(self._queue._queue)]

    def subscribe(self) -> asyncio.Queue[ChannelMessage]:
        q: asyncio.Queue[ChannelMessage] = asyncio.Queue()
        self._subscribers.append(q)
        return q

    def unsubscribe(self, q: asyncio.Queue[ChannelMessage]) -> None:
        self._subscribers.remove(q)


class ChannelBus:
    def __init__(self) -> None:
        self._channels: dict[str, Channel] = {}

    def get_or_create(self, name: str, maxsize: int = 0) -> Channel:
        if name not in self._channels:
            self._channels[name] = Channel(name, maxsize)
        return self._channels[name]

    def __getitem__(self, name: str) -> Channel:
        return self.get_or_create(name)

    async def send_to(self, channel_name: str, sender: str, payload: Any, topic: str = "") -> None:
        ch = self.get_or_create(channel_name)
        await ch.send(ChannelMessage(sender=sender, payload=payload, topic=topic))
