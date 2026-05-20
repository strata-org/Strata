from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import AsyncIterator
from dataclasses import dataclass, field
from typing import Any


@dataclass
class BackendMessage:
    type: str  # "text" | "tool_use" | "thinking" | "result"
    content: str | None = None
    raw_result: str | None = None
    structured_output: Any = None
    cost_usd: float | None = None
    num_turns: int = 0
    session_id: str | None = None
    duration_ms: int | None = None
    stop_reason: str | None = None


@dataclass
class BackendConfig:
    allowed_tools: list[str] = field(default_factory=list)
    disallowed_tools: list[str] = field(default_factory=list)
    permission_mode: str = "auto"
    max_turns: int | None = None
    max_budget_usd: float | None = None
    model: str | None = None
    system_prompt: str | None = None
    output_format: dict[str, Any] | None = None
    extra: dict[str, Any] | None = None


class AgentBackend(ABC):
    @abstractmethod
    async def connect(self, config: BackendConfig) -> None: ...

    @abstractmethod
    async def send_query(self, prompt: str) -> None: ...

    @abstractmethod
    def receive_messages(self) -> AsyncIterator[BackendMessage]: ...

    @abstractmethod
    async def interrupt(self) -> None: ...

    @abstractmethod
    async def disconnect(self) -> None: ...

    async def reconnect(self) -> bool:
        """Reconnect using stored session. Returns True if successful."""
        return False

    async def get_context_percentage(self) -> float | None:
        """Return context usage as 0-100 percentage. None if not supported."""
        return None

    async def compact(self) -> None:
        """Trigger context compaction. No-op if not supported."""
        pass

    async def __aenter__(self) -> AgentBackend:
        return self

    async def __aexit__(self, *exc: object) -> None:
        await self.disconnect()
