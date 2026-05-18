from __future__ import annotations

import asyncio
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING, Any, Generic, TypeVar

if TYPE_CHECKING:
    from ._result_parsers import ResultParser
    from ._tools import ToolSet
    from ._validators import HaltValidator

T = TypeVar("T")


class AgentStatus(str, Enum):
    PENDING = "pending"
    RUNNING = "running"
    PAUSED = "paused"
    COMPLETED = "completed"
    CANCELLED = "cancelled"
    FAILED = "failed"
    HALTED = "halted"


@dataclass
class AgentSpec(Generic[T]):
    name: str
    prompt: str | Path
    tools: ToolSet
    result_parser: ResultParser[T] | None = None
    model: str | None = None
    max_turns: int | None = None
    max_budget_usd: float | None = None
    timeout_seconds: float | None = None
    halt_when: HaltValidator | None = None
    permission_mode: str = "auto"
    system_prompt: str | None = None
    mcp_servers: dict[str, Any] = field(default_factory=dict)
    inbox_channel: str | None = None


@dataclass
class AgentResult(Generic[T]):
    name: str
    output: T | None = None
    raw_result: str | None = None
    structured_output: Any = None
    cost_usd: float | None = None
    num_turns: int = 0
    session_id: str | None = None
    duration_ms: int | None = None
    halted_by: str = "completion"
    status: AgentStatus = AgentStatus.PENDING


@dataclass
class AgentEvent:
    agent_name: str
    event_type: str
    data: Any = None
    timestamp_ms: int = 0


class SwarmContext:
    def __init__(self) -> None:
        self._data: dict[str, Any] = {}
        self._lock = asyncio.Lock()

    async def get(self, key: str, default: Any = None) -> Any:
        async with self._lock:
            return self._data.get(key, default)

    async def set(self, key: str, value: Any) -> None:
        async with self._lock:
            self._data[key] = value

    async def snapshot(self) -> dict[str, Any]:
        async with self._lock:
            return dict(self._data)
