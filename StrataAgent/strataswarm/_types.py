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
class ShardConfig:
    """Configuration for sharded (replicated) agents."""

    replicas: int = 1
    routing: str = "round_robin"  # "hash" | "round_robin" | "least_busy"
    routing_key: str | None = None  # for hash routing: key to extract from message


@dataclass
class Workspace:
    """Defines the file-system paths an agent is allowed to access."""

    read: list[str] = field(default_factory=list)   # paths agent can read
    write: list[str] = field(default_factory=list)  # paths agent can write/create
    edit: list[str] = field(default_factory=list)   # paths agent can edit


@dataclass
class AgentSpec(Generic[T]):
    name: str
    prompt: str | Path = ""
    tools: ToolSet | None = None
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
    is_super_agent: bool = False
    reply_only: bool = False
    resume_session_id: str | None = None
    workspace: Workspace | None = None
    description: str = ""
    visibility: str | dict = "all"
    child_prefix: str | None = None
    shard: ShardConfig | None = None
    max_inbound_length: int | None = None  # Max chars in messages sent TO this agent
    max_inbound_response: str | None = None  # Error shown to sender when inbound limit exceeded
    max_outbound_length: int | None = None  # Max chars in messages this agent sends
    max_outbound_response: str | None = None  # Error shown to this agent when outbound limit exceeded
    ignore_stall: bool = False  # If True, never trigger stall detection (e.g., user agent)
    stateless: bool = False  # If True, agent disconnects after first response (no persistence)
    module: str | None = None  # Python module path for custom workflow orchestration
    checkpointable: bool = False  # If True, appends handoff suffix to system prompt
    checkpoint_prompt: str | None = None  # Domain-specific handoff instructions (appended when checkpointable)
    disable_compaction: bool = False  # If True, never auto-compact — context accumulates indefinitely
    auto_start: bool = True  # If False, agent is not started by the swarm — must be launched manually
    hooks: str | None = None  # dotted path to a hook factory in modules/hooks.py (e.g. "search_agent_hooks")
    tool_error_reminder: str | None = None  # Message injected when a tool call fails (permission/workspace errors)
    _base_system_prompt: str | None = None  # Original system prompt before workspace composition


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
