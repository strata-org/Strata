# StrataSwarm: Multi-Agent Orchestration Framework

## Context

A lightweight framework wrapping `claude_agent_sdk` behind provider-agnostic interfaces for multi-agent coordination. Agents can communicate mid-execution, be paused/cancelled cooperatively, define typed returns, and declare halting conditions via serializable validators (not lambdas). Includes a Web UI (FastAPI + WebSocket) for monitoring agent status, viewing chat history, sending feedback to individual agents, and pause/resume control.

---

## Module Structure

```
StrataAgent/
  strataswarm/
    __init__.py          Public exports (37 symbols)
    _types.py            AgentSpec, AgentResult, AgentEvent, AgentStatus, SwarmContext
    _tools.py            ToolSet abstraction (provider-agnostic allowed/disallowed)
    _tokens.py           CancellationToken, PauseToken
    _channels.py         Channel (with peek_summary), ChannelBus
    _validators.py       HaltValidator ABC (message-level + result-level halting)
    _result_parsers.py   ResultParser strategy: JsonSchema, Regex, Pydantic, Custom, Raw
    _templates.py        Jinja2 rendering (inline + file-based .j2)
    _backend.py          AgentBackend ABC (provider-agnostic LLM interface)
    _claude_backend.py   ClaudeBackend adapter (auto-resolves CLI path)
    _messaging.py        MCP tools: send_message, check_messages (via ChannelBus)
    _agent.py            SwarmAgent (emits events before pause, notification injection)
    _swarm.py            Swarm orchestrator (DAG, messaging injection, enable_messaging)
    _server.py           FastAPI + WebSocket dashboard
    _static/
      index.html         Single-page dashboard UI
  tests/
    test_claude_backend_integration.py    Backend tests (tool use, chaining, structured output)
    test_swarm_agent_integration.py       Agent tests (cancellation, pause, multi-agent)
    test_agent_channel_comms.py           Messaging tests (3-agent security scenario)
  pyproject.toml         Dependencies: claude-agent-sdk, jinja2, pydantic, fastapi, uvicorn
  .gitignore             __pycache__/, *.pyc, .venv/
```

---

## Core Abstractions

### 1. `ToolSet` — Provider-Agnostic Tool Configuration (`_tools.py`)

Abstracts tool declarations so the framework isn't tied to Claude Code's string-based tool syntax.

```python
from dataclasses import dataclass, field
from typing import Any


@dataclass(frozen=True)
class Tool:
    """A single tool declaration."""
    name: str
    pattern: str | None = None  # Optional glob/regex filter (e.g., "lake*" for Bash)

    def to_claude_format(self) -> str:
        """Serialize to Claude SDK format: 'Bash(lake*)'."""
        if self.pattern:
            return f"{self.name}({self.pattern})"
        return self.name


@dataclass
class ToolSet:
    """
    Provider-agnostic tool configuration.
    Separates allowed vs disallowed tools and provides
    serialization to any backend format.
    """
    allowed: list[Tool] = field(default_factory=list)
    disallowed: list[Tool] = field(default_factory=list)

    def allow(self, name: str, pattern: str | None = None) -> "ToolSet":
        """Fluent API: add an allowed tool."""
        self.allowed.append(Tool(name=name, pattern=pattern))
        return self

    def disallow(self, name: str, pattern: str | None = None) -> "ToolSet":
        """Fluent API: add a disallowed tool."""
        self.disallowed.append(Tool(name=name, pattern=pattern))
        return self

    def to_claude_allowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.allowed]

    def to_claude_disallowed(self) -> list[str]:
        return [t.to_claude_format() for t in self.disallowed]

    @classmethod
    def from_names(cls, *names: str) -> "ToolSet":
        """Shorthand: ToolSet.from_names('Read', 'Bash', 'Grep')"""
        return cls(allowed=[Tool(name=n) for n in names])
```

Usage:
```python
tools = (
    ToolSet()
    .allow("Read")
    .allow("Bash", pattern="lake*")
    .allow("Grep")
    .disallow("Edit", pattern="StrataAgentTest.lean")
)
```

---

### 2. `ResultParser` — Strategy Pattern for Result Parsing (`_result_parsers.py`)

Each agent declares how its final result should be parsed. The user picks a strategy per-agent.

```python
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any, Generic, TypeVar
import re
import json

from pydantic import TypeAdapter

T = TypeVar("T")


class ResultParser(ABC, Generic[T]):
    """Strategy for parsing an agent's raw result into a typed output."""

    @property
    @abstractmethod
    def name(self) -> str: ...

    @abstractmethod
    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        """Parse the result. Returns None if parsing fails."""
        ...

    def to_dict(self) -> dict[str, Any]:
        return {"type": self.name, **self._params()}

    def _params(self) -> dict[str, Any]:
        return {}


@dataclass
class JsonSchemaParser(ResultParser[T]):
    """
    Uses SDK's native output_format (JSON schema from Pydantic model).
    This tells the LLM to produce structured JSON matching the schema.
    The SDK returns it in ResultMessage.structured_output.
    """
    output_type: type[T]

    @property
    def name(self) -> str:
        return "json_schema"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        adapter = TypeAdapter(self.output_type)
        if structured_output is not None:
            return adapter.validate_python(structured_output)
        if raw_result:
            try:
                return adapter.validate_json(raw_result)
            except Exception:
                return None
        return None

    def get_output_format(self) -> dict[str, Any]:
        """Generate the output_format config for ClaudeAgentOptions."""
        adapter = TypeAdapter(self.output_type)
        return {"type": "json_schema", "schema": adapter.json_schema()}

    def _params(self) -> dict[str, Any]:
        return {"output_type": self.output_type.__name__}


@dataclass
class RegexParser(ResultParser[dict[str, str]]):
    """
    Extract named groups from raw_result using a regex pattern.
    Returns a dict of group_name -> matched_value.
    """
    pattern: str
    flags: int = 0

    @property
    def name(self) -> str:
        return "regex"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> dict[str, str] | None:
        if not raw_result:
            return None
        match = re.search(self.pattern, raw_result, self.flags)
        if match:
            return match.groupdict()
        return None

    def _params(self) -> dict[str, Any]:
        return {"pattern": self.pattern}


@dataclass
class PydanticFromTextParser(ResultParser[T]):
    """
    Parse raw text result as JSON into a Pydantic model.
    Unlike JsonSchemaParser, this does NOT constrain the LLM's output format—
    it just tries to find and parse JSON from the text after the fact.
    """
    output_type: type[T]

    @property
    def name(self) -> str:
        return "pydantic_from_text"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        if not raw_result:
            return None
        adapter = TypeAdapter(self.output_type)
        # Try to find JSON block in the text
        json_match = re.search(r'```json\s*(.*?)\s*```', raw_result, re.DOTALL)
        text_to_parse = json_match.group(1) if json_match else raw_result
        try:
            return adapter.validate_json(text_to_parse)
        except Exception:
            return None

    def _params(self) -> dict[str, Any]:
        return {"output_type": self.output_type.__name__}


@dataclass
class CustomParser(ResultParser[T]):
    """
    User provides a callable for custom parsing logic.
    The callable must be importable (not a lambda) for serialization.
    """
    parse_fn: callable  # (raw_result, structured_output) -> T | None
    parser_name: str = "custom"

    @property
    def name(self) -> str:
        return self.parser_name

    def parse(self, raw_result: str | None, structured_output: Any | None) -> T | None:
        return self.parse_fn(raw_result, structured_output)

    def _params(self) -> dict[str, Any]:
        return {"parser_name": self.parser_name}


class RawTextParser(ResultParser[str]):
    """No parsing — just return raw text as-is."""

    @property
    def name(self) -> str:
        return "raw_text"

    def parse(self, raw_result: str | None, structured_output: Any | None) -> str | None:
        return raw_result
```

Usage in AgentSpec:
```python
checker = AgentSpec(
    name="checker",
    prompt="...",
    tools=ToolSet().allow("Read"),
    result_parser=JsonSchemaParser(output_type=ProofResult),  # Strategy choice
    ...
)

# Or regex extraction:
log_agent = AgentSpec(
    name="log-parser",
    prompt="...",
    tools=ToolSet().allow("Bash"),
    result_parser=RegexParser(pattern=r"ERROR: (?P<error>.+)\nLINE: (?P<line>\d+)"),
)
```

---

### 3. `HaltValidator` Registry — Serializable Halting Conditions (`_validators.py`)

Replaces lambdas with named, serializable validator classes. Validators can inspect both in-flight messages AND the final parsed result. They are composable.

```python
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any


class HaltValidator(ABC):
    """Base class for serializable halt conditions.
    
    Two evaluation points:
    - should_halt_on_messages(): checked per-message during streaming
    - should_halt_on_result(): checked AFTER result parsing (final gate)
    """

    @property
    @abstractmethod
    def name(self) -> str: ...

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        """Check during message streaming. Default: no halt."""
        return False

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        """Check after final result is parsed. Default: no halt."""
        return False

    def to_dict(self) -> dict[str, Any]:
        return {"type": self.name, **self._params()}

    def _params(self) -> dict[str, Any]:
        return {}


@dataclass
class ContainsText(HaltValidator):
    """Halt when any message contains the given text (checked during streaming)."""
    text: str
    case_sensitive: bool = True

    @property
    def name(self) -> str:
        return "contains_text"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        target = self.text if self.case_sensitive else self.text.lower()
        for msg in messages:
            content = str(msg)
            if not self.case_sensitive:
                content = content.lower()
            if target in content:
                return True
        return False

    def _params(self) -> dict[str, Any]:
        return {"text": self.text, "case_sensitive": self.case_sensitive}


@dataclass
class MessageCount(HaltValidator):
    """Halt after N messages received."""
    max_messages: int

    @property
    def name(self) -> str:
        return "message_count"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return len(messages) >= self.max_messages

    def _params(self) -> dict[str, Any]:
        return {"max_messages": self.max_messages}


@dataclass
class ResultFieldEquals(HaltValidator):
    """Halt (post-parse) when parsed result has a field matching expected value."""
    field_name: str
    expected_value: Any

    @property
    def name(self) -> str:
        return "result_field_equals"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        if parsed_result is None:
            return False
        if isinstance(parsed_result, dict):
            return parsed_result.get(self.field_name) == self.expected_value
        return getattr(parsed_result, self.field_name, None) == self.expected_value

    def _params(self) -> dict[str, Any]:
        return {"field_name": self.field_name, "expected_value": self.expected_value}


@dataclass
class ResultFieldTruthy(HaltValidator):
    """Halt (post-parse) when a field on the parsed result is truthy."""
    field_name: str

    @property
    def name(self) -> str:
        return "result_field_truthy"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        if parsed_result is None:
            return False
        if isinstance(parsed_result, dict):
            return bool(parsed_result.get(self.field_name))
        return bool(getattr(parsed_result, self.field_name, None))

    def _params(self) -> dict[str, Any]:
        return {"field_name": self.field_name}


@dataclass
class ResultTextContains(HaltValidator):
    """Halt (post-parse) when the raw result text contains a substring."""
    text: str

    @property
    def name(self) -> str:
        return "result_text_contains"

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return raw_result is not None and self.text in raw_result

    def _params(self) -> dict[str, Any]:
        return {"text": self.text}


@dataclass
class AnyOf(HaltValidator):
    """Halt when ANY sub-validator triggers (at either evaluation point)."""
    validators: list[HaltValidator] = field(default_factory=list)

    @property
    def name(self) -> str:
        return "any_of"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return any(v.should_halt_on_messages(messages) for v in self.validators)

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return any(v.should_halt_on_result(parsed_result, raw_result) for v in self.validators)

    def _params(self) -> dict[str, Any]:
        return {"validators": [v.to_dict() for v in self.validators]}


@dataclass
class AllOf(HaltValidator):
    """Halt when ALL sub-validators trigger."""
    validators: list[HaltValidator] = field(default_factory=list)

    @property
    def name(self) -> str:
        return "all_of"

    def should_halt_on_messages(self, messages: list[Any]) -> bool:
        return all(v.should_halt_on_messages(messages) for v in self.validators)

    def should_halt_on_result(self, parsed_result: Any, raw_result: str | None) -> bool:
        return all(v.should_halt_on_result(parsed_result, raw_result) for v in self.validators)

    def _params(self) -> dict[str, Any]:
        return {"validators": [v.to_dict() for v in self.validators]}
```

**Result-based halting flow in the agent:**
```
1. Stream messages → check should_halt_on_messages() per message
2. On ResultMessage → parse via ResultParser
3. After parsing → check should_halt_on_result(parsed, raw)
4. If result halt triggers → mark halted_by="predicate", don't continue multi-turn loop
```

---

### 4. `AgentSpec[T]` — Declarative Agent Definition (`_types.py`)

```python
from dataclasses import dataclass, field
from typing import Any, Generic, TypeVar
from pathlib import Path
from enum import Enum

T = TypeVar("T")


class AgentStatus(str, Enum):
    """Observable status of a running agent."""
    PENDING = "pending"        # Waiting for dependencies
    RUNNING = "running"        # Actively executing
    PAUSED = "paused"          # Paused by user/orchestrator
    COMPLETED = "completed"    # Finished successfully
    CANCELLED = "cancelled"    # Cancelled externally
    FAILED = "failed"          # Error or timeout
    HALTED = "halted"          # Stopped by halt validator


@dataclass
class AgentSpec(Generic[T]):
    """Declarative specification for a swarm agent."""
    name: str
    prompt: str | Path                     # Inline Jinja2, plain string, or .j2 file path
    tools: "ToolSet"                       # Provider-agnostic tool config
    result_parser: "ResultParser[T] | None" = None  # Strategy for parsing output
    model: str | None = None
    max_turns: int | None = None
    max_budget_usd: float | None = None
    timeout_seconds: float | None = None   # Wall-clock timeout
    halt_when: "HaltValidator | None" = None  # Serializable halting condition
    permission_mode: str = "auto"
    system_prompt: str | None = None
    mcp_servers: dict[str, Any] = field(default_factory=dict)
    inbox_channel: str | None = None       # Channel for mid-run messages


@dataclass
class AgentResult(Generic[T]):
    """Result produced by an agent after execution."""
    name: str
    output: T | None = None           # Parsed result (via result_parser)
    raw_result: str | None = None     # Raw text from ResultMessage
    structured_output: Any = None     # Raw structured_output from SDK
    cost_usd: float | None = None
    num_turns: int = 0
    session_id: str | None = None     # For resuming or viewing history
    duration_ms: int | None = None
    halted_by: str = "completion"     # "completion"|"max_turns"|"budget"|"cancelled"|"predicate"|"dependency"|"timeout"
    status: "AgentStatus" = AgentStatus.PENDING


@dataclass
class AgentEvent:
    """Real-time event emitted by an agent for the UI/observers."""
    agent_name: str
    event_type: str  # "status_change"|"message"|"result"|"error"|"cost_update"
    data: Any = None
    timestamp_ms: int = 0
```

---

### 5. `CancellationToken` and `PauseToken` (`_tokens.py`)

```python
import asyncio


class CancellationToken:
    """Cooperative cancellation. Shared across agent groups."""
    def __init__(self) -> None:
        self._event = asyncio.Event()

    @property
    def is_cancelled(self) -> bool:
        return self._event.is_set()

    def cancel(self) -> None:
        self._event.set()

    async def wait(self) -> None:
        await self._event.wait()

    def link(self, other: "CancellationToken") -> None:
        """Propagate: when self cancels, also cancel other."""
        async def _propagate():
            await self._event.wait()
            other.cancel()
        asyncio.ensure_future(_propagate())


class PauseToken:
    """Gate for pause/resume. Set = running, clear = paused."""
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
```

---

### 6. `Channel` + `ChannelBus` — Inter-Agent Communication (`_channels.py`)

```python
import asyncio
from dataclasses import dataclass
from typing import Any


@dataclass
class ChannelMessage:
    """A message between agents."""
    sender: str
    payload: Any
    topic: str = ""


class Channel:
    """Named async queue with pub/sub support."""
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

    def subscribe(self) -> asyncio.Queue[ChannelMessage]:
        q: asyncio.Queue[ChannelMessage] = asyncio.Queue()
        self._subscribers.append(q)
        return q

    def unsubscribe(self, q: asyncio.Queue[ChannelMessage]) -> None:
        self._subscribers.remove(q)


class ChannelBus:
    """Registry of named channels."""
    def __init__(self) -> None:
        self._channels: dict[str, Channel] = {}

    def get_or_create(self, name: str, maxsize: int = 0) -> Channel:
        if name not in self._channels:
            self._channels[name] = Channel(name, maxsize)
        return self._channels[name]

    def __getitem__(self, name: str) -> Channel:
        return self.get_or_create(name)

    async def send_to(self, channel_name: str, sender: str, payload: Any, topic: str = "") -> None:
        """Convenience: send a message to a named channel."""
        ch = self.get_or_create(channel_name)
        await ch.send(ChannelMessage(sender=sender, payload=payload, topic=topic))
```

---

### 7. `_templates.py` — Jinja2 Template Loading

```python
from pathlib import Path
from typing import Any
from jinja2 import Template, Environment, FileSystemLoader


def render_prompt(prompt: str | Path, variables: dict[str, Any]) -> str:
    """
    Render a prompt from:
    - Path to .j2/.jinja2 file -> load and render
    - Inline string with {{ or {% -> Jinja2 render
    - Plain string -> return as-is
    """
    if isinstance(prompt, Path) or (
        isinstance(prompt, str) and (prompt.endswith(".j2") or prompt.endswith(".jinja2"))
    ):
        path = Path(prompt)
        if path.exists():
            env = Environment(loader=FileSystemLoader(str(path.parent)))
            tmpl = env.get_template(path.name)
            return tmpl.render(**variables)
        raise FileNotFoundError(f"Template not found: {path}")

    if isinstance(prompt, str) and ("{{" in prompt or "{%" in prompt):
        tmpl = Template(prompt)
        return tmpl.render(**variables)

    return str(prompt)
```

---

### 8. `AgentBackend` Protocol — LLM Provider Interface (`_backend.py`)

The `SwarmAgent` does NOT import `claude_agent_sdk` directly. Instead it programs against this abstract interface. A `ClaudeBackend` adapter (in a separate file) implements it.

```python
from abc import ABC, abstractmethod
from collections.abc import AsyncIterator
from dataclasses import dataclass
from typing import Any


@dataclass
class BackendMessage:
    """Provider-agnostic message from the LLM backend."""
    type: str  # "text" | "tool_use" | "thinking" | "result"
    content: str | None = None
    # Result-specific fields (populated when type == "result")
    raw_result: str | None = None
    structured_output: Any = None
    cost_usd: float | None = None
    num_turns: int = 0
    session_id: str | None = None
    duration_ms: int | None = None
    stop_reason: str | None = None  # "max_turns" | "budget" | "end_turn" | etc.


@dataclass
class BackendConfig:
    """Provider-agnostic configuration passed to the backend."""
    allowed_tools: list[str]
    disallowed_tools: list[str]
    permission_mode: str = "auto"
    max_turns: int | None = None
    max_budget_usd: float | None = None
    model: str | None = None
    system_prompt: str | None = None
    output_format: dict[str, Any] | None = None  # JSON schema for structured output
    extra: dict[str, Any] = None  # Provider-specific options


class AgentBackend(ABC):
    """
    Abstract LLM backend that SwarmAgent programs against.
    Each provider (Claude, OpenAI, etc.) implements this interface.
    """

    @abstractmethod
    async def connect(self, config: BackendConfig) -> None:
        """Initialize the backend connection with the given config."""
        ...

    @abstractmethod
    async def send_query(self, prompt: str) -> None:
        """Send a query/message to the LLM."""
        ...

    @abstractmethod
    def receive_messages(self) -> AsyncIterator[BackendMessage]:
        """Async generator yielding messages until the response is complete."""
        ...

    @abstractmethod
    async def interrupt(self) -> None:
        """Signal the backend to stop the current response."""
        ...

    @abstractmethod
    async def disconnect(self) -> None:
        """Clean up resources."""
        ...

    async def __aenter__(self) -> "AgentBackend":
        return self

    async def __aexit__(self, *exc) -> None:
        await self.disconnect()
```

---

### 8b. `ClaudeBackend` — Claude SDK Adapter (`_claude_backend.py`)

```python
from collections.abc import AsyncIterator
from typing import Any

from claude_agent_sdk import (
    ClaudeSDKClient,
    ClaudeAgentOptions,
    AssistantMessage,
    ResultMessage,
    TextBlock,
    ThinkingBlock,
    ToolUseBlock,
)

from ._backend import AgentBackend, BackendConfig, BackendMessage


class ClaudeBackend(AgentBackend):
    """Adapter from AgentBackend interface to claude_agent_sdk."""

    def __init__(self, cli_path: str | None = None) -> None:
        self._cli_path = cli_path
        self._client: ClaudeSDKClient | None = None

    async def connect(self, config: BackendConfig) -> None:
        opts_kwargs: dict[str, Any] = {
            "allowed_tools": config.allowed_tools,
            "disallowed_tools": config.disallowed_tools,
            "permission_mode": config.permission_mode,
        }
        if config.max_turns:
            opts_kwargs["max_turns"] = config.max_turns
        if config.max_budget_usd:
            opts_kwargs["max_budget_usd"] = config.max_budget_usd
        if config.model:
            opts_kwargs["model"] = config.model
        if config.system_prompt:
            opts_kwargs["system_prompt"] = config.system_prompt
        if config.output_format:
            opts_kwargs["output_format"] = config.output_format
        if self._cli_path:
            opts_kwargs["cli_path"] = self._cli_path
        if config.extra:
            if "mcp_servers" in config.extra:
                opts_kwargs["mcp_servers"] = config.extra["mcp_servers"]

        options = ClaudeAgentOptions(**opts_kwargs)
        self._client = ClaudeSDKClient(options=options)
        await self._client.connect()

    async def send_query(self, prompt: str) -> None:
        await self._client.query(prompt)

    async def receive_messages(self) -> AsyncIterator[BackendMessage]:
        async for message in self._client.receive_response():
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        yield BackendMessage(type="text", content=block.text)
                    elif isinstance(block, ThinkingBlock):
                        yield BackendMessage(type="thinking", content=block.thinking)
                    elif isinstance(block, ToolUseBlock):
                        yield BackendMessage(type="tool_use", content=f"{block.name}({block.input})")
            elif isinstance(message, ResultMessage):
                yield BackendMessage(
                    type="result",
                    raw_result=message.result,
                    structured_output=message.structured_output,
                    cost_usd=message.total_cost_usd,
                    num_turns=message.num_turns,
                    session_id=message.session_id,
                    duration_ms=message.duration_ms,
                    stop_reason=message.stop_reason or (
                        "budget" if message.subtype and "budget" in message.subtype else None
                    ),
                )

    async def interrupt(self) -> None:
        if self._client:
            await self._client.interrupt()

    async def disconnect(self) -> None:
        if self._client:
            await self._client.disconnect()
            self._client = None
```

---

### 8c. `SwarmAgent[T]` — Running Agent with Multi-Turn Injection (`_agent.py`)

Now programs against `AgentBackend`, not Claude SDK directly.

```python
import asyncio
import time
from typing import Any, Generic, TypeVar
from collections.abc import Callable, Awaitable

from ._backend import AgentBackend, BackendConfig, BackendMessage
from ._types import AgentSpec, AgentResult, AgentEvent, AgentStatus
from ._result_parsers import ResultParser, JsonSchemaParser
from ._tools import ToolSet
from ._tokens import CancellationToken, PauseToken
from ._channels import ChannelBus, ChannelMessage
from ._templates import render_prompt

T = TypeVar("T")

EventCallback = Callable[[AgentEvent], Awaitable[None]]


class SwarmAgent(Generic[T]):
    """
    Running agent instance. Programs against AgentBackend interface.
    - Multi-turn loop (inbox channel injection between turns)
    - Cancellation/pause tokens checked per-message
    - Messages emitted to UI BEFORE entering pause gate
    - Serializable halt validators (message-level AND result-level)
    - Result parsing via strategy pattern
    - Wall-clock timeout
    """

    def __init__(
        self,
        spec: AgentSpec[T],
        backend: AgentBackend,
        channel_bus: ChannelBus,
        cancellation: CancellationToken,
        pause: PauseToken,
        render_vars: dict[str, Any] | None = None,
        on_event: EventCallback | None = None,
    ) -> None:
        self.spec = spec
        self.backend = backend
        self.channel_bus = channel_bus
        self.cancellation = cancellation
        self.pause = pause
        self._render_vars = render_vars or {}
        self._messages: list[BackendMessage] = []
        self._on_event = on_event

    async def _emit(self, event_type: str, data: Any = None) -> None:
        if self._on_event:
            event = AgentEvent(
                agent_name=self.spec.name,
                event_type=event_type,
                data=data,
                timestamp_ms=int(time.time() * 1000),
            )
            await self._on_event(event)

    def _build_config(self) -> BackendConfig:
        output_format = None
        if isinstance(self.spec.result_parser, JsonSchemaParser):
            output_format = self.spec.result_parser.get_output_format()

        return BackendConfig(
            allowed_tools=self.spec.tools.to_claude_allowed(),
            disallowed_tools=self.spec.tools.to_claude_disallowed(),
            permission_mode=self.spec.permission_mode,
            max_turns=self.spec.max_turns,
            max_budget_usd=self.spec.max_budget_usd,
            model=self.spec.model,
            system_prompt=self.spec.system_prompt,
            output_format=output_format,
            extra={"mcp_servers": self.spec.mcp_servers} if self.spec.mcp_servers else None,
        )

    async def run(self) -> AgentResult[T]:
        prompt = render_prompt(self.spec.prompt, self._render_vars)
        config = self._build_config()
        result = AgentResult[T](name=self.spec.name, status=AgentStatus.PENDING)
        start_time = time.monotonic()

        if self.cancellation.is_cancelled:
            result.halted_by = "cancelled"
            result.status = AgentStatus.CANCELLED
            await self._emit("status_change", AgentStatus.CANCELLED)
            return result

        await self.pause.wait_if_paused()

        result.status = AgentStatus.RUNNING
        await self._emit("status_change", AgentStatus.RUNNING)

        inbox_channel = self.spec.inbox_channel or f"{self.spec.name}:inbox"

        # Connect to the abstract backend
        await self.backend.connect(config)

        try:
            await self.backend.send_query(prompt)

            # Multi-turn loop
            while True:
                async for message in self.backend.receive_messages():
                    # Timeout check
                    if self.spec.timeout_seconds:
                        elapsed = time.monotonic() - start_time
                        if elapsed >= self.spec.timeout_seconds:
                            await self.backend.interrupt()
                            result.halted_by = "timeout"
                            result.status = AgentStatus.FAILED
                            result.duration_ms = int(elapsed * 1000)
                            await self._emit("status_change", AgentStatus.FAILED)
                            return result

                    # Cancellation check
                    if self.cancellation.is_cancelled:
                        await self.backend.interrupt()
                        result.halted_by = "cancelled"
                        result.status = AgentStatus.CANCELLED
                        await self._emit("status_change", AgentStatus.CANCELLED)
                        return result

                    self._messages.append(message)

                    # === EMIT MESSAGE TO UI FIRST (before pause gate) ===
                    if message.type == "text" and message.content:
                        await self._emit("message", message.content)
                    elif message.type == "tool_use" and message.content:
                        await self._emit("message", f"[tool] {message.content}")

                    # === THEN check pause (user sees the message, then agent pauses) ===
                    if self.pause.is_paused:
                        result.status = AgentStatus.PAUSED
                        await self._emit("status_change", AgentStatus.PAUSED)
                    await self.pause.wait_if_paused()
                    if result.status == AgentStatus.PAUSED:
                        result.status = AgentStatus.RUNNING
                        await self._emit("status_change", AgentStatus.RUNNING)

                    # Message-level halt check
                    if self.spec.halt_when and self.spec.halt_when.should_halt_on_messages(self._messages):
                        await self.backend.interrupt()
                        result.halted_by = "predicate"
                        result.status = AgentStatus.HALTED
                        await self._emit("status_change", AgentStatus.HALTED)
                        break

                    # Process result message
                    if message.type == "result":
                        result.raw_result = message.raw_result
                        result.structured_output = message.structured_output
                        result.cost_usd = message.cost_usd
                        result.num_turns = message.num_turns
                        result.session_id = message.session_id
                        result.duration_ms = message.duration_ms
                        await self._emit("cost_update", message.cost_usd)

                        # Parse result via strategy
                        if self.spec.result_parser:
                            result.output = self.spec.result_parser.parse(
                                message.raw_result, message.structured_output
                            )

                        # Result-level halt check
                        if self.spec.halt_when and self.spec.halt_when.should_halt_on_result(
                            result.output, result.raw_result
                        ):
                            result.halted_by = "predicate"
                            result.status = AgentStatus.HALTED
                            await self._emit("status_change", AgentStatus.HALTED)
                            break

                        if message.stop_reason == "max_turns":
                            result.halted_by = "max_turns"
                        elif message.stop_reason == "budget":
                            result.halted_by = "budget"

                # Exit multi-turn loop?
                if result.halted_by != "completion" or self.cancellation.is_cancelled:
                    break

                # Check inbox for inter-agent / user messages (mid-turn injection)
                inbox = self.channel_bus[inbox_channel]
                injected_msg = await inbox.receive(timeout=0.1)
                if injected_msg:
                    injection = f"[Message from '{injected_msg.sender}']: {injected_msg.payload}"
                    await self.backend.send_query(injection)
                    await self._emit("message", f"[Injected from {injected_msg.sender}]: {injected_msg.payload}")
                else:
                    break  # No pending messages, done

        finally:
            await self.backend.disconnect()

        # Final status
        if result.status == AgentStatus.RUNNING:
            result.status = AgentStatus.COMPLETED
            await self._emit("status_change", AgentStatus.COMPLETED)

        # Publish to output channel
        out_ch = self.channel_bus.get_or_create(f"{self.spec.name}:result")
        await out_ch.send(ChannelMessage(sender=self.spec.name, payload=result))
        await self._emit("result", {"output": str(result.output), "halted_by": result.halted_by})

        return result
```

**Key design points:**
- `SwarmAgent` takes an `AgentBackend` instance (injected by the Swarm orchestrator)
- No `claude_agent_sdk` import in `_agent.py` — fully decoupled
- **Message emitted to UI BEFORE pause gate**: the user always sees what the agent just produced, THEN it pauses. This gives a clear picture of where the agent stopped.
- `BackendMessage` is the only message type the agent sees (provider-agnostic)

---

### 9. `Swarm` — Orchestrator (`_swarm.py`)

```python
import asyncio
from collections.abc import Callable, Awaitable
from dataclasses import dataclass, field
from typing import Any, TypeVar

from ._types import AgentSpec, AgentResult, AgentEvent, AgentStatus, SwarmContext
from ._tokens import CancellationToken, PauseToken
from ._channels import ChannelBus
from ._agent import SwarmAgent, EventCallback

T = TypeVar("T")


class ExecutionMode:
    AWAIT_ALL = "all"
    AWAIT_FIRST = "first"
    FIRE_FORGET = "forget"


@dataclass
class AgentNode:
    spec: AgentSpec[Any]
    depends_on: list[str] = field(default_factory=list)
    render_vars: dict[str, Any] = field(default_factory=dict)


class SwarmContext:
    """Shared mutable state accessible by all agents."""
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


class Swarm:
    """
    Orchestrator coordinating multiple agents as async tasks.
    Supports DAG dependencies, shared context, inter-agent messaging,
    per-agent pause/cancel, event emission for UI, and multiple execution modes.
    """

    def __init__(
        self,
        backend_factory: Callable[[], AgentBackend],  # Factory creates one backend per agent
        context: SwarmContext | None = None,
        enable_messaging: bool = True,  # Auto-inject send_message/check_messages tools
    ) -> None:
        self._nodes: dict[str, AgentNode] = {}
        self._results: dict[str, AgentResult[Any]] = {}
        self._tasks: dict[str, asyncio.Task[AgentResult[Any]]] = {}
        self._cancellation = CancellationToken()
        self._pause_tokens: dict[str, PauseToken] = {}
        self._channel_bus = ChannelBus()
        self._context = context or SwarmContext()
        self._backend_factory = backend_factory
        self._event_callback: EventCallback | None = None
        self._enable_messaging = enable_messaging

    @property
    def context(self) -> SwarmContext:
        return self._context

    @property
    def channels(self) -> ChannelBus:
        return self._channel_bus

    @property
    def results(self) -> dict[str, AgentResult[Any]]:
        return dict(self._results)

    def set_event_callback(self, callback: EventCallback) -> None:
        """Register a callback for agent events (used by SwarmDashboard)."""
        self._event_callback = callback

    def add(
        self,
        spec: AgentSpec[Any],
        depends_on: list[str] | None = None,
        render_vars: dict[str, Any] | None = None,
    ) -> "Swarm":
        node = AgentNode(
            spec=spec,
            depends_on=depends_on or [],
            render_vars=render_vars or {},
        )
        self._nodes[spec.name] = node
        self._pause_tokens[spec.name] = PauseToken()
        return self

    def cancel(self) -> None:
        self._cancellation.cancel()

    def cancel_agent(self, name: str) -> None:
        """Cancel a specific agent's task."""
        if name in self._tasks:
            self._tasks[name].cancel()

    def pause(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].pause()

    def resume(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].resume()

    async def send_to_agent(self, agent_name: str, sender: str, payload: Any) -> None:
        """Send a message to an agent's inbox for mid-turn injection."""
        inbox = f"{agent_name}:inbox"
        await self._channel_bus.send_to(inbox, sender=sender, payload=payload)

    def get_agent_session_id(self, agent_name: str) -> str | None:
        """Get session_id for a completed/running agent (useful for manual resume)."""
        if agent_name in self._results:
            return self._results[agent_name].session_id
        return None

    async def _run_node(self, name: str) -> AgentResult[Any]:
        node = self._nodes[name]

        # Wait for dependencies
        if node.depends_on:
            dep_tasks = [self._tasks[dep] for dep in node.depends_on if dep in self._tasks]
            if dep_tasks:
                await asyncio.gather(*dep_tasks, return_exceptions=True)
                for dep_name in node.depends_on:
                    if dep_name in self._results:
                        dep_result = self._results[dep_name]
                        if dep_result.halted_by == "cancelled":
                            result = AgentResult(name=name, halted_by="dependency")
                            result.status = AgentStatus.CANCELLED
                            self._results[name] = result
                            return result

        # Build render vars: node-specific + dependency results + context
        render_vars = dict(node.render_vars)
        for dep_name in node.depends_on:
            if dep_name in self._results:
                render_vars[dep_name] = self._results[dep_name]
        render_vars["context"] = await self._context.snapshot()

        # Create backend instance (injected, not hardcoded)
        backend = self._backend_factory()

        agent = SwarmAgent(
            spec=node.spec,
            backend=backend,
            channel_bus=self._channel_bus,
            cancellation=self._cancellation,
            pause=self._pause_tokens[name],
            render_vars=render_vars,
            on_event=self._event_callback,  # Pass UI event callback
        )

        result = await agent.run()
        self._results[name] = result
        await self._context.set(f"result:{name}", result)
        return result

    async def run(self, mode: str = ExecutionMode.AWAIT_ALL) -> dict[str, AgentResult[Any]]:
        # Launch all tasks (each internally waits for its deps)
        for name in self._nodes:
            task = asyncio.create_task(self._run_node(name), name=f"swarm:{name}")
            self._tasks[name] = task

        if mode == ExecutionMode.AWAIT_ALL:
            await asyncio.gather(*self._tasks.values(), return_exceptions=True)

        elif mode == ExecutionMode.AWAIT_FIRST:
            done, pending = await asyncio.wait(
                self._tasks.values(), return_when=asyncio.FIRST_COMPLETED
            )
            self._cancellation.cancel()
            for t in pending:
                t.cancel()
                try:
                    await t
                except asyncio.CancelledError:
                    pass

        elif mode == ExecutionMode.FIRE_FORGET:
            pass  # Tasks running; caller manages lifecycle

        return dict(self._results)
```

---

---

### 10. Web UI — FastAPI + WebSocket Dashboard (`_server.py`)

A lightweight web server for observing and controlling the swarm in real-time.

```python
import asyncio
import json
from typing import Any
from pathlib import Path

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from fastapi.staticfiles import StaticFiles

from ._types import AgentEvent, AgentStatus, AgentResult
from ._swarm import Swarm


class SwarmDashboard:
    """
    FastAPI-based dashboard for monitoring and controlling a swarm.
    
    Features:
    - Real-time agent status via WebSocket
    - Chat/message history per agent (streamed)
    - User can send feedback to specific agents (pauses agent, injects message, resumes)
    - Pause/resume/cancel controls per agent
    - Session ID display for each agent (for manual CLI resume)
    """

    def __init__(self, swarm: Swarm, host: str = "0.0.0.0", port: int = 8420) -> None:
        self.swarm = swarm
        self.host = host
        self.port = port
        self.app = FastAPI(title="StrataSwarm Dashboard")
        self._connections: list[WebSocket] = []
        self._event_history: dict[str, list[AgentEvent]] = {}  # per-agent event log
        self._setup_routes()

    def _setup_routes(self) -> None:
        static_dir = Path(__file__).parent / "_static"

        @self.app.get("/")
        async def index():
            return HTMLResponse((static_dir / "index.html").read_text())

        @self.app.websocket("/ws")
        async def websocket_endpoint(ws: WebSocket):
            await ws.accept()
            self._connections.append(ws)
            # Send current state snapshot
            await ws.send_json(self._get_state_snapshot())
            try:
                while True:
                    data = await ws.receive_json()
                    await self._handle_client_message(data)
            except WebSocketDisconnect:
                self._connections.remove(ws)

        @self.app.get("/api/agents")
        async def list_agents():
            return self._get_state_snapshot()

        @self.app.get("/api/agents/{name}/history")
        async def agent_history(name: str):
            return self._event_history.get(name, [])

        @self.app.post("/api/agents/{name}/pause")
        async def pause_agent(name: str):
            self.swarm.pause(name)
            return {"status": "paused"}

        @self.app.post("/api/agents/{name}/resume")
        async def resume_agent(name: str):
            self.swarm.resume(name)
            return {"status": "resumed"}

        @self.app.post("/api/agents/{name}/cancel")
        async def cancel_agent(name: str):
            self.swarm.cancel_agent(name)
            return {"status": "cancelled"}

        @self.app.post("/api/agents/{name}/message")
        async def send_message(name: str, body: dict):
            """Send user feedback to a running agent. Pauses, injects, resumes."""
            message = body.get("message", "")
            # Inject via the agent's inbox channel
            await self.swarm.send_to_agent(name, sender="user", payload=message)
            return {"status": "sent"}

    async def _handle_client_message(self, data: dict[str, Any]) -> None:
        """Handle WebSocket messages from the UI."""
        action = data.get("action")
        agent_name = data.get("agent")

        if action == "pause" and agent_name:
            self.swarm.pause(agent_name)
        elif action == "resume" and agent_name:
            self.swarm.resume(agent_name)
        elif action == "cancel" and agent_name:
            self.swarm.cancel_agent(agent_name)
        elif action == "send_message" and agent_name:
            await self.swarm.send_to_agent(
                agent_name, sender="user", payload=data.get("message", "")
            )
        elif action == "cancel_all":
            self.swarm.cancel()

    def _get_state_snapshot(self) -> dict[str, Any]:
        """Current state of all agents."""
        agents = {}
        for name, result in self.swarm.results.items():
            agents[name] = {
                "name": name,
                "status": result.status.value if hasattr(result, 'status') else "unknown",
                "session_id": result.session_id,
                "cost_usd": result.cost_usd,
                "num_turns": result.num_turns,
                "halted_by": result.halted_by,
            }
        # Also include pending agents not yet in results
        for name in self.swarm._nodes:
            if name not in agents:
                agents[name] = {"name": name, "status": "pending", "session_id": None}
        return {"agents": agents}

    async def on_agent_event(self, event: AgentEvent) -> None:
        """Callback registered with SwarmAgent. Stores and broadcasts events."""
        # Store in history
        if event.agent_name not in self._event_history:
            self._event_history[event.agent_name] = []
        self._event_history[event.agent_name].append(event)

        # Broadcast to all connected WebSocket clients
        payload = {
            "type": "agent_event",
            "agent": event.agent_name,
            "event_type": event.event_type,
            "data": str(event.data) if event.data else None,
            "timestamp_ms": event.timestamp_ms,
        }
        for ws in list(self._connections):
            try:
                await ws.send_json(payload)
            except Exception:
                self._connections.remove(ws)

    async def start(self) -> None:
        """Start the dashboard server (non-blocking)."""
        import uvicorn
        config = uvicorn.Config(self.app, host=self.host, port=self.port, log_level="warning")
        server = uvicorn.Server(config)
        asyncio.create_task(server.serve())
```

**Usage with Swarm:**
```python
async def main():
    swarm = Swarm(cli_path="~/.toolbox/bin/claude")
    swarm.add(checker, render_vars={"file_path": "test.lean"})
    swarm.add(fixer, depends_on=["proof-checker"])

    # Start dashboard (non-blocking)
    dashboard = SwarmDashboard(swarm, port=8420)
    await dashboard.start()

    # Register event callback so agents emit to dashboard
    swarm.set_event_callback(dashboard.on_agent_event)

    # Run swarm (agents emit events to dashboard in real-time)
    results = await swarm.run()
```

**UI Features (index.html):**
- Left sidebar: list of agents with colored status badges (green=running, yellow=paused, red=failed, gray=pending)
- Main panel: selected agent's message history (streamed in real-time)
- Bottom bar: text input to send feedback to selected agent
- Control buttons per agent: Pause / Resume / Cancel
- Displays session_id for each agent (useful for manual CLI `--resume`)
- Total cost aggregation at top

---

## Inter-Agent Communication

### Two-channel architecture per agent

Each agent has two separate channels:
- **`{name}:inbox`** — User/framework messages. Consumed by the run loop and injected directly into the agent's conversation.
- **`{name}:messages`** — Agent-to-agent messages. Written by `send_message` tool, consumed by `check_messages` tool. The run loop only peeks (never consumes).

### Pattern 1: Native messaging tools (default, `enable_messaging=True`)

When messaging is enabled, each agent automatically receives:
- `send_message(to, message)` — writes to `{recipient}:messages`
- `check_messages(wait_seconds)` — reads from `{self}:messages`

After each response, the framework peeks at the `:messages` channel. If there are pending messages, it injects a notification:
```
[NOTIFICATION]: You have 2 pending messages from: user_agent, noise_agent. Use check_messages to read them.
```
The agent then calls `check_messages` on its next turn (or ignores).

**System prompt requirement**: All agents must have a `system_prompt` when messaging is enabled. It should describe the agent's role and which agents it collaborates with. The framework appends messaging tool documentation as a postfix.

### Pattern 2: DAG Result Passing (Implicit)
Dependency results are auto-injected into downstream prompt templates:
```python
swarm.add(analyzer, render_vars={"file": "main.py"})
swarm.add(fixer, depends_on=["analyzer"])
# fixer's prompt can use {{ analyzer.output }} or {{ analyzer.raw_result }}
```

### Pattern 3: User feedback via inbox
```python
# From the dashboard or programmatically:
await swarm.send_to_agent("proof-fixer", sender="user", payload="Focus on line 42 first")
# Injected as [USER FEEDBACK]: Focus on line 42 first
```

### Pattern 4: Pub/Sub Broadcast
```python
sub = swarm.channels["progress"].subscribe()
msg = await sub.get()
```

---

## Example: Proof Checking Swarm

```python
import asyncio
from pathlib import Path
from pydantic import BaseModel
from strataswarm import (
    Swarm, AgentSpec, ToolSet, ExecutionMode,
    ClaudeBackend, SwarmDashboard,
    JsonSchemaParser, RegexParser,
    ContainsText, MessageCount, ResultFieldTruthy, AnyOf,
)


class ProofResult(BaseModel):
    has_sorry: bool
    compiles: bool
    file_path: str
    details: str


# Agent 1: Check proofs (structured output via JsonSchemaParser)
checker = AgentSpec(
    name="proof-checker",
    system_prompt="You are a proof checker. You work with: proof-fixer (fixes issues you find), verifier (confirms fixes).",
    prompt=Path("prompts/check_proofs.j2"),  # file-based template
    tools=ToolSet().allow("Read").allow("Bash", "lake*").disallow("Edit"),
    result_parser=JsonSchemaParser(output_type=ProofResult),
    max_turns=5,
    max_budget_usd=0.10,
    timeout_seconds=120.0,
    halt_when=AnyOf(validators=[
        ContainsText(text="sorry", case_sensitive=False),        # halt during streaming
        ResultFieldTruthy(field_name="has_sorry"),               # halt after result parse
        MessageCount(max_messages=20),
    ]),
)

# Agent 2: Fix proofs (depends on checker, accepts user guidance)
fixer = AgentSpec(
    name="proof-fixer",
    system_prompt="You are a proof fixer. You work with: proof-checker (reports issues), verifier (validates your fixes).",
    prompt="Fix the sorry-based proofs in {{ proof_checker.output.file_path }}. Issues: {{ proof_checker.output.details }}",
    tools=ToolSet().allow("Read").allow("Edit").allow("Bash", "lake*"),
    max_turns=15,
    max_budget_usd=0.50,
    timeout_seconds=300.0,
    inbox_channel="proof-fixer:inbox",
)

# Agent 3: Verify fix (depends on fixer)
verifier = AgentSpec(
    name="verifier",
    system_prompt="You are a proof verifier. You work with: proof-checker (original checker), proof-fixer (made the fixes).",
    prompt="Run `lake lean {{ proof_checker.output.file_path }}` and confirm no errors.",
    tools=ToolSet().allow("Bash", "lake*").allow("Read"),
    result_parser=JsonSchemaParser(output_type=ProofResult),
    max_turns=3,
    timeout_seconds=60.0,
)


async def main():
    # Backend factory: creates a fresh ClaudeBackend for each agent
    def make_backend():
        return ClaudeBackend(cli_path="~/.toolbox/bin/claude")

    swarm = Swarm(backend_factory=make_backend)

    swarm.add(checker, render_vars={"file_path": "StrataAgentTest.lean"})
    swarm.add(fixer, depends_on=["proof-checker"])
    swarm.add(verifier, depends_on=["proof-fixer"])

    # Start web dashboard (open http://localhost:8420)
    dashboard = SwarmDashboard(swarm, port=8420)
    await dashboard.start()
    swarm.set_event_callback(dashboard.on_agent_event)

    # Run the swarm
    results = await swarm.run(mode=ExecutionMode.AWAIT_ALL)

    total_cost = sum(r.cost_usd or 0 for r in results.values())
    print(f"Total cost: ${total_cost:.4f}")
    print(f"Checker: {results['proof-checker'].halted_by}")
    print(f"Fixer: {results['proof-fixer'].halted_by}")
    print(f"Verifier: {results['verifier'].output}")


asyncio.run(main())
```

---

## Dependencies (pyproject.toml)

```toml
[project]
name = "strataagent"
version = "0.1.0"
requires-python = ">=3.14"
dependencies = [
    "claude-agent-sdk>=0.2.82",
    "jinja2>=3.1",
    "pydantic>=2.0",
    "fastapi>=0.115",
    "uvicorn[standard]>=0.30",
]
```

---

## Key Design Decisions

| Decision | Rationale |
|----------|-----------|
| **ToolSet class (not raw strings)** | Provider-agnostic; `.to_claude_allowed()` is the only Claude-specific method. Easy to add `.to_openai_format()` later. |
| **HaltValidator with two gates** | `should_halt_on_messages()` fires during streaming; `should_halt_on_result()` fires after parsing. Covers both early-exit and post-result validation. |
| **ResultParser strategy pattern** | User picks: JsonSchemaParser (constrains LLM), RegexParser, PydanticFromTextParser, CustomParser, or RawTextParser. Each agent declares its own strategy. |
| **AgentBackend ABC** | `SwarmAgent` programs against an abstract interface, not `claude_agent_sdk` directly. `ClaudeBackend` is one adapter. Easy to add OpenAI, mock, etc. |
| **Emit before pause** | Messages are emitted to the UI BEFORE the pause gate fires. The user always sees what the agent just said, THEN it pauses — giving a clear picture. |
| **Two-channel architecture** | `:inbox` for user/framework injection (consumed by run loop); `:messages` for agent-to-agent comms (consumed by `check_messages` tool). No competition. |
| **Peek-based notifications** | Run loop peeks at `:messages` (no consume). If pending, injects a notification nudging the agent to call `check_messages`. Agent decides when to read. |
| **MCP tools for messaging** | `send_message`/`check_messages` are native MCP tools auto-injected by the Swarm. Return format: `{"content": [{"type": "text", "text": "..."}]}`. |
| **System prompt required with messaging** | Forces the user to describe agent roles and collaborators. Framework appends messaging docs as a postfix — agent's persona comes first. |
| **Auto-allowed messaging tools** | When messaging MCP server is injected, `mcp__agent_messaging__*` tools are automatically added to `allowed_tools` — no permission prompts. |
| **Event callback for UI** | Each agent emits `AgentEvent`s (status change, messages, tool results, cost). Dashboard subscribes via `set_event_callback()`. Decoupled from agent logic. |
| **Backend factory** | Swarm takes `backend_factory: Callable[[], AgentBackend]` — creates a fresh backend instance per agent. No shared mutable state. |
| **ClaudeBackend auto-resolves CLI path** | Checks `STRATA_AGENT_CLAUDE_PATH` env var, then `~/.toolbox/bin/claude`. No explicit path needed. |
| **DAG via asyncio.gather on deps** | No topological sort; each task awaits its own deps. Handles diamonds naturally. |
| **Jinja2 (inline + file-based)** | Detects `.j2`/`.jinja2` suffix → file load. Detects `{{`/`{%` → inline render. Otherwise plain string. |

---

## Verification Plan

1. **Unit tests** (no SDK needed) — run inline:
   - `CancellationToken`: cancel propagation, link behavior
   - `PauseToken`: pause/resume/wait_if_paused
   - `Channel`: send/receive/timeout/subscribe/peek_summary/pending_count
   - `HaltValidator`: ContainsText, MessageCount, ResultFieldEquals, ResultFieldTruthy, AnyOf, AllOf
   - `ResultParser`: each strategy (JsonSchema, Regex, PydanticFromText, Custom, Raw)
   - `render_prompt`: inline, file-based, plain string detection
   - `ToolSet`: allow/disallow/to_claude_format

2. **Integration tests** (`tests/test_claude_backend_integration.py`):
   - Single query with tool use (Bash)
   - Multi-turn chaining (write file → read file)
   - Interrupt mid-execution
   - Structured output: treasure hunt (JsonSchema + tool use)
   - Structured output: math puzzle (JsonSchema + calculator)

3. **Agent tests** (`tests/test_swarm_agent_integration.py`):
   - Cancellation: cancel after 3s, verify clean shutdown
   - User message injection: pause → inject → resume
   - Autonomous agents (shared mailbox, no DAG)
   - Three-agent relay race (sleep-based coordination)

4. **Messaging tests** (`tests/test_agent_channel_comms.py`):
   - Three agents (SecurityAgent, UserAgent, NoiseAgent) coordinating via `send_message`/`check_messages`
   - Verifies messages are delivered, agents respond, workflow completes

5. **Web UI verification**:
   - Dashboard shows agents with status badges
   - Real-time message streaming via WebSocket
   - Pause/resume/cancel controls
   - User feedback injection
   - Session ID and cost tracking
