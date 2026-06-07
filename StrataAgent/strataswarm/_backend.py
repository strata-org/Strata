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
    cwd: str | None = None
    resume_session_id: str | None = None
    hooks: dict[str, Any] | None = None


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

    @property
    def supports_compaction(self) -> bool:
        """Whether this backend supports native context compaction.
        If False, the framework will use summary-based compaction as fallback."""
        return False

    async def compact(self) -> None:
        """Reduce context size. Backends that support native compaction (e.g., Claude)
        use the built-in mechanism. Others generate a summary of recent messages and
        replace the conversation with it.

        The framework calls this when context usage exceeds a threshold.
        Subclasses should override to provide their compaction strategy."""
        pass

    async def compact_with_summary(self, backend_factory: Any = None) -> None:
        """Fallback compaction for backends without native support.
        Generates a summary from recent messages using a separate LLM call,
        then starts a fresh session seeded with that summary.

        Only called by the framework when supports_compaction is False."""
        if not backend_factory or not self._messages:
            return

        lines = []
        for msg in self._messages[-80:]:
            if msg.type in ("text", "tool_use", "tool_result") and msg.content:
                lines.append(f"[{msg.type}] {msg.content[:300]}")
        transcript = "\n".join(lines)
        if not transcript.strip():
            return

        summarizer = backend_factory()
        await summarizer.connect(BackendConfig(
            allowed_tools=[], permission_mode="auto", max_turns=1,
            system_prompt=(
                "Produce a concise summary: (1) task, (2) accomplished, "
                "(3) next steps, (4) key state. Include file paths and values."
            ),
        ))
        await summarizer.send_query(f"Summarize:\n{transcript}")
        summary = ""
        async for msg in summarizer.receive_messages():
            if msg.type == "text" and msg.content:
                summary += msg.content
        await summarizer.disconnect()

        if summary.strip():
            self._messages = [BackendMessage(type="text", content=summary.strip())]

    @property
    def model_name(self) -> str | None:
        """The actual model being used by this backend (reported by the API)."""
        return getattr(self, "_model_name", None)

    @property
    def messages(self) -> list[BackendMessage]:
        """Recent messages from this session. Backend owns the message history.
        Returns whatever is available locally — may be empty on resume if the
        backend doesn't support history retrieval yet."""
        return getattr(self, "_messages", [])

    async def get_message_history(self) -> list[BackendMessage] | None:
        """Retrieve full message history from the backend if supported.
        Returns None if the backend doesn't support history retrieval.
        Future backends may implement this to pull from session storage."""
        return None


    async def __aenter__(self) -> AgentBackend:
        return self

    async def __aexit__(self, *exc: object) -> None:
        await self.disconnect()
