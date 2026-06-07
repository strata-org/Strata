from __future__ import annotations

import asyncio
import os
from collections.abc import AsyncIterator
from pathlib import Path
from typing import Any

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ClaudeSDKClient,
    ResultMessage,
    TextBlock,
    ThinkingBlock,
    ToolResultBlock,
    ToolUseBlock,
    UserMessage,
)

from ._backend import AgentBackend, BackendConfig, BackendMessage


def _default_cli_path() -> str:
    env_path = os.environ.get("STRATA_AGENT_CLAUDE_PATH")
    if env_path:
        return env_path
    default_path = Path.home() / ".toolbox" / "bin" / "claude"
    if default_path.exists():
        return str(default_path)
    raise FileNotFoundError(
        "Claude CLI not found. Set STRATA_AGENT_CLAUDE_PATH or install to ~/.toolbox/bin/claude"
    )


class ClaudeBackend(AgentBackend):
    def __init__(self, cli_path: str | None = None) -> None:
        self._cli_path = cli_path or _default_cli_path()
        self._client: ClaudeSDKClient | None = None
        self._cumulative_input_tokens: int = 0
        self._cumulative_output_tokens: int = 0
        self._cumulative_cache_read: int = 0
        self._turn_count: int = 0
        self._session_id: str | None = None
        self._config: BackendConfig | None = None
        self._messages: list[BackendMessage] = []
        self._model_name: str | None = None

    def _estimate_cost(self) -> float:
        # Opus pricing: $15/M input, $75/M output, $1.5/M cache read
        input_cost = self._cumulative_input_tokens * 15.0 / 1_000_000
        output_cost = self._cumulative_output_tokens * 75.0 / 1_000_000
        cache_cost = self._cumulative_cache_read * 1.5 / 1_000_000
        return input_cost + output_cost + cache_cost

    async def connect(self, config: BackendConfig) -> None:
        self._config = config
        # Already connected — don't create a new session
        if self._client is not None and self._session_id:
            return
        await self._do_connect(resume=False)

    async def force_new_session(self) -> None:
        """Force a fresh session (for handoff-restart / checkpoint recovery).
        Disconnects existing client and creates a new session."""
        if self._client:
            try:
                await self.disconnect()
            except Exception:
                pass
        self._client = None
        self._session_id = None
        await self._do_connect(resume=False)

    async def _do_connect(self, resume: bool = False) -> None:
        config = self._config
        assert config is not None
        opts_kwargs: dict[str, Any] = {
            "allowed_tools": config.allowed_tools,
            "disallowed_tools": config.disallowed_tools,
            "permission_mode": config.permission_mode,
        }
        if config.max_turns:
            opts_kwargs["max_turns"] = config.max_turns
        # Only pass budget if explicitly set — None means unlimited
        if config.max_budget_usd is not None and config.max_budget_usd > 0:
            opts_kwargs["max_budget_usd"] = config.max_budget_usd
        if config.model:
            opts_kwargs["model"] = config.model
        if config.system_prompt:
            opts_kwargs["system_prompt"] = config.system_prompt
        if config.output_format:
            opts_kwargs["output_format"] = config.output_format
        if self._cli_path:
            opts_kwargs["cli_path"] = self._cli_path
        if config.cwd:
            opts_kwargs["cwd"] = config.cwd
        if config.extra:
            if "mcp_servers" in config.extra:
                opts_kwargs["mcp_servers"] = config.extra["mcp_servers"]

        # Hooks (workspace enforcement, etc.)
        if config.hooks:
            opts_kwargs["hooks"] = config.hooks

        # Resume from previous session if available
        if resume and self._session_id:
            opts_kwargs["resume"] = self._session_id
        elif config.resume_session_id:
            opts_kwargs["resume"] = config.resume_session_id
            self._session_id = config.resume_session_id

        options = ClaudeAgentOptions(**opts_kwargs)
        self._client = ClaudeSDKClient(options=options)
        await self._client.connect()

    async def reconnect(self) -> bool:
        """Attempt to reconnect using stored session ID. Returns True if successful."""
        if not self._session_id:
            return False
        try:
            await self._do_connect(resume=True)
            return True
        except Exception:
            return False

    async def get_message_history(self) -> list[BackendMessage] | None:
        """Retrieve message history from local JSONL session files.

        Claude stores session transcripts at:
        ~/.claude/projects/{encoded_cwd}/{session_id}.jsonl

        Returns parsed messages or None if unavailable.
        """
        if not self._session_id or not self._config:
            return None

        import json
        from pathlib import Path

        cwd = self._config.cwd or os.getcwd()
        encoded_cwd = cwd.replace("/", "-")
        history_file = Path.home() / ".claude" / "projects" / encoded_cwd / f"{self._session_id}.jsonl"

        if not history_file.exists():
            return None

        messages: list[BackendMessage] = []
        try:
            with open(history_file, "r", encoding="utf-8") as f:
                for line in f:
                    if not line.strip():
                        continue
                    event = json.loads(line)
                    ev_type = event.get("type")

                    if ev_type == "user":
                        msg = event.get("message", {})
                        content = msg.get("content", "")
                        if isinstance(content, str):
                            messages.append(BackendMessage(type="text", content=content))

                    elif ev_type == "assistant":
                        msg = event.get("message", {})
                        for block in msg.get("content", []):
                            block_type = block.get("type")
                            if block_type == "text":
                                messages.append(BackendMessage(type="text", content=block.get("text", "")))
                            elif block_type == "tool_use":
                                messages.append(BackendMessage(
                                    type="tool_use",
                                    content=f"{block.get('name', '')}({block.get('input', '')})",
                                ))
        except (json.JSONDecodeError, OSError):
            return None

        return messages if messages else None

    async def send_query(self, prompt: str) -> None:
        assert self._client is not None
        await self._client.query(prompt)

    async def receive_messages(self) -> AsyncIterator[BackendMessage]:
        import random
        async for msg in self._receive_messages_inner():
            self._messages.append(msg)
            await asyncio.sleep(random.uniform(0.02, 0.15))
            yield msg

    async def _receive_messages_inner(self) -> AsyncIterator[BackendMessage]:
        assert self._client is not None
        async for message in self._client.receive_response():
            if isinstance(message, AssistantMessage):
                if message.session_id:
                    self._session_id = message.session_id
                if message.model and not self._model_name:
                    self._model_name = message.model
                for block in message.content:
                    if isinstance(block, TextBlock):
                        yield BackendMessage(type="text", content=block.text)
                    elif isinstance(block, ThinkingBlock):
                        yield BackendMessage(type="thinking", content=block.thinking)
                    elif isinstance(block, ToolUseBlock):
                        yield BackendMessage(
                            type="tool_use", content=f"{block.name}({block.input})"
                        )
                    elif isinstance(block, ToolResultBlock):
                        content = block.content
                        if isinstance(content, list):
                            content = " ".join(
                                item.get("text", str(item)) for item in content
                            )
                        yield BackendMessage(
                            type="tool_result", content=str(content) if content else ""
                        )
                # Emit usage info after processing blocks
                if message.usage:
                    self._cumulative_input_tokens += message.usage.get("input_tokens", 0)
                    self._cumulative_output_tokens += message.usage.get("output_tokens", 0)
                    self._cumulative_cache_read += message.usage.get("cache_read_input_tokens", 0)
                    self._turn_count += 1
                    yield BackendMessage(
                        type="usage",
                        content=None,
                        num_turns=self._turn_count,
                        cost_usd=self._estimate_cost(),
                    )
            elif isinstance(message, UserMessage):
                # UserMessage carries tool results back from MCP tools
                if message.tool_use_result:
                    result_content = message.tool_use_result
                    if isinstance(result_content, dict):
                        text = result_content.get("text", str(result_content))
                    elif isinstance(result_content, list):
                        text = " ".join(
                            item.get("text", str(item)) if isinstance(item, dict) else str(item)
                            for item in result_content
                        )
                    else:
                        text = str(result_content)
                    yield BackendMessage(type="tool_result", content=text)
                elif isinstance(message.content, list):
                    for block in message.content:
                        if isinstance(block, ToolResultBlock):
                            content = block.content
                            if isinstance(content, list):
                                content = " ".join(
                                    item.get("text", str(item)) for item in content
                                )
                            yield BackendMessage(
                                type="tool_result", content=str(content) if content else ""
                            )
            elif isinstance(message, ResultMessage):
                # Track session ID for reconnection
                if message.session_id:
                    self._session_id = message.session_id
                stop_reason = message.stop_reason
                if not stop_reason and message.subtype and "budget" in message.subtype:
                    stop_reason = "budget"
                yield BackendMessage(
                    type="result",
                    raw_result=message.result,
                    structured_output=message.structured_output,
                    cost_usd=message.total_cost_usd,
                    num_turns=message.num_turns,
                    session_id=message.session_id,
                    duration_ms=message.duration_ms,
                    stop_reason=stop_reason,
                )

    async def interrupt(self) -> None:
        if self._client:
            await self._client.interrupt()

    async def get_context_percentage(self) -> float | None:
        if not self._client:
            return None
        try:
            usage = await self._client.get_context_usage()
            return usage.get("percentage", None)
        except Exception:
            return None

    @property
    def supports_compaction(self) -> bool:
        return True

    async def compact(self) -> None:
        if self._client:
            await self._client.query("/compact")
            async for _ in self._client.receive_response():
                pass

    async def disconnect(self) -> None:
        if self._client:
            await self._client.disconnect()
            self._client = None

