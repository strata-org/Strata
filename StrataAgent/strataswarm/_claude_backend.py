from __future__ import annotations

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
        assert self._client is not None
        await self._client.query(prompt)

    async def receive_messages(self) -> AsyncIterator[BackendMessage]:
        assert self._client is not None
        async for message in self._client.receive_response():
            if isinstance(message, AssistantMessage):
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

    async def disconnect(self) -> None:
        if self._client:
            await self._client.disconnect()
            self._client = None
