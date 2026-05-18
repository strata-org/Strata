from __future__ import annotations

import time
from collections import Counter
from collections.abc import Awaitable, Callable
from typing import Any, Generic, TypeVar

from ._backend import AgentBackend, BackendConfig, BackendMessage
from ._channels import ChannelBus, ChannelMessage
from ._result_parsers import JsonSchemaParser
from ._templates import render_prompt
from ._tokens import CancellationToken, PauseToken
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus

T = TypeVar("T")

EventCallback = Callable[[AgentEvent], Awaitable[None]]


class SwarmAgent(Generic[T]):
    def __init__(
        self,
        spec: AgentSpec[T],
        backend: AgentBackend,
        channel_bus: ChannelBus,
        cancellation: CancellationToken,
        pause: PauseToken,
        render_vars: dict[str, Any] | None = None,
        on_event: EventCallback | None = None,
        mcp_servers_override: dict[str, Any] | None = None,
        system_prompt_override: str | None = None,
    ) -> None:
        self.spec = spec
        self.backend = backend
        self.channel_bus = channel_bus
        self.cancellation = cancellation
        self.pause = pause
        self._render_vars = render_vars or {}
        self._messages: list[BackendMessage] = []
        self._on_event = on_event
        self._mcp_servers_override = mcp_servers_override
        self._system_prompt_override = system_prompt_override

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

        mcp_servers = self._mcp_servers_override or self.spec.mcp_servers or None
        system_prompt = self._system_prompt_override or self.spec.system_prompt

        allowed_tools = self.spec.tools.to_claude_allowed()

        # Auto-allow messaging tools when the messaging server is injected
        if mcp_servers and "agent_messaging" in mcp_servers:
            allowed_tools = allowed_tools + [
                "mcp__agent_messaging__send_message",
                "mcp__agent_messaging__check_messages",
            ]

        return BackendConfig(
            allowed_tools=allowed_tools,
            disallowed_tools=self.spec.tools.to_claude_disallowed(),
            permission_mode=self.spec.permission_mode,
            max_turns=self.spec.max_turns,
            max_budget_usd=self.spec.max_budget_usd,
            model=self.spec.model,
            system_prompt=system_prompt,
            output_format=output_format,
            extra={"mcp_servers": mcp_servers} if mcp_servers else None,
        )

    async def run(self) -> AgentResult[T]:
        prompt = render_prompt(self.spec.prompt, self._render_vars)
        config = self._build_config()
        result: AgentResult[T] = AgentResult(name=self.spec.name, status=AgentStatus.PENDING)
        start_time = time.monotonic()

        if self.cancellation.is_cancelled:
            result.halted_by = "cancelled"
            result.status = AgentStatus.CANCELLED
            await self._emit("status_change", AgentStatus.CANCELLED.value)
            return result

        await self.pause.wait_if_paused()

        result.status = AgentStatus.RUNNING
        await self._emit("status_change", AgentStatus.RUNNING.value)

        inbox_channel = self.spec.inbox_channel or f"{self.spec.name}:inbox"

        await self.backend.connect(config)

        try:
            await self.backend.send_query(prompt)

            while True:
                async for message in self.backend.receive_messages():
                    # Timeout
                    if self.spec.timeout_seconds:
                        elapsed = time.monotonic() - start_time
                        if elapsed >= self.spec.timeout_seconds:
                            await self.backend.interrupt()
                            result.halted_by = "timeout"
                            result.status = AgentStatus.FAILED
                            result.duration_ms = int(elapsed * 1000)
                            await self._emit("status_change", AgentStatus.FAILED.value)
                            return result

                    # Cancellation
                    if self.cancellation.is_cancelled:
                        await self.backend.interrupt()
                        result.halted_by = "cancelled"
                        result.status = AgentStatus.CANCELLED
                        await self._emit("status_change", AgentStatus.CANCELLED.value)
                        return result

                    self._messages.append(message)

                    # Emit message to UI BEFORE pause gate
                    if message.type == "text" and message.content:
                        await self._emit("message", message.content)
                    elif message.type == "tool_use" and message.content:
                        await self._emit("message", f"[tool] {message.content}")
                    elif message.type == "tool_result" and message.content:
                        await self._emit("message", f"[tool_result] {message.content}")

                    # Pause gate (user sees message first, then agent pauses)
                    if self.pause.is_paused:
                        result.status = AgentStatus.PAUSED
                        await self._emit("status_change", AgentStatus.PAUSED.value)
                    await self.pause.wait_if_paused()
                    if result.status == AgentStatus.PAUSED:
                        result.status = AgentStatus.RUNNING
                        await self._emit("status_change", AgentStatus.RUNNING.value)

                    # Message-level halt check
                    if (
                        self.spec.halt_when
                        and self.spec.halt_when.should_halt_on_messages(self._messages)
                    ):
                        await self.backend.interrupt()
                        result.halted_by = "predicate"
                        result.status = AgentStatus.HALTED
                        await self._emit("status_change", AgentStatus.HALTED.value)
                        break

                    # Process result
                    if message.type == "result":
                        result.raw_result = message.raw_result
                        result.structured_output = message.structured_output
                        result.cost_usd = message.cost_usd
                        result.num_turns = message.num_turns
                        result.session_id = message.session_id
                        result.duration_ms = message.duration_ms
                        await self._emit("cost_update", message.cost_usd)

                        # Parse via strategy
                        if self.spec.result_parser:
                            result.output = self.spec.result_parser.parse(
                                message.raw_result, message.structured_output
                            )

                        # Result-level halt check
                        if (
                            self.spec.halt_when
                            and self.spec.halt_when.should_halt_on_result(
                                result.output, result.raw_result
                            )
                        ):
                            result.halted_by = "predicate"
                            result.status = AgentStatus.HALTED
                            await self._emit("status_change", AgentStatus.HALTED.value)
                            break

                        if message.stop_reason == "max_turns":
                            result.halted_by = "max_turns"
                        elif message.stop_reason == "budget":
                            result.halted_by = "budget"

                # Exit multi-turn loop?
                if result.halted_by != "completion" or self.cancellation.is_cancelled:
                    break

                has_messaging_tools = (
                    self._mcp_servers_override
                    and "agent_messaging" in self._mcp_servers_override
                )

                # --- Phase A: Check :inbox for user/framework injection (consume) ---
                inbox = self.channel_bus[inbox_channel]
                injected_msg = await inbox.receive(timeout=0.1)

                if injected_msg:
                    source = injected_msg.sender
                    if source == "user":
                        injection = f"[USER FEEDBACK]: {injected_msg.payload}"
                    else:
                        injection = (
                            f"[MESSAGE FROM AGENT '{source}']: {injected_msg.payload}"
                        )
                    await self.backend.send_query(injection)
                    await self._emit(
                        "message",
                        f"[Injected from {source}]: {injected_msg.payload}",
                    )
                    continue  # Loop back to receive_messages()

                # --- Phase B: Peek at :messages channel for notification (no consume) ---
                if has_messaging_tools:
                    messages_ch = self.channel_bus.get_or_create(
                        f"{self.spec.name}:messages"
                    )
                    pending = messages_ch.peek_summary()
                    if pending:
                        sender_counts = Counter(
                            sender for sender, _ in pending
                        )
                        sender_list = ", ".join(
                            f"{name} ({count})" if count > 1 else name
                            for name, count in sender_counts.items()
                        )
                        total = len(pending)
                        notification = (
                            f"[NOTIFICATION]: You have {total} pending "
                            f"message{'s' if total > 1 else ''} "
                            f"from: {sender_list}. "
                            f"Use check_messages to read them."
                        )
                        await self.backend.send_query(notification)
                        await self._emit(
                            "message",
                            f"[Notification: {total} pending from {sender_list}]",
                        )
                        continue  # Loop back to receive_messages()

                # No inbox message, no pending agent messages => done
                break

        finally:
            await self.backend.disconnect()

        if result.status == AgentStatus.RUNNING:
            result.status = AgentStatus.COMPLETED
            await self._emit("status_change", AgentStatus.COMPLETED.value)

        out_ch = self.channel_bus.get_or_create(f"{self.spec.name}:result")
        await out_ch.send(ChannelMessage(sender=self.spec.name, payload=result))
        await self._emit("result", {"output": str(result.output), "halted_by": result.halted_by})

        return result
