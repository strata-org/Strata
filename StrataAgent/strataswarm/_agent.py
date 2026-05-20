from __future__ import annotations

import asyncio
import logging
import time
from collections import Counter
from collections.abc import Awaitable, Callable
from datetime import datetime
from typing import Any, Generic, TypeVar

from ._backend import AgentBackend, BackendConfig, BackendMessage
from ._channels import ChannelBus, ChannelMessage
from ._result_parsers import JsonSchemaParser
from ._templates import render_prompt
from ._tokens import CancellationToken, PauseToken
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus

T = TypeVar("T")
logger = logging.getLogger("strataswarm.agent")

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
        wait_after_completion: bool = False,
        backend_factory: Any = None,
        swarm_name: str = "",
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
        self._wait_after_completion = wait_after_completion
        self._backend_factory = backend_factory
        self._swarm_name = swarm_name
        self._last_emit_time = time.monotonic()

    async def _emit(self, event_type: str, data: Any = None) -> None:
        if self._on_event:
            event = AgentEvent(
                agent_name=self.spec.name,
                event_type=event_type,
                data=data,
                timestamp_ms=int(time.time() * 1000),
            )
            await self._on_event(event)
        self._last_emit_time = time.monotonic()

    async def _emit_heartbeat_if_needed(self) -> None:
        elapsed = time.monotonic() - self._last_emit_time
        if elapsed >= 5.0:
            await self._emit("heartbeat", "working...")

    def _get_summary_path(self) -> Any:
        from pathlib import Path
        swarm_dir = self._swarm_name or "default"
        summary_dir = Path(__file__).parent.parent / "temp" / swarm_dir
        summary_dir.mkdir(parents=True, exist_ok=True)
        return summary_dir / f"{self.spec.name}_summary.txt"

    def _get_raw_transcript(self) -> str:
        lines = []
        for msg in self._messages[-80:]:
            if msg.type in ("text", "tool_use", "tool_result") and msg.content:
                lines.append(f"[{msg.type}] {msg.content[:300]}")
        return "\n".join(lines)

    def _load_last_summary(self) -> str | None:
        path = self._get_summary_path()
        if path.exists():
            return path.read_text().strip() or None
        return None

    async def _periodic_summary_saver(self, backend_factory: Any) -> None:
        from ._backend import BackendConfig as BC

        while True:
            await asyncio.sleep(300)
            if len(self._messages) < 5:
                continue

            transcript = self._get_raw_transcript()
            if not transcript.strip():
                continue

            logger.info(f"[SUMMARY] {self.spec.name}: generating summary...")
            try:
                summarizer = backend_factory()
                await summarizer.connect(BC(
                    allowed_tools=[],
                    permission_mode="auto",
                    max_turns=1,
                    system_prompt=(
                        "You are a summarizer. Given an agent's conversation transcript, "
                        "produce a concise summary that captures: "
                        "(1) what task the agent was working on, "
                        "(2) what it has accomplished so far, "
                        "(3) what it was about to do next, "
                        "(4) any important state or decisions made. "
                        "This summary will be used to resume the agent if it crashes. "
                        "Be specific — include file paths, variable values, and exact progress."
                    ),
                ))
                await summarizer.send_query(
                    f"Summarize this agent's progress for crash recovery:\n\n"
                    f"Agent name: {self.spec.name}\n"
                    f"Original task: {self.spec.prompt}\n\n"
                    f"--- Transcript (last messages) ---\n{transcript}\n---"
                )
                summary_text = ""
                async for msg in summarizer.receive_messages():
                    if msg.type == "text" and msg.content:
                        summary_text += msg.content
                    elif msg.type == "result" and msg.raw_result:
                        summary_text = msg.raw_result
                await summarizer.disconnect()

                if summary_text.strip():
                    self._get_summary_path().write_text(summary_text.strip())
                    logger.info(f"[SUMMARY] {self.spec.name}: saved ({len(summary_text)} chars)")
            except Exception as e:
                logger.error(f"[SUMMARY] {self.spec.name}: failed: {e}")

    def _build_config(self) -> BackendConfig:
        output_format = None
        if isinstance(self.spec.result_parser, JsonSchemaParser):
            output_format = self.spec.result_parser.get_output_format()

        mcp_servers = self._mcp_servers_override or self.spec.mcp_servers or None
        system_prompt = self._system_prompt_override or self.spec.system_prompt

        allowed_tools = self.spec.tools.to_claude_allowed()

        if mcp_servers and "agent_messaging" in mcp_servers:
            allowed_tools = allowed_tools + [
                "mcp__agent_messaging__send_message",
                "mcp__agent_messaging__check_messages",
                "mcp__agent_messaging__get_time",
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

        try:
            await self.backend.connect(config)
        except Exception as e:
            result.halted_by = "failed"
            result.status = AgentStatus.FAILED
            await self._emit("status_change", AgentStatus.FAILED.value)
            await self._emit("message", f"[ERROR] Failed to connect: {e}")
            logger.error(f"[ERROR] {self.spec.name}: connect failed: {e}")
            return result

        self._last_emit_time = time.monotonic()

        # Start periodic summary saver
        summary_task = None
        if self._backend_factory:
            summary_task = asyncio.create_task(
                self._periodic_summary_saver(self._backend_factory)
            )

        try:
            await self.backend.send_query(prompt)

            while True:
                _loop_start = time.monotonic()
                logger.debug(f"[LOOP] {self.spec.name}: entering receive_messages()")
                await self._emit("message", "[thinking...]")
                _first_msg = True

                async for message in self.backend.receive_messages():
                    if _first_msg:
                        _wait = time.monotonic() - _loop_start
                        logger.debug(f"[LOOP] {self.spec.name}: first msg (type={message.type}) after {_wait:.1f}s")
                        _first_msg = False

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
                    await self._emit_heartbeat_if_needed()

                    # Emit message to UI BEFORE pause gate
                    if message.type == "text" and message.content:
                        await self._emit("message", message.content)
                    elif message.type == "tool_use" and message.content:
                        await self._emit("message", f"[tool] {message.content}")
                    elif message.type == "tool_result" and message.content:
                        await self._emit("message", f"[tool_result] {message.content}")
                    elif message.type == "usage":
                        result.cost_usd = message.cost_usd
                        result.num_turns = message.num_turns
                        await self._emit("cost_estimate", message.cost_usd)
                        continue

                    # Pause gate
                    if self.pause.is_paused:
                        result.status = AgentStatus.PAUSED
                        await self._emit("status_change", AgentStatus.PAUSED.value)
                    await self.pause.wait_if_paused()
                    if result.status == AgentStatus.PAUSED:
                        result.status = AgentStatus.RUNNING
                        await self._emit("status_change", AgentStatus.RUNNING.value)

                    # Message-level halt check
                    if self.spec.halt_when and self.spec.halt_when.should_halt_on_messages(self._messages):
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

                        if self.spec.result_parser:
                            result.output = self.spec.result_parser.parse(
                                message.raw_result, message.structured_output
                            )

                        if self.spec.halt_when and self.spec.halt_when.should_halt_on_result(
                            result.output, result.raw_result
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

                # Check context usage — compact if >= 70%
                ctx_pct = await self.backend.get_context_percentage()
                if ctx_pct is not None and ctx_pct >= 70.0:
                    logger.info(f"[COMPACT] {self.spec.name}: context at {ctx_pct:.0f}%, compacting")
                    await self._emit("message", f"[Compacting context ({ctx_pct:.0f}% used)...]")
                    await self.backend.compact()

                # Check :messages for pending messages (agents + user)
                has_messaging_tools = (
                    self._mcp_servers_override
                    and "agent_messaging" in self._mcp_servers_override
                )

                if has_messaging_tools:
                    messages_ch = self.channel_bus.get_or_create(f"{self.spec.name}:messages")
                    msg = await messages_ch.receive(timeout=0.1)
                    if msg:
                        ts = datetime.now().strftime("%H:%M:%S")
                        injection = f"[{ts}] [From {msg.sender}]: {msg.payload}"
                        logger.debug(f"[MID] {self.spec.name}: from '{msg.sender}', injecting")
                        await self.backend.send_query(injection)
                        await self._emit("message", injection)
                        continue

                # No pending messages => work is done.
                if not self._wait_after_completion:
                    break

                # Enter waiting state
                result.status = AgentStatus.COMPLETED
                await self._emit("status_change", AgentStatus.COMPLETED.value)
                await self._emit("message", "[Waiting for messages or cancellation...]")

                while not self.cancellation.is_cancelled:
                    messages_ch = self.channel_bus.get_or_create(f"{self.spec.name}:messages")
                    msg = await messages_ch.receive(timeout=1.0)
                    if msg:
                        result.status = AgentStatus.RUNNING
                        await self._emit("status_change", AgentStatus.RUNNING.value)
                        ts = datetime.now().strftime("%H:%M:%S")
                        injection = f"[{ts}] [From {msg.sender}]: {msg.payload}"
                        logger.info(f"[WAKE] {self.spec.name}: from '{msg.sender}'")
                        await self.backend.send_query(injection)
                        await self._emit("message", injection)
                        break
                else:
                    result.halted_by = "cancelled"
                    result.status = AgentStatus.CANCELLED
                    await self._emit("status_change", AgentStatus.CANCELLED.value)
                    break

        except Exception as e:
            logger.error(f"[ERROR] {self.spec.name}: crashed: {e}")
            await self._emit("message", f"[ERROR] Agent crashed: {e}")

            recovered = False

            # Attempt 1: session reconnect
            logger.info(f"[RETRY] {self.spec.name}: attempting session reconnect")
            await self._emit("message", "[Attempting session reconnect...]")
            try:
                reconnected = await self.backend.reconnect()
            except Exception:
                reconnected = False

            if reconnected:
                logger.info(f"[RETRY] {self.spec.name}: reconnected")
                await self._emit("message", "[Reconnected, resuming...]")
                await self._emit("status_change", AgentStatus.RUNNING.value)
                try:
                    await self.backend.send_query("[SYSTEM]: You were disconnected. Continue where you left off.")
                    async for message in self.backend.receive_messages():
                        self._messages.append(message)
                        if message.type == "text" and message.content:
                            await self._emit("message", message.content)
                        elif message.type == "tool_use" and message.content:
                            await self._emit("message", f"[tool] {message.content}")
                        elif message.type == "result":
                            result.raw_result = message.raw_result
                            result.cost_usd = message.cost_usd
                            result.num_turns = message.num_turns
                            result.session_id = message.session_id
                            await self._emit("cost_update", message.cost_usd)
                    recovered = True
                except Exception as e2:
                    logger.error(f"[RETRY] {self.spec.name}: session reconnect failed: {e2}")

            # Attempt 2: fresh start with summary
            if not recovered and self._backend_factory:
                summary = self._load_last_summary()
                if summary:
                    logger.info(f"[RETRY] {self.spec.name}: resuming from summary")
                    await self._emit("message", "[Session lost. Resuming from last summary...]")
                    try:
                        fresh_backend = self._backend_factory()
                        await fresh_backend.connect(config)
                        self.backend = fresh_backend
                        resume_prompt = (
                            f"[SYSTEM]: You are resuming after a crash. "
                            f"Summary of your progress:\n\n{summary}\n\n"
                            f"Continue your work from where you left off."
                        )
                        await self.backend.send_query(resume_prompt)
                        await self._emit("status_change", AgentStatus.RUNNING.value)
                        async for message in self.backend.receive_messages():
                            self._messages.append(message)
                            if message.type == "text" and message.content:
                                await self._emit("message", message.content)
                            elif message.type == "tool_use" and message.content:
                                await self._emit("message", f"[tool] {message.content}")
                            elif message.type == "result":
                                result.raw_result = message.raw_result
                                result.cost_usd = message.cost_usd
                                result.num_turns = message.num_turns
                                result.session_id = message.session_id
                                await self._emit("cost_update", message.cost_usd)
                        recovered = True
                    except Exception as e3:
                        logger.error(f"[RETRY] {self.spec.name}: summary resume failed: {e3}")
                        await self._emit("message", f"[ERROR] Summary resume failed: {e3}")

            if not recovered:
                if result.halted_by == "completion":
                    result.halted_by = "failed"
                result.status = AgentStatus.FAILED
                await self._emit("status_change", AgentStatus.FAILED.value)
        finally:
            if summary_task:
                summary_task.cancel()
            try:
                await self.backend.disconnect()
            except Exception:
                pass

        if result.status == AgentStatus.RUNNING:
            result.status = AgentStatus.COMPLETED
            await self._emit("status_change", AgentStatus.COMPLETED.value)

        out_ch = self.channel_bus.get_or_create(f"{self.spec.name}:result")
        await out_ch.send(ChannelMessage(sender=self.spec.name, payload=result))
        await self._emit("result", {"output": str(result.output), "halted_by": result.halted_by})

        return result
