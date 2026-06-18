"""SwarmAgent: unified agent implementation.

Stateless vs Stateful is determined by `spec.stateless`:
- stateless=True: runs full response cycle, then disconnects. No persistence.
- stateless=False: persists connection, waits for messages, stays alive.

Both have full access to messaging, tools, and response processing.
"""

from __future__ import annotations

import asyncio
import logging
import time
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

STALL_TIMEOUT = 300  # 5 minutes — if no message for this long, agent is likely dead


def parse_checkpoint_state(checkpoint_md: str) -> dict | None:
    """Extract machine-readable YAML state from a checkpoint .md file.
    Returns the parsed dict, or None if no machine state found."""
    import yaml as _yaml
    import re
    match = re.search(r'## Machine State\s*```yaml\s*(.+?)```', checkpoint_md, re.DOTALL)
    if match:
        try:
            return _yaml.safe_load(match.group(1))
        except Exception:
            return None
    return None


class SwarmAgent:
    """Unified agent. Stateless or stateful based on spec.stateless flag.

    Stateless: full response cycle (with tools, messaging), then exit. No persistence.
    Stateful: persists connection, receives messages, stays alive between responses.
    """

    def __init__(
        self,
        spec: AgentSpec[T],
        backend: AgentBackend | None = None,
        channel_bus: ChannelBus | None = None,
        cancellation: CancellationToken | None = None,
        pause: PauseToken | None = None,
        render_vars: dict[str, Any] | None = None,
        on_event: EventCallback | None = None,
        mcp_servers_override: dict[str, Any] | None = None,
        system_prompt_override: str | None = None,
        wait_after_completion: bool = True,
        backend_factory: Callable[[], AgentBackend] | None = None,
        cwd: str | None = None,
        nudge_monitor: Any = None,
        should_exit: Callable[[], bool] | None = None,
        swarm_name: str = "",
    ) -> None:
        # Default backend_factory to ClaudeBackend (lazy import to avoid cycles)
        if backend_factory is None:
            def _default_backend_factory() -> AgentBackend:
                from ._claude_backend import ClaudeBackend
                return ClaudeBackend()
            backend_factory = _default_backend_factory

        self.spec = spec
        self.backend = backend or backend_factory()
        self.channel_bus = channel_bus or ChannelBus()
        self.cancellation = cancellation or CancellationToken()
        self.pause = pause or PauseToken()
        self._backend_lock = asyncio.Lock()
        self._render_vars = render_vars or {}
        self._on_event = on_event
        self._mcp_servers_override = mcp_servers_override
        self._system_prompt_override = system_prompt_override
        self._wait_after_completion = wait_after_completion and not spec.stateless
        self._backend_factory = backend_factory
        self._cwd = cwd
        self._swarm_name = swarm_name
        self.swarm = None  # Set by Swarm._run_node_inner — gives module access to registry/topology
        self._nudge_monitor = nudge_monitor
        self._should_exit = should_exit
        self._last_emit_time = time.monotonic()
        self._hooks: dict[str, Any] | None = None

    # ─── Event emission ──────────────────────────────────────────────────

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
        if time.monotonic() - self._last_emit_time >= 5.0:
            await self._emit("heartbeat", "working...")

    # ─── Config building ─────────────────────────────────────────────────

    CHECKPOINT_SYSTEM_HINT = (
        "\nYou may receive a [CHECKPOINT] request. When you do, follow the instructions in that message."
    )

    def _build_config(self) -> BackendConfig:
        output_format = None
        if isinstance(self.spec.result_parser, JsonSchemaParser):
            output_format = self.spec.result_parser.get_output_format()

        mcp_servers = self._mcp_servers_override or self.spec.mcp_servers or None
        system_prompt = self._system_prompt_override or self.spec.system_prompt

        # Minimal hint for checkpointable agents (full instructions sent at checkpoint time)
        if self.spec.checkpointable and system_prompt:
            system_prompt = system_prompt + self.CHECKPOINT_SYSTEM_HINT

        allowed_tools = self.spec.tools.to_claude_allowed() if self.spec.tools else []
        disallowed_tools = self.spec.tools.to_claude_disallowed() if self.spec.tools else []

        has_file_tools = any(
            t.startswith("Read") or t.startswith("Write") or t.startswith("Edit") for t in allowed_tools
        )
        permission_mode = "bypassPermissions"

        # Inject path guidance for agents with file tools
        if has_file_tools and system_prompt:
            system_prompt = system_prompt + (
                "\n\nPATH RULES: ALWAYS use relative paths from the project root. "
                "Example: Read({'file_path': 'StrataAgent/Sandbox/Stub.lean'}) "
                "NOT Read({'file_path': '/local/home/.../StrataAgent/Sandbox/Stub.lean'}). "
                "Absolute system paths will be DENIED."
            )

        if mcp_servers and "agent_messaging" in mcp_servers:
            messaging_tools = ["mcp__agent_messaging__send_message", "mcp__agent_messaging__get_time"]
            if not self.spec.reply_only:
                messaging_tools.append("mcp__agent_messaging__check_messages")
            allowed_tools = allowed_tools + messaging_tools
        if mcp_servers and "agent_directory" in mcp_servers:
            allowed_tools = allowed_tools + [
                "mcp__agent_directory__list_agents",
            ]
        if mcp_servers and "agent_spawn" in mcp_servers:
            allowed_tools = allowed_tools + [
                "mcp__agent_spawn__sleep",
                "mcp__agent_spawn__my_workspace",
                "mcp__agent_spawn__done",
            ]

        return BackendConfig(
            allowed_tools=allowed_tools,
            disallowed_tools=disallowed_tools,
            permission_mode=permission_mode,
            max_turns=self.spec.max_turns,
            max_budget_usd=self.spec.max_budget_usd,
            model=self.spec.model,
            system_prompt=system_prompt,
            output_format=output_format,
            extra={"mcp_servers": mcp_servers} if mcp_servers else None,
            cwd=self._cwd,
            resume_session_id=self.spec.resume_session_id,
            hooks=self._hooks,
        )

    # ─── Response consumption ────────────────────────────────────────────

    async def _consume_response(self, result: AgentResult[T], start_time: float,
                                query: str | None = None) -> bool:
        """Send query (if given) + consume response from backend, under lock.
        Returns True to continue outer loop, False to break."""
        async with self._backend_lock:
            if query:
                await self._emit("message", "[Sending query to backend...]")
                await self.backend.send_query(query)
                await self._emit("message", "[Query sent]")
            return await self._consume_response_inner(result, start_time)

    async def _consume_response_inner(self, result: AgentResult[T], start_time: float) -> bool:
        """Inner consume logic (called under lock)."""
        await self._emit("message", "[Waiting for backend response...]")
        self._last_message_time = time.monotonic()  # watchdog timestamp
        msg_iter = self.backend.receive_messages().__aiter__()

        while True:
            try:
                stall_timeout = None if self.spec.ignore_stall else STALL_TIMEOUT
                await self._emit_heartbeat_if_needed()
                await self._emit("message", "[Waiting for backend response...]")
                message = await asyncio.wait_for(msg_iter.__anext__(), timeout=stall_timeout)
                # Only reset watchdog on substantive messages (not heartbeats)
                if message.type != "heartbeat":
                    self._last_message_time = time.monotonic()
                else:
                    # Heartbeat received but check if we've been stalled too long
                    elapsed = time.monotonic() - self._last_message_time
                    if stall_timeout and elapsed > stall_timeout:
                        raise asyncio.TimeoutError()
            except StopAsyncIteration:
                return True
            except asyncio.TimeoutError:
                logger.warning(f"[STALL] {self.spec.name}: no message in {STALL_TIMEOUT}s")
                await self._emit("message", f"[STALL DETECTED] No response for {STALL_TIMEOUT}s — reconnecting session")
                await self._emit("stall", f"stalled_for_{STALL_TIMEOUT}s")
                # Kill dead subprocess, then reconnect with same session_id
                try:
                    await self.backend.disconnect()
                except Exception:
                    pass
                await asyncio.sleep(5)  # cooldown before reconnecting
                try:
                    reconnected = await self.backend.reconnect()
                    if reconnected:
                        await self._emit("message", "[STALL] Reconnected successfully")
                    else:
                        await self._emit("message", "[STALL] Reconnect failed — session lost")
                except Exception:
                    await self._emit("message", "[STALL] Reconnect raised exception")
                return True
            except (ConnectionError, OSError, RuntimeError) as e:
                logger.warning(f"[DISCONNECT] {self.spec.name}: {e}")
                try:
                    if await self.backend.reconnect():
                        return True
                except Exception:
                    pass
                raise

            if self.spec.timeout_seconds:
                elapsed = time.monotonic() - start_time
                if elapsed >= self.spec.timeout_seconds:
                    await self.backend.interrupt()
                    result.halted_by = "timeout"
                    result.status = AgentStatus.FAILED
                    return False

            if self.cancellation.is_cancelled:
                await self.backend.interrupt()
                result.halted_by = "cancelled"
                result.status = AgentStatus.CANCELLED
                return False

            await self._emit_heartbeat_if_needed()

            # Session/model tracking
            if not result.session_id and hasattr(self.backend, '_session_id') and self.backend._session_id:
                result.session_id = self.backend._session_id
                await self._emit("session_id", self.backend._session_id)
            if hasattr(self.backend, 'model_name') and self.backend.model_name and not getattr(result, '_model_emitted', False):
                await self._emit("model_name", self.backend.model_name)
                result._model_emitted = True

            # Emit to UI
            if message.type == "text" and message.content:
                await self._emit("message", message.content)
            elif message.type == "tool_use" and message.content:
                await self._emit("message", f"[tool] {message.content}")
                await self._emit("tool_use", message.content)
            elif message.type == "tool_result" and message.content:
                await self._emit("message", f"[tool_result] {message.content}")
            elif message.type == "usage":
                result.cost_usd = message.cost_usd
                result.num_turns = message.num_turns
                await self._emit("cost_estimate", message.cost_usd)

                # Track turn count for budget hook
                if self.spec.max_turns and message.num_turns:
                    self._current_turns = message.num_turns
                continue

            # Halt predicate
            if self.spec.halt_when and self.spec.halt_when.should_halt_on_messages(self.backend.messages):
                await self.backend.interrupt()
                result.halted_by = "predicate"
                result.status = AgentStatus.HALTED
                return False

            # Result message
            if message.type == "result":
                result.raw_result = message.raw_result
                result.structured_output = message.structured_output
                result.cost_usd = message.cost_usd
                result.num_turns = message.num_turns
                result.session_id = message.session_id
                result.duration_ms = message.duration_ms
                await self._emit("cost_update", message.cost_usd)
                if message.session_id:
                    await self._emit("session_id", message.session_id)
                if self.spec.result_parser:
                    result.output = self.spec.result_parser.parse(
                        message.raw_result, message.structured_output
                    )
                    result.structured_output = result.output
                    # If parse failed but we have raw text, ask the LLM to retry with proper schema
                    if result.output is None and message.raw_result:
                        # Build a helpful retry message with schema details
                        schema_hint = ""
                        if isinstance(self.spec.result_parser, JsonSchemaParser):
                            fields = self.spec.result_parser.get_field_hints()
                            if fields:
                                schema_hint = f"\n\nRequired fields: {fields}"
                        raw_preview = message.raw_result[:200] if message.raw_result else ""
                        await self._emit("message", "[Parse error — requesting structured output retry]")
                        await self.backend.send_query(
                            f"Your response could not be parsed as structured output. "
                            f"You MUST call the StructuredOutput tool (not just write text).{schema_hint}\n\n"
                            f"What I received (not valid): {raw_preview!r}\n\n"
                            f"Call StructuredOutput now with the correct fields."
                        )
                        continue  # loop back to consume the retry response
                if self.spec.halt_when and self.spec.halt_when.should_halt_on_result(
                    result.output, result.raw_result
                ):
                    result.halted_by = "predicate"
                    result.status = AgentStatus.HALTED
                    return False
                if message.stop_reason == "max_turns":
                    result.halted_by = "max_turns"
                elif message.stop_reason == "budget":
                    result.halted_by = "budget"

        return True  # pragma: no cover

    # ─── Wait for wakeup (stateful only) ─────────────────────────────────

    async def _wait_for_wakeup(self, result: AgentResult[T]) -> str | None:
        """Block until a message arrives. Returns the injection string, or None if cancelled."""
        result.status = AgentStatus.COMPLETED
        await self._emit("status_change", AgentStatus.COMPLETED.value)
        await self._emit("message", "[Waiting for messages...]")

        while not self.cancellation.is_cancelled:
            messages_ch = self.channel_bus.get_or_create(f"{self.spec.name}:messages")
            msg = await messages_ch.receive(timeout=None)
            if msg:
                result.status = AgentStatus.RUNNING
                await self._emit("status_change", AgentStatus.RUNNING.value)
                ts = datetime.now().strftime("%H:%M:%S")
                if self.spec.reply_only and self._mcp_servers_override and msg.sender != "TipAgent":
                    ms = self._mcp_servers_override.get("agent_messaging")
                    if ms and isinstance(ms, dict) and "_pending_replies" in ms:
                        ms["_pending_replies"].append(msg.sender)
                injection = f"[{ts}] [From {msg.sender}]: {msg.payload}"
                logger.info(f"[WAKE] {self.spec.name}: from '{msg.sender}'")
                await self._emit("message", injection)
                return injection

        result.halted_by = "cancelled"
        result.status = AgentStatus.CANCELLED
        return None

    # ─── Crash recovery (stateful only) ──────────────────────────────────

    async def _attempt_recovery(self, result: AgentResult[T], config: BackendConfig) -> bool:
        try:
            if await self.backend.reconnect():
                history = await self.backend.get_message_history()
                if history:
                    self.backend._messages = history
                await self.backend.send_query("[SYSTEM]: You were disconnected. Continue.")
                async for message in self.backend.receive_messages():
                    if message.type == "text" and message.content:
                        await self._emit("message", message.content)
                    elif message.type == "result":
                        result.raw_result = message.raw_result
                        result.cost_usd = message.cost_usd
                return True
        except Exception as e:
            logger.error(f"[RETRY] {self.spec.name}: reconnect failed: {e}")
        return False

    # ─── AI control handoff ─────────────────────────────────────────────

    async def run_ai(
        self,
        inp: Any = None,
        result_type: type[T] | None = None,
        max_turns: int | None = None,
    ) -> AgentResult[T]:
        """Hand control to the LLM on the existing session.

        The session persists between run_ai() calls — backend.connect() is
        idempotent (no-op if already connected). The agent retains full
        conversation history across calls.

        Args:
            inp: Optional query to send. None = agent picks up from inbox.
            result_type: Force structured output. None = freeform text.
            max_turns: Cap LLM turns for this call. Prevents runaway.
        """
        saved_wait = self._wait_after_completion
        saved_turns = self.spec.max_turns
        self._wait_after_completion = False
        if max_turns is not None:
            self.spec.max_turns = max_turns
        try:
            return await self._run_inner(inp, result_type)
        finally:
            self._wait_after_completion = saved_wait
            self.spec.max_turns = saved_turns

    async def run_checkpoint(self) -> str:
        """Generate a checkpoint handoff note.

        For LLM agents: queries backend with [CHECKPOINT], collects response.
        For module agents: serializes _workflow_state.
        Both combined into one .md file (handoff text first, machine state last).

        Returns:
            Markdown string suitable for resume.
        """
        import yaml as _yaml
        from dataclasses import asdict as _asdict

        parts: list[str] = []
        parts.append(f"# {self.spec.name} Checkpoint\n")

        # LLM agents (non-module): query backend for handoff text
        if not self.spec.module:
            instructions = self.spec.checkpoint_prompt or (
                "Generate a detailed handoff note so a successor can continue your work. "
                "Include: current state, what's done, what's in progress, what's remaining, "
                "key context, and recommended next steps."
            )
            cp_result: AgentResult = AgentResult(name=self.spec.name, status=AgentStatus.RUNNING)
            await self._consume_response(cp_result, time.monotonic(), query=f"[CHECKPOINT] {instructions}")
            if cp_result.raw_result:
                parts.append(cp_result.raw_result)
                parts.append("")

        # Module agents: serialize workflow state (machine-readable, at the end)
        workflow_state = getattr(self, '_workflow_state', None)
        if workflow_state:
            parts.append("## Machine State")
            parts.append("```yaml")
            state_dict = _asdict(workflow_state) if hasattr(workflow_state, '__dataclass_fields__') else workflow_state
            parts.append(_yaml.dump(state_dict, default_flow_style=False).strip())
            parts.append("```")

        handoff = "\n".join(parts)
        self.backend._last_handoff = handoff
        logger.info(f"[CHECKPOINT] {self.spec.name}: generated {len(handoff)} chars")
        return handoff

    # ─── Main run ────────────────────────────────────────────────────────

    async def run(self, inp: Any = None, result_type: type[T] | None = None) -> AgentResult[T]:
        """Run the agent.

        Args:
            inp: For stateless agents — any object with __str__. Becomes the task prompt.
                 If None, uses spec.prompt. Ignored for stateful agents.
            result_type: If provided, sets result_parser for typed structured output.
                         The response is validated against this type.

        If spec.module is set, the module's run_workflow() is called instead of
        the default agent loop. The module receives (agent, inp, result_type).
        """
        # Hybrid/custom agent: delegate to module
        if self.spec.module:
            import importlib
            mod = importlib.import_module(self.spec.module)
            return await mod.run_workflow(self, inp, result_type)

        return await self._run_inner(inp, result_type)

    async def _run_inner(self, inp: Any = None, result_type: type[T] | None = None) -> AgentResult[T]:
        """The actual agent loop. Called by run() (after module check) and run_ai() (direct)."""
        if inp is not None:
            prompt = str(inp)
        else:
            prompt = render_prompt(self.spec.prompt, self._render_vars)

        if result_type is not None:
            self.spec.result_parser = JsonSchemaParser(output_type=result_type)
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

        # Stateless: guarantee fresh backend on every run
        if self.spec.stateless and self._backend_factory:
            self.backend = self._backend_factory()

        try:
            logger.info(f"[START] {self.spec.name}: connecting...")
            await self.backend.connect(config)
            if hasattr(self.backend, '_session_id') and self.backend._session_id:
                await self._emit("session_id", self.backend._session_id)
            # Only resume sessions for stateful agents (stateless = always fresh)
            if not self.spec.stateless and self.spec.resume_session_id:
                history = await self.backend.get_message_history()
                if history:
                    self.backend._messages = history
        except Exception as e:
            result.halted_by = "failed"
            result.status = AgentStatus.FAILED
            await self._emit("status_change", AgentStatus.FAILED.value)
            await self._emit("message", f"[ERROR] Failed to connect: {e}")
            return result

        has_messaging = bool(
            self._mcp_servers_override and "agent_messaging" in self._mcp_servers_override
        )

        try:
            # First send+consume (initial prompt)
            should_continue = await self._consume_response(result, start_time, query=prompt)

            while should_continue:
                if result.halted_by != "completion" or self.cancellation.is_cancelled:
                    break
                if self._should_exit and self._should_exit():
                    result.halted_by = "exit_signal"
                    await self._emit("status_change", "exiting")
                    break

                # Yield to event loop between cycles
                await asyncio.sleep(0)

                # Context management (stateful only)
                if not self.spec.stateless:
                    ctx_pct = await self.backend.get_context_percentage()
                    if ctx_pct is not None and ctx_pct >= 70.0:
                        if self.spec.checkpointable:
                            # Checkpointable agents: handoff-restart instead of compact
                            # Generate handoff, then signal exit for fresh restart
                            logger.info(f"[HANDOFF-RESTART] {self.spec.name}: context at {ctx_pct:.0f}%")
                            await self._emit("message", f"[Context at {ctx_pct:.0f}% — generating handoff for restart]")
                            await self.run_checkpoint()
                            result.halted_by = "context_handoff"
                            await self._emit("status_change", "context_handoff")
                            break
                        elif self.backend.supports_compaction:
                            # Non-checkpointable: fall back to compact
                            await self.backend.compact()

                # Check for pending messages
                if has_messaging:
                    messages_ch = self.channel_bus.get_or_create(f"{self.spec.name}:messages")
                    msg = await messages_ch.receive(timeout=0.1)
                    if msg:
                        if self.spec.reply_only and self._mcp_servers_override and msg.sender != "TipAgent":
                            ms = self._mcp_servers_override.get("agent_messaging")
                            if ms and isinstance(ms, dict) and "_pending_replies" in ms:
                                ms["_pending_replies"].append(msg.sender)
                        await self._emit("message_received", f"from:{msg.sender}")
                        ts = datetime.now().strftime("%H:%M:%S")
                        injection = f"[{ts}] [From {msg.sender}]: {msg.payload}"
                        await self._emit("message", injection)
                        # Send + consume under lock
                        should_continue = await self._consume_response(result, start_time, query=injection)
                        continue

                # Stateless: exit after first response cycle
                # Stateful: wait for more messages or exit
                if not self._wait_after_completion:
                    break

                wakeup_query = await self._wait_for_wakeup(result)
                if wakeup_query is None:
                    break
                # Send + consume the wakeup message under lock
                should_continue = await self._consume_response(result, start_time, query=wakeup_query)

        except Exception as e:
            logger.error(f"[ERROR] {self.spec.name}: crashed: {e}")
            await self._emit("message", f"[ERROR] Agent crashed: {e}")
            if not self.spec.stateless:
                recovered = await self._attempt_recovery(result, config)
                if not recovered:
                    if result.halted_by == "completion":
                        result.halted_by = "failed"
                    result.status = AgentStatus.FAILED
                    await self._emit("status_change", AgentStatus.FAILED.value)
            else:
                result.halted_by = "failed"
                result.status = AgentStatus.FAILED
                await self._emit("status_change", AgentStatus.FAILED.value)
        finally:
            # Don't disconnect if this is a run_ai() call from a module —
            # the session must persist between run_ai() calls.
            # Only disconnect when _wait_after_completion is True (normal agent lifecycle)
            # or for stateless agents.
            if self._wait_after_completion or self.spec.stateless:
                try:
                    await self.backend.disconnect()
                except Exception:
                    pass

        if result.status == AgentStatus.RUNNING:
            result.status = AgentStatus.COMPLETED
            await self._emit("status_change", AgentStatus.COMPLETED.value)

        result.duration_ms = int((time.monotonic() - start_time) * 1000)
        out_ch = self.channel_bus.get_or_create(f"{self.spec.name}:result")
        await out_ch.send(ChannelMessage(sender=self.spec.name, payload=result))
        return result
