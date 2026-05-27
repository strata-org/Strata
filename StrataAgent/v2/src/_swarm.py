from __future__ import annotations

import asyncio
import logging
import re
from collections.abc import Awaitable, Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ._agent import EventCallback, SwarmAgent
from ._backend import AgentBackend
from ._channels import ChannelBus
from ._checkpoint import CheckpointManager
from ._directory import create_directory_server
from ._messaging import create_messaging_server
from ._nudge import NudgeMonitor
from ._spawn import create_spawn_server
from ._telemetry import TelemetryEvent, TelemetryStream
from ._tokens import CancellationToken, PauseToken
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus, ShardConfig, SwarmContext

logger = logging.getLogger("strataswarm.swarm")


class ExecutionMode:
    AWAIT_ALL = "all"
    AWAIT_FIRST = "first"
    FIRE_FORGET = "forget"


@dataclass
class AgentNode:
    spec: AgentSpec[Any]
    depends_on: list[str] = field(default_factory=list)
    render_vars: dict[str, Any] = field(default_factory=dict)


class Swarm:
    def __init__(
        self,
        backend_factory: Callable[[], AgentBackend],
        context: SwarmContext | None = None,
        enable_messaging: bool = True,
        wait_after_completion: bool = False,
        name: str = "",
        cwd: str | None = None,
        checkpoint_dir: str | None = None,
        nudge_module: str | None = None,
    ) -> None:
        self._nodes: dict[str, AgentNode] = {}
        self._results: dict[str, AgentResult[Any]] = {}
        self._tasks: dict[str, asyncio.Task[AgentResult[Any]]] = {}
        self._cancellation = CancellationToken()
        self._pause_tokens: dict[str, PauseToken] = {}
        self._pending_successions: dict[str, AgentSpec[Any]] = {}
        self._session_history: dict[str, list[str]] = {}
        self._channel_bus = ChannelBus()
        self._context = context or SwarmContext()
        self._backend_factory = backend_factory
        self._event_callback: EventCallback | None = None
        self._enable_messaging = enable_messaging
        self._cwd = cwd
        self._wait_after_completion = wait_after_completion
        self._name = name
        self._visibility_graph: dict[str, set[str]] = {}
        self._sharded_agents: dict[str, ShardConfig] = {}
        self._shard_counters: dict[str, int] = {}
        self._telemetry = TelemetryStream()
        self._nudge_monitor = NudgeMonitor(
            nudge_module, self._telemetry,
            channel_bus=self._channel_bus,
            check_interval=30.0,
        )
        self._live_session_ids: dict[str, str] = {}
        self._checkpoint_manager: CheckpointManager | None = None
        if checkpoint_dir:
            self._checkpoint_manager = CheckpointManager(self, Path(checkpoint_dir))

    @property
    def name(self) -> str:
        return self._name

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
        self._event_callback = callback

    def _record_tool_call(self, agent_name: str, tool_name: str, args: dict) -> None:
        """Record a tool call in telemetry and update pending replies tracker."""
        import time as _time
        if tool_name == "send_message":
            event_type = "message_sent"
            # Resolve pending reply: agent responded to someone
            recipient = args.get("to")
            if recipient:
                self._nudge_monitor.pending.resolve_pending(agent_name, recipient)
        elif tool_name == "message_received":
            event_type = "message_received"
            # Track pending reply: agent owes a response to sender
            sender = args.get("from")
            if sender:
                self._nudge_monitor.pending.add_pending(agent_name, sender)
        else:
            event_type = "tool_call"
        self._telemetry.record(TelemetryEvent(
            agent=agent_name,
            timestamp=_time.time(),
            event_type=event_type,
            tool_name=tool_name,
            tool_args=args,
            target=args.get("to"),
            source=args.get("from"),
        ))

    async def _on_event_with_telemetry(self, event: AgentEvent) -> None:
        """Wraps the user's event callback to also record telemetry."""
        # Track session IDs as they're emitted by agents
        if event.event_type == "session_id" and event.data:
            self._live_session_ids[event.agent_name] = str(event.data)

        # Record telemetry from agent events
        if event.event_type == "tool_use" and event.data:
            data = str(event.data)
            # Extract tool name from "ToolName({...})" format
            tool_name = data.split("(")[0] if "(" in data else data[:50]
            self._telemetry.record(TelemetryEvent(
                agent=event.agent_name,
                timestamp=event.timestamp_ms / 1000.0,
                event_type="tool_call",
                tool_name=tool_name,
                tool_args={"raw": data[:200]},
            ))
        elif event.event_type == "message_received" and event.data:
            data = str(event.data)
            source = data.replace("from:", "") if data.startswith("from:") else data
            self._telemetry.record(TelemetryEvent(
                agent=event.agent_name,
                timestamp=event.timestamp_ms / 1000.0,
                event_type="message_received",
                source=source,
            ))
            # Track pending reply (framework injection path)
            if source and source != "TipAgent":
                self._nudge_monitor.pending.add_pending(event.agent_name, source)
        elif event.event_type == "message" and event.data:
            data = str(event.data)
            if data.startswith("[tool]"):
                tool_name = data[6:].strip().split("(")[0] if "(" in data else data[6:50]
                self._telemetry.record(TelemetryEvent(
                    agent=event.agent_name,
                    timestamp=event.timestamp_ms / 1000.0,
                    event_type="tool_call",
                    tool_name=tool_name,
                    tool_args={"raw": data[:200]},
                ))
            elif "sent to" in data.lower() or "Message sent to" in data:
                self._telemetry.record(TelemetryEvent(
                    agent=event.agent_name,
                    timestamp=event.timestamp_ms / 1000.0,
                    event_type="message_sent",
                    target=data,
                ))
        # Forward to user callback
        if self._event_callback:
            await self._event_callback(event)

    def add(
        self,
        spec: AgentSpec[Any],
        depends_on: list[str] | None = None,
        render_vars: dict[str, Any] | None = None,
    ) -> Swarm:
        if self._enable_messaging and not spec.system_prompt:
            raise ValueError(
                f"AgentSpec '{spec.name}' must have a system_prompt when messaging is enabled. "
                f"The system prompt should describe the agent's role and the other agents it can talk to."
            )
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
        if name in self._tasks:
            self._tasks[name].cancel()

    def pause(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].pause()
        # Also interrupt the backend to stop mid-response waiting
        if agent_name in self._tasks and not self._tasks[agent_name].done():
            # The agent will check the pause flag on next loop iteration
            logger.info(f"[PAUSE] {agent_name}: paused")

    def resume(self, agent_name: str) -> None:
        self._pause_tokens[agent_name].resume()

    async def send_to_agent(self, agent_name: str, sender: str, payload: Any) -> None:
        messages_channel = f"{agent_name}:messages"
        await self._channel_bus.send_to(messages_channel, sender=sender, payload=payload)

    def _is_shard_instance(self, name: str) -> bool:
        """Check if a node name is a shard instance (e.g. 'ProofValidator_0')."""
        for logical_name in self._sharded_agents:
            if name.startswith(f"{logical_name}_") and name[len(logical_name) + 1:].isdigit():
                return True
        return False

    def _build_visibility_graph(self) -> None:
        """Build the visibility graph from agent specs. Called before run().

        Sharded agents appear under their LOGICAL name in the graph (e.g., "ProofValidator")
        even though only instances (ProofValidator_0, _1) exist in _nodes.
        Messaging routes through the logical name transparently.
        """
        self._visibility_graph = {}

        # Collect non-shard-instance nodes for visibility purposes
        logical_nodes = {
            name: node for name, node in self._nodes.items()
            if not self._is_shard_instance(name)
        }

        # Also include sharded agents as logical entries (use first instance's spec)
        for logical_name, shard_config in self._sharded_agents.items():
            instance_name = f"{logical_name}_0"
            if instance_name in self._nodes:
                logical_nodes[logical_name] = self._nodes[instance_name]

        # Identify service agents (visibility == "all")
        service_agents = {
            name for name, node in logical_nodes.items()
            if node.spec.visibility == "all"
        }

        for name, node in logical_nodes.items():
            spec = node.spec
            if spec.visibility == "all":
                # Service agents can message everyone except themselves
                self._visibility_graph[name] = set(logical_nodes.keys()) - {name}
            else:
                # Restricted agents can message their can_see list + all service agents
                can_see: list[str] = []
                if isinstance(spec.visibility, dict):
                    can_see = spec.visibility.get("can_see", [])
                self._visibility_graph[name] = (set(can_see) | service_agents) - {name}

        # Shard instances inherit their logical group's visibility
        for logical_name in self._sharded_agents:
            logical_visibility = self._visibility_graph.get(logical_name, set())
            for name in self._nodes:
                if name.startswith(f"{logical_name}_") and name[len(logical_name) + 1:].isdigit():
                    self._visibility_graph[name] = set(logical_visibility)

    def _on_agent_spawned(self, child_name: str, parent_name: str) -> None:
        """Update visibility graph when a sub-agent is spawned.

        - Child inherits parent's full visibility + parent itself.
        - Parent can see child.
        - Everyone who could see parent can now also see child.
        """
        parent_visible = self._visibility_graph.get(parent_name, set())
        # Child can see everything parent can see, plus parent
        self._visibility_graph[child_name] = parent_visible | {parent_name}
        # Parent can see child
        self._visibility_graph[parent_name].add(child_name)
        # Everyone who can see parent can also see child
        for agent, visible_set in self._visibility_graph.items():
            if agent == child_name:
                continue
            if parent_name in visible_set:
                visible_set.add(child_name)

    def _build_roster(self, agent_name: str) -> str:
        """Generate a collaborator roster for restricted agents.

        Service agents (visibility == "all") get no roster.
        Restricted agents get a list of all agents in their visibility set.
        """
        spec = self._nodes[agent_name].spec

        # Service agents get no roster
        if spec.visibility == "all":
            return ""

        visible = self._visibility_graph.get(agent_name, set())
        lines = []
        for other_name in sorted(visible):
            # Resolve node — for sharded agents, use first instance
            if other_name in self._nodes:
                desc = self._nodes[other_name].spec.description or other_name
            elif other_name in self._sharded_agents:
                instance = f"{other_name}_0"
                if instance in self._nodes:
                    desc = self._nodes[instance].spec.description or other_name
                else:
                    continue
            else:
                continue
            lines.append(f"- {other_name}: {desc}")

        if not lines:
            return ""

        return (
            "\n\n=== YOUR COLLABORATORS ===\n"
            "You can message these agents:\n"
            + "\n".join(lines)
            + "\nUse list_agents() to refresh — new agents may join at runtime."
            "\n==========================="
        )

    def can_message(self, sender: str, recipient: str) -> bool:
        """Check if sender is allowed to message recipient.

        If the visibility graph is empty (not yet built), default to allowing
        all messages for backward compatibility.
        """
        if not self._visibility_graph:
            return True
        return recipient in self._visibility_graph.get(sender, set())

    def _route_message(self, logical_name: str, message: str) -> str:
        """Resolve logical agent name to physical instance for sharded agents."""
        if logical_name not in self._sharded_agents:
            return logical_name
        shard = self._sharded_agents[logical_name]
        if shard.routing == "hash":
            key = self._extract_routing_key(message, shard.routing_key)
            idx = hash(key) % shard.replicas
        elif shard.routing == "round_robin":
            idx = self._shard_counters.get(logical_name, 0)
            self._shard_counters[logical_name] = (idx + 1) % shard.replicas
        else:
            idx = 0
        return f"{logical_name}_{idx}"

    def _extract_routing_key(self, message: str, key_name: str | None) -> str:
        """Extract routing key from message for hash-based routing."""
        if not key_name:
            return message
        paths = re.findall(r"[\w/.-]+\.lean", message)
        return paths[0] if paths else message

    def _get_sender_display(self, agent_name: str) -> str:
        """Rewrite sharded instance name to logical name for outbound messages."""
        for logical_name in self._sharded_agents:
            prefix = f"{logical_name}_"
            if agent_name.startswith(prefix) and agent_name[len(prefix):].isdigit():
                return logical_name
        return agent_name

    def get_agent_session_id(self, agent_name: str) -> str | None:
        # Check live session IDs first (captured from events during run)
        if agent_name in self._live_session_ids:
            return self._live_session_ids[agent_name]
        # Fallback: check completed results
        if agent_name in self._results:
            return self._results[agent_name].session_id
        return None

    async def _run_node(self, name: str) -> AgentResult[Any]:
        logger.info(f"[NODE] {name}: _run_node started")
        try:
            return await self._run_node_inner(name)
        except Exception as e:
            logger.error(f"[NODE] {name}: _run_node CRASHED: {e}")
            import traceback
            traceback.print_exc()
            raise

    async def _run_node_inner(self, name: str) -> AgentResult[Any]:
        node = self._nodes[name]

        if node.depends_on:
            dep_tasks = [self._tasks[dep] for dep in node.depends_on if dep in self._tasks]
            if dep_tasks:
                await asyncio.gather(*dep_tasks, return_exceptions=True)
                for dep_name in node.depends_on:
                    if dep_name in self._results:
                        dep_result = self._results[dep_name]
                        if dep_result.halted_by == "cancelled":
                            result: AgentResult[Any] = AgentResult(
                                name=name, halted_by="dependency", status=AgentStatus.CANCELLED
                            )
                            self._results[name] = result
                            return result

        render_vars = dict(node.render_vars)
        for dep_name in node.depends_on:
            if dep_name in self._results:
                render_vars[dep_name] = self._results[dep_name]
        render_vars["context"] = await self._context.snapshot()

        backend = self._backend_factory()

        mcp_servers: dict[str, Any] | None = None
        combined_system_prompt: str | None = None

        if self._enable_messaging:
            other_agents = [n for n in self._nodes if n != name]
            messaging_server = create_messaging_server(
                agent_name=name,
                channel_bus=self._channel_bus,
                known_agents=other_agents,
                can_message=self.can_message,
                route_message=self._route_message,
                get_sender_display=self._get_sender_display,
                on_tool_call=self._record_tool_call,
                reply_only_mode=node.spec.reply_only,
            )
            mcp_servers = dict(node.spec.mcp_servers)
            mcp_servers["agent_messaging"] = messaging_server
            directory_server = create_directory_server(agent_name=name, swarm=self)
            mcp_servers["agent_directory"] = directory_server

            agents_note = (
                f"- send_message(to, message): Send a message to any agent by name. "
            )
            cwd_note = (
                f"Project root: {self._cwd}\n"
                f"CRITICAL: When using Read, Edit, or Write tools, ALWAYS use RELATIVE paths "
                f"(e.g. 'src/module/file.ext'). "
                f"NEVER use absolute paths starting with /. "
                f"The tools resolve paths from the project root automatically.\n"
            ) if self._cwd else ""
            if node.spec.reply_only:
                messaging_suffix = (
                    f"\n\n=== ENVIRONMENT ===\n"
                    f"{cwd_note}"
                    f"===================\n"
                    f"\n=== MESSAGING (REPLY-ONLY MODE) ===\n"
                    f"Your agent name is '{name}'.\n"
                    f"You are a REPLY-ONLY agent. You can ONLY respond to whoever messaged you.\n"
                    f"- send_message(to, message): Send a response. You MUST reply to the agent\n"
                    f"  who asked you, in the order they asked (FIFO). If you try to message\n"
                    f"  someone who didn't ask you anything, you will get an error.\n"
                    f"- check_messages(): Read the next pending message from your inbox.\n"
                    f"- get_time(): Get the current timestamp.\n\n"
                    f"WORKFLOW: receive message → do the work → send_message(to=sender, message=result)\n"
                    f"You cannot initiate conversations. Only respond to requests in order.\n\n"
                    f"IMPORTANT — WAITING PROTOCOL:\n"
                    f"When you have nothing to do, simply STOP and end your turn. "
                    f"The framework will notify you when a new message arrives.\n"
                    f"================="
                )
            else:
                messaging_suffix = (
                    f"\n\n=== ENVIRONMENT ===\n"
                    f"{cwd_note}"
                    f"===================\n"
                    f"\n=== MESSAGING ===\n"
                    f"Your agent name is '{name}'.\n"
                    f"You have tools to communicate with other agents and the user:\n"
                    f"{agents_note}"
                    f"- check_messages(): Read the next pending message from your inbox.\n"
                    f"- list_agents(): Discover all agents you can communicate with and their status.\n"
                    f"- get_time(): Get the current timestamp.\n\n"
                    f"Messages you receive are tagged with the sender (e.g. '[From user]: ...').\n\n"
                    f"IMPORTANT — WAITING PROTOCOL:\n"
                    f"NEVER poll or call check_messages in a loop to wait for messages. "
                    f"When you have nothing to do, simply STOP and end your turn. "
                    f"The framework will automatically notify you when a new message arrives. "
                    f"Only call check_messages AFTER you have been notified that messages are pending. "
                    f"Polling wastes budget and is strictly forbidden.\n\n"
                    f"IMPORTANT — STALL PREVENTION:\n"
                    f"If you are processing something that takes time, emit a brief status update "
                    f"every few minutes (e.g. 'Still working on X...'). If 30 minutes pass with no "
                    f"output from you, the framework will interrupt and ask for your status.\n"
                    f"================="
                )

            # SuperAgent: inject spawn_agent tool
            if node.spec.is_super_agent:
                spawn_server = create_spawn_server(
                    parent_name=name,
                    parent_spec=node.spec,
                    channel_bus=self._channel_bus,
                    swarm=self,
                )
                mcp_servers["agent_spawn"] = spawn_server
                messaging_suffix += (
                    f"\n\n=== SUPER AGENT ===\n"
                    f"You are a SuperAgent. You can spawn sub-agents using:\n"
                    f"- spawn_agent(name, system_prompt, prompt, max_budget_usd, max_turns, timeout_seconds)\n"
                    f"- sleep(seconds): Sleep for 5-300 seconds. Use this to control your polling interval. "
                    f"Sleep longer (60-120s) when sub-agents need time, shorter (10-15s) when expecting results soon.\n\n"
                    f"Sub-agents inherit your exact tool permissions. "
                    f"You set their name, system prompt, task prompt, and budget (<= yours). "
                    f"They join the swarm and can communicate via messaging.\n"
                    f"You will be nudged every 30s if idle. Use sleep() to override this interval.\n"
                    f"==================="
                )

            # Append collaborator roster for restricted agents
            messaging_suffix += self._build_roster(name)

            combined_system_prompt = node.spec.system_prompt + messaging_suffix
        else:
            combined_system_prompt = node.spec.system_prompt

        agent: SwarmAgent[Any] = SwarmAgent(
            spec=node.spec,
            backend=backend,
            channel_bus=self._channel_bus,
            cancellation=self._cancellation,
            pause=self._pause_tokens[name],
            render_vars=render_vars,
            on_event=self._on_event_with_telemetry,
            mcp_servers_override=mcp_servers,
            system_prompt_override=combined_system_prompt,
            wait_after_completion=self._wait_after_completion,
            backend_factory=self._backend_factory,
            swarm_name=self._name,
            cwd=self._cwd,
            nudge_monitor=self._nudge_monitor,
        )

        result = await agent.run()
        self._results[name] = result
        await self._context.set(f"result:{name}", result)
        await self._check_succession(name)
        return result

    async def _check_succession(self, agent_name: str) -> None:
        """If agent designated a successor, execute the atomic swap."""
        if agent_name not in self._pending_successions:
            return
        successor_spec = self._pending_successions.pop(agent_name)
        await self._execute_succession(agent_name, successor_spec)

    async def _execute_succession(self, agent_name: str, successor_spec: Any) -> None:
        """Atomic swap: lock channel, replace agent, start successor, unlock."""
        # Checkpoint before swap
        if self._checkpoint_manager:
            self._checkpoint_manager.create(reason=f"pre_succession:{agent_name}")
        # Record old session in history
        self._session_history.setdefault(agent_name, []).append(f"pre_swap_{agent_name}")

        channel = self._channel_bus.get_or_create(f"{agent_name}:messages")
        channel.lock()
        try:
            successor_spec.name = agent_name
            self._nodes[agent_name] = type(self._nodes[agent_name])(spec=successor_spec)
            task = asyncio.create_task(self._run_node(agent_name), name=f"swarm:{agent_name}")
            self._tasks[agent_name] = task
            logger.info(f"[SUCCESSION] {agent_name} swapped to fresh instance")
        finally:
            channel.unlock()

    async def run(self, mode: str = ExecutionMode.AWAIT_ALL) -> dict[str, AgentResult[Any]]:
        logger.info(f"[SWARM] Building visibility graph for {len(self._nodes)} nodes...")
        try:
            self._build_visibility_graph()
        except Exception as e:
            logger.error(f"[SWARM] Visibility graph failed: {e}")
            import traceback
            traceback.print_exc()

        # Populate nudge monitor with agent info and start background loop
        for name, node in self._nodes.items():
            self._nudge_monitor._agents.add(name)
            if node.spec.is_super_agent:
                self._nudge_monitor._super_agents.add(name)
        self._nudge_monitor.start()
        logger.info(f"[SWARM] Visibility graph built. Starting agents...")

        for name in self._nodes:
            logger.info(f"[SWARM] Creating task for: {name}")
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
            pass

        return dict(self._results)
