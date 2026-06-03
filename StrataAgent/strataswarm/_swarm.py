from __future__ import annotations

import asyncio
import logging
import re
from collections.abc import Callable
from pathlib import Path
from typing import Any

from ._agent import EventCallback, SwarmAgent
from ._backend import AgentBackend
from ._channels import ChannelBus
from ._checkpoint import CheckpointManager
from ._directory import create_directory_server
from ._messaging import create_messaging_server
from ._nudge import NudgeMonitor
from ._registry import AgentNode, SwarmRegistry
from ._spawn import create_spawn_server
from ._telemetry import TelemetryEvent, TelemetryStream
from ._tokens import CancellationToken
from ._types import AgentEvent, AgentResult, AgentSpec, AgentStatus, SwarmContext

logger = logging.getLogger("strataswarm.swarm")


class ExecutionMode:
    AWAIT_ALL = "all"
    AWAIT_FIRST = "first"
    FIRE_FORGET = "forget"


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
        manager: str | None = None,
    ) -> None:
        self._registry = SwarmRegistry()
        self._cancellation = CancellationToken()
        self._channel_bus = ChannelBus()
        self._context = context or SwarmContext()
        self._backend_factory = backend_factory
        self._event_callback: EventCallback | None = None
        self._enable_messaging = enable_messaging
        self._cwd = cwd
        self._wait_after_completion = wait_after_completion
        self._name = name
        self._manager = manager
        self._telemetry = TelemetryStream()
        self._nudge_monitor = NudgeMonitor(
            nudge_module, self._telemetry,
            channel_bus=self._channel_bus,
            check_interval=30.0,
        )
        self._checkpoint_manager: CheckpointManager | None = None
        if checkpoint_dir:
            self._checkpoint_manager = CheckpointManager(self, Path(checkpoint_dir))

    @property
    def name(self) -> str:
        return self._name

    @property
    def context(self) -> SwarmContext:
        return self._context

    async def checkpoint(self, reason: str = "manual") -> None:
        """Trigger a swarm-wide checkpoint. Collects handoffs from all checkpointable agents."""
        if self._checkpoint_manager:
            await self._checkpoint_manager.create(reason=reason)

    @property
    def channels(self) -> ChannelBus:
        return self._channel_bus

    @property
    def results(self) -> dict[str, AgentResult[Any]]:
        return dict(self._registry.results)

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
            # Track pending reply: agent owes a response to sender (never TipAgent)
            sender = args.get("from")
            if sender and sender != "TipAgent":
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
            self._registry.session_ids[event.agent_name] = str(event.data)

        # Track model names as they're reported by backends
        if event.event_type == "model_name" and event.data:
            self._registry.models[event.agent_name] = str(event.data)

        # Track stall events — nudge monitor will send recovery tip
        if event.event_type == "stall":
            self._nudge_monitor.record_stall(event.agent_name)

        # Track live costs as they're reported
        if event.event_type in ("cost_update", "cost_estimate") and event.data:
            try:
                self._registry.costs[event.agent_name] = float(event.data)
            except (ValueError, TypeError):
                pass

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
        self._registry.add(spec, depends_on, render_vars)
        return self

    async def interrupt_agent(self, agent_name: str, message: str) -> bool:
        """Interrupt an agent's backend and send it a message. Returns True if successful."""
        backend = self._registry.backends.get(agent_name)
        if backend:
            try:
                await backend.interrupt()
            except Exception:
                pass
        # Send the interrupt message to the agent's channel
        await self.send_to_agent(agent_name, sender="user", payload=f"[INTERRUPT]: {message}")
        return True

    def cancel(self) -> None:
        self._cancellation.cancel()

    def cancel_agent(self, name: str) -> None:
        if name in self._registry.tasks:
            self._registry.tasks[name].cancel()

    def pause(self, agent_name: str) -> None:
        self._registry.pause_tokens[agent_name].pause()
        # Also interrupt the backend to stop mid-response waiting
        if agent_name in self._registry.tasks and not self._registry.tasks[agent_name].done():
            # The agent will check the pause flag on next loop iteration
            logger.info(f"[PAUSE] {agent_name}: paused")

    def resume(self, agent_name: str) -> None:
        self._registry.pause_tokens[agent_name].resume()

    async def send_to_agent(self, agent_name: str, sender: str, payload: Any) -> None:
        messages_channel = f"{agent_name}:messages"
        await self._channel_bus.send_to(messages_channel, sender=sender, payload=payload)

    def _is_shard_instance(self, name: str) -> bool:
        """Check if a node name is a shard instance (e.g. 'ProofValidator_0')."""
        for logical_name in self._registry.sharded_agents:
            if name.startswith(f"{logical_name}_") and name[len(logical_name) + 1:].isdigit():
                return True
        return False

    def _build_visibility_graph(self) -> None:
        """Build the visibility graph from agent specs. Called before run().

        Sharded agents appear under their LOGICAL name in the graph (e.g., "ProofValidator")
        even though only instances (ProofValidator_0, _1) exist in _nodes.
        Messaging routes through the logical name transparently.
        """
        self._registry.visibility_graph = {}

        # Collect non-shard-instance nodes for visibility purposes
        logical_nodes = {
            name: node for name, node in self._registry.nodes.items()
            if not self._is_shard_instance(name)
        }

        # Also include sharded agents as logical entries (use first instance's spec)
        for logical_name, shard_config in self._registry.sharded_agents.items():
            instance_name = f"{logical_name}_0"
            if instance_name in self._registry.nodes:
                logical_nodes[logical_name] = self._registry.nodes[instance_name]

        # Identify service agents (visibility == "all")
        service_agents = {
            name for name, node in logical_nodes.items()
            if node.spec.visibility == "all"
        }

        for name, node in logical_nodes.items():
            spec = node.spec
            if spec.visibility == "all":
                # Service agents can message everyone except themselves
                self._registry.visibility_graph[name] = set(logical_nodes.keys()) - {name}
            else:
                # Restricted agents can message their can_see list + all service agents
                can_see: list[str] = []
                if isinstance(spec.visibility, dict):
                    can_see = spec.visibility.get("can_see", [])
                self._registry.visibility_graph[name] = (set(can_see) | service_agents) - {name}

        # Shard instances inherit their logical group's visibility
        for logical_name in self._registry.sharded_agents:
            logical_visibility = self._registry.visibility_graph.get(logical_name, set())
            for name in self._registry.nodes:
                if name.startswith(f"{logical_name}_") and name[len(logical_name) + 1:].isdigit():
                    self._registry.visibility_graph[name] = set(logical_visibility)

    def _on_agent_spawned(self, child_name: str, parent_name: str) -> None:
        """Update visibility graph when a sub-agent is spawned.

        - Child inherits parent's full visibility + parent itself.
        - Parent can see child.
        - Everyone who could see parent can now also see child.
        """
        parent_visible = self._registry.visibility_graph.get(parent_name, set())
        # Child can see everything parent can see, plus parent
        self._registry.visibility_graph[child_name] = parent_visible | {parent_name}
        # Parent can see child
        self._registry.visibility_graph[parent_name].add(child_name)
        # Everyone who can see parent can also see child
        for agent, visible_set in self._registry.visibility_graph.items():
            if agent == child_name:
                continue
            if parent_name in visible_set:
                visible_set.add(child_name)


    def _build_roster(self, agent_name: str) -> str:
        """Generate a collaborator roster for restricted agents.

        Service agents (visibility == "all") get no roster.
        Restricted agents get a list of all agents in their visibility set.
        """
        spec = self._registry.nodes[agent_name].spec

        # Service agents get no roster
        if spec.visibility == "all":
            return ""

        visible = self._registry.visibility_graph.get(agent_name, set())
        lines = []
        for other_name in sorted(visible):
            # Resolve node — for sharded agents, use first instance
            if other_name in self._registry.nodes:
                other_spec = self._registry.nodes[other_name].spec
                desc = other_spec.description or other_name
            elif other_name in self._registry.sharded_agents:
                instance = f"{other_name}_0"
                if instance in self._registry.nodes:
                    other_spec = self._registry.nodes[instance].spec
                    desc = other_spec.description or other_name
                else:
                    continue
            else:
                continue
            # Include inbound limit if set
            limit_note = ""
            if other_spec.max_inbound_length:
                limit_note = f" [MAX {other_spec.max_inbound_length} chars]"
            lines.append(f"- {other_name}: {desc}{limit_note}")

        if not lines:
            return ""

        # Add sender's own outbound limit
        own_limit_note = ""
        if spec.max_outbound_length:
            own_limit_note = f"\nYOUR outbound limit: {spec.max_outbound_length} chars per message.\n"

        return (
            "\n\n=== YOUR COLLABORATORS ===\n"
            "You can message these agents:\n"
            + "\n".join(lines)
            + "\n" + own_limit_note
            + "Use list_agents() to refresh — new agents may join at runtime."
            "\n==========================="
        )

    async def _remove_agent(self, name: str, cancel_task: bool = True) -> None:
        """Single point of agent removal. Cleans up ALL per-agent state."""
        await self._registry.remove(name, cancel_task=cancel_task)

        # Clean up nudge monitor pending replies tracker
        self._nudge_monitor.pending._pending.pop(name, None)

        # Sync checkpoint to reflect agent removal
        if self._checkpoint_manager:
            await self._checkpoint_manager.create(reason=f"agent_removed:{name}")

        logger.info(f"[REMOVE] Agent '{name}' removed from swarm")

    def _get_inbound_limit(self, recipient: str) -> tuple[int | None, str | None]:
        """Get the inbound message limit for a recipient (resolves sharded logical names)."""
        # Check logical name for sharded agents
        if recipient in self._registry.sharded_agents:
            instance_name = f"{recipient}_0"
            node = self._registry.nodes.get(instance_name)
        else:
            node = self._registry.nodes.get(recipient)
        if node:
            return (node.spec.max_inbound_length, node.spec.max_inbound_response)
        return (None, None)

    def can_message(self, sender: str, recipient: str) -> bool:
        """Check if sender is allowed to message recipient.

        If the visibility graph is empty (not yet built), default to allowing
        all messages for backward compatibility.
        Service agents (visibility: all) can always message anyone.
        """
        if not self._registry.visibility_graph:
            return True
        # Service agents can message anyone (including dynamically spawned agents)
        sender_base = sender.rsplit("_", 1)[0] if sender not in self._registry.nodes else sender
        node = self._registry.nodes.get(sender) or self._registry.nodes.get(sender_base)
        if node and node.spec.visibility == "all":
            return True
        return recipient in self._registry.visibility_graph.get(sender, set())

    def _route_message(self, logical_name: str, message: str, sender: str = "") -> str:
        """Resolve logical agent name to physical instance for sharded agents.
        Uses affinity: if sender has talked to this service before, route to same instance."""
        if logical_name not in self._registry.sharded_agents:
            return logical_name

        shard = self._registry.sharded_agents[logical_name]

        # Affinity: if sender already has a binding, use it
        if sender:
            affinity_key = (sender, logical_name)
            if affinity_key in self._registry.affinities:
                return self._registry.affinities[affinity_key]

        # No affinity — route normally
        if shard.routing == "hash":
            key = self._extract_routing_key(message, shard.routing_key)
            idx = hash(key) % shard.replicas
        elif shard.routing == "round_robin":
            idx = self._registry.shard_counters.get(logical_name, 0)
            self._registry.shard_counters[logical_name] = (idx + 1) % shard.replicas
        else:
            idx = 0

        physical = f"{logical_name}_{idx}"

        # Establish affinity for this sender → this instance
        if sender:
            self._registry.affinities[(sender, logical_name)] = physical

        return physical

    def _extract_routing_key(self, message: str, key_name: str | None) -> str:
        """Extract routing key from message for hash-based routing."""
        if not key_name:
            return message
        paths = re.findall(r"[\w/.-]+\.lean", message)
        return paths[0] if paths else message

    def _get_sender_display(self, agent_name: str) -> str:
        """Rewrite sharded instance name to logical name for outbound messages."""
        for logical_name in self._registry.sharded_agents:
            prefix = f"{logical_name}_"
            if agent_name.startswith(prefix) and agent_name[len(prefix):].isdigit():
                return logical_name
        return agent_name

    def get_agent_session_id(self, agent_name: str) -> str | None:
        # Check live session IDs first (captured from events during run)
        if agent_name in self._registry.session_ids:
            return self._registry.session_ids[agent_name]
        # Fallback: check completed results
        if agent_name in self._registry.results:
            return self._registry.results[agent_name].session_id
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
        node = self._registry.nodes[name]

        if node.depends_on:
            dep_tasks = [self._registry.tasks[dep] for dep in node.depends_on if dep in self._registry.tasks]
            if dep_tasks:
                await asyncio.gather(*dep_tasks, return_exceptions=True)
                for dep_name in node.depends_on:
                    if dep_name in self._registry.results:
                        dep_result = self._registry.results[dep_name]
                        if dep_result.halted_by == "cancelled":
                            result: AgentResult[Any] = AgentResult(
                                name=name, halted_by="dependency", status=AgentStatus.CANCELLED
                            )
                            self._registry.results[name] = result
                            return result

        render_vars = dict(node.render_vars)
        for dep_name in node.depends_on:
            if dep_name in self._registry.results:
                render_vars[dep_name] = self._registry.results[dep_name]
        render_vars["context"] = await self._context.snapshot()

        # Use UserBackend for the virtual user agent, normal factory for others
        if getattr(node.spec, '_is_virtual', False) and name == "user" and hasattr(self, '_user_backend'):
            backend = self._user_backend
        else:
            backend = self._backend_factory()
        self._registry.backends[name] = backend

        mcp_servers: dict[str, Any] | None = None
        combined_system_prompt: str | None = None

        if self._enable_messaging:
            other_agents = [n for n in self._registry.nodes if n != name]
            # Service agents = reply_only agents (by logical name)
            service_agents = {
                n for n, nd in self._registry.nodes.items()
                if nd.spec.reply_only
            } | set(self._registry.sharded_agents.keys())

            from datetime import datetime as _dt
            agent_start_time = _dt.now()
            self._registry.start_times[name] = agent_start_time

            messaging_server = create_messaging_server(
                agent_name=name,
                channel_bus=self._channel_bus,
                known_agents=other_agents,
                can_message=self.can_message,
                route_message=self._route_message,
                get_sender_display=self._get_sender_display,
                on_tool_call=self._record_tool_call,
                reply_only_mode=node.spec.reply_only,
                known_service_agents=service_agents,
                start_time=agent_start_time,
                is_agent_alive=lambda r: r in self._registry.nodes or r in self._registry.sharded_agents,
                outbound_limit=node.spec.max_outbound_length,
                outbound_limit_response=node.spec.max_outbound_response,
                get_inbound_limit=self._get_inbound_limit,
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
            # Build message limits note for service agents
            limits_note = ""
            if node.spec.max_outbound_length or node.spec.max_inbound_length:
                parts = []
                if node.spec.max_outbound_length:
                    parts.append(f"Your responses MUST be under {node.spec.max_outbound_length} chars.")
                if node.spec.max_inbound_length:
                    parts.append(f"Messages TO you are limited to {node.spec.max_inbound_length} chars (enforced by framework).")
                limits_note = "\nMESSAGE LIMITS:\n" + " ".join(parts) + "\n"

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
                    f"You cannot initiate conversations. Only respond to requests in order.\n"
                    f"{limits_note}\n"
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

            # Spawn server: always inject for spawned children (gives them sleep tool)
            # SuperAgents get full spawn capabilities; leaf agents get sleep + my_workspace only
            if node.spec.is_super_agent or getattr(node.spec, '_spawned_by', None):
                spawn_server = create_spawn_server(
                    parent_name=name,
                    parent_spec=node.spec,
                    channel_bus=self._channel_bus,
                    swarm=self,
                )
                mcp_servers["agent_spawn"] = spawn_server

                # Build workspace info for the prompt
                ws_info = ""
                if node.spec.workspace:
                    ws = node.spec.workspace
                    ws_info = (
                        f"\n\n=== YOUR WORKSPACE ===\n"
                        f"Read:  {ws.read}\n"
                        f"Write: {ws.write}\n"
                        f"Edit:  {ws.edit}\n"
                        f"If you have file access issues, call my_workspace to check your permissions.\n"
                        f"======================"
                    )

                messaging_suffix += (
                    f"\n\n=== SUPER AGENT ===\n"
                    f"You are a SuperAgent. You can spawn sub-agents using:\n"
                    f"- spawn_agent(name, folder, system_prompt, prompt, recursive=false)\n"
                    f"  folder: subdirectory name relative to YOUR workspace.\n"
                    f"  recursive=true: child can spawn its own sub-agents.\n"
                    f"- my_workspace(): View your workspace paths and permissions.\n"
                    f"- sleep(seconds): Sleep 5-300s while waiting for sub-agents.\n"
                    f"- kill_agent(name): Kill a sub-agent you own.\n"
                    f"- interrupt_agent(name, message): Interrupt and redirect a sub-agent.\n\n"
                    f"Sub-agents get their own workspace subfolder. They can create files freely.\n"
                    f"They can talk to SearchAgent, ProofValidator, CEA, LemmaProposer directly.\n"
                    f"==================="
                    f"{ws_info}"
                )

            # Append collaborator roster for restricted agents
            messaging_suffix += self._build_roster(name)

            # Inject start time so agent knows when it began
            start_ts = agent_start_time.strftime("%Y-%m-%d %H:%M:%S")
            messaging_suffix += (
                f"\n\n=== TIMING ===\n"
                f"You started at: {start_ts}\n"
                f"Use get_time() to check elapsed time at any point.\n"
                f"==============="
            )

            combined_system_prompt = node.spec.system_prompt + messaging_suffix
            # Store base prompt for inheritance (before workspace/messaging composition)
            if not node.spec._base_system_prompt:
                node.spec._base_system_prompt = node.spec.system_prompt
        else:
            combined_system_prompt = node.spec.system_prompt

        agent: SwarmAgent[Any] = SwarmAgent(
            spec=node.spec,
            backend=backend,
            channel_bus=self._channel_bus,
            cancellation=self._cancellation,
            pause=self._registry.pause_tokens[name],
            render_vars=render_vars,
            on_event=self._on_event_with_telemetry,
            mcp_servers_override=mcp_servers,
            system_prompt_override=combined_system_prompt,
            wait_after_completion=self._wait_after_completion,
            backend_factory=self._backend_factory,
            swarm_name=self._name,
            cwd=self._cwd,
            nudge_monitor=self._nudge_monitor,
            should_exit=lambda: self._registry.exit_signals.get(name, False),
        )
        agent.swarm = self  # Give module agents access to registry/topology
        self._registry.agents[name] = agent  # Store for checkpoint access

        # Restore state from checkpoint if resuming
        agent_checkpoints = getattr(self, '_agent_checkpoints', {})
        if name in agent_checkpoints:
            handoff_md = agent_checkpoints[name]
            from ._agent import parse_checkpoint_state
            # For module agents: restore machine state
            restored = parse_checkpoint_state(handoff_md)
            if restored:
                agent._restored_state = restored
                logger.info(f"[RESUME] {name}: restored workflow state from checkpoint")
            # For all agents: inject handoff as context in first prompt
            if handoff_md.strip():
                original_prompt = node.spec.prompt or ""
                node.spec.prompt = (
                    f"[RESUMING FROM CHECKPOINT — read this context carefully]\n\n"
                    f"{handoff_md}\n\n"
                    f"[END OF CHECKPOINT CONTEXT]\n\n"
                    f"{original_prompt}"
                )
                logger.info(f"[RESUME] {name}: injected handoff into prompt")

        result = await agent.run()
        self._registry.results[name] = result
        await self._context.set(f"result:{name}", result)

        # Handoff-restart: agent hit context limit, restart with fresh context
        if result.halted_by == "context_handoff":
            handoff = getattr(agent.backend, '_last_handoff', '')
            # Checkpoint ALL agents (not just this one) so everything is saved
            if self._checkpoint_manager:
                await self._checkpoint_manager.create(reason=f"context_handoff:{name}")
            logger.info(f"[HANDOFF-RESTART] {name}: restarting with fresh context")
            # Only inject handoff for the agent that needs restart
            agent_checkpoints = getattr(self, '_agent_checkpoints', {})
            agent_checkpoints[name] = handoff
            self._agent_checkpoints = agent_checkpoints
            # Restart: recursive call to _run_node (fresh backend, handoff injected)
            return await self._run_node(name)

        # Clear exit signal
        self._registry.exit_signals.pop(name, None)

        # Check if succession was registered (takes priority over done-exit)
        if name in self._registry.pending_successions:
            await self._check_succession(name)
            return result

        # If agent exited via exit signal with no succession → done exit, clean up
        if result.halted_by == "exit_signal":
            await self._registry.remove(name, cancel_task=False)
            if self._checkpoint_manager:
                await self._checkpoint_manager.create(reason=f"done_exit:{name}")
            return result

        await self._check_succession(name)
        return result

    async def _check_succession(self, agent_name: str) -> None:
        """If agent designated a successor, execute the atomic swap."""
        if agent_name not in self._registry.pending_successions:
            return
        successor_spec = self._registry.pending_successions.pop(agent_name)
        await self._execute_succession(agent_name, successor_spec)

    async def _execute_succession(self, agent_name: str, successor_spec: Any) -> None:
        """Atomic swap: lock channel, replace agent, start successor, unlock."""
        # Checkpoint before swap
        if self._checkpoint_manager:
            await self._checkpoint_manager.create(reason=f"pre_succession:{agent_name}")

        # Clear stale per-instance state (new _run_node_inner will repopulate)
        await self._registry.clear_agent_runtime(agent_name)

        channel = self._channel_bus.get_or_create(f"{agent_name}:messages")
        channel.lock()
        try:
            successor_spec.name = agent_name
            self._registry.nodes[agent_name] = type(self._registry.nodes[agent_name])(spec=successor_spec)
            task = asyncio.create_task(self._run_node(agent_name), name=f"swarm:{agent_name}")
            self._registry.tasks[agent_name] = task
            logger.info(f"[SUCCESSION] {agent_name} swapped to fresh instance")
        finally:
            channel.unlock()

        # Checkpoint after swap so latest reflects the new state
        if self._checkpoint_manager:
            await self._checkpoint_manager.create(reason=f"post_succession:{agent_name}")

    def _register_user_agent(self) -> None:
        """Register 'user' as a virtual agent — visible to all, has an inbox.
        Uses UserBackend so it participates in the standard agent lifecycle."""
        if "user" in self._registry.nodes:
            return
        from ._user_backend import UserBackend

        async def _on_user_event(event_type: str, data: Any) -> None:
            """Handle block/unblock events from UserBackend."""
            if event_type == "blocked_on_user":
                self._registry.blocked_on_user = True
                self._registry.blocked_by_agent = data.get("from")
                logger.info(f"[USER] Nudge monitor PAUSED (blocked by '{data.get('from')}')")
                # Checkpoint before blocking — preserves state in case user takes long
                if self._checkpoint_manager:
                    await self._checkpoint_manager.create(reason=f"blocked_on_user:{data.get('from')}")
                # Emit to UI
                if self._event_callback:
                    event = AgentEvent(
                        agent_name="user",
                        event_type="blocked_on_user",
                        data=data,
                        timestamp_ms=int(asyncio.get_event_loop().time() * 1000),
                    )
                    await self._event_callback(event)
            elif event_type == "unblocked_by_user":
                self._registry.blocked_on_user = False
                self._registry.blocked_by_agent = None
                logger.info("[USER] Nudge monitor RESUMED (user responded)")
                if self._event_callback:
                    event = AgentEvent(
                        agent_name="user",
                        event_type="unblocked_by_user",
                        data=data,
                        timestamp_ms=int(asyncio.get_event_loop().time() * 1000),
                    )
                    await self._event_callback(event)
            elif event_type == "user_message_received":
                # Emit as a normal message event so UI shows it in user's tab
                if self._event_callback:
                    event = AgentEvent(
                        agent_name="user",
                        event_type="message",
                        data=data.get("message", ""),
                        timestamp_ms=int(asyncio.get_event_loop().time() * 1000),
                    )
                    await self._event_callback(event)

        self._user_backend = UserBackend(on_event=_on_user_event, channel_bus=self._channel_bus)

        from ._tools import ToolSet
        manager = self._manager or "TaskManager"
        user_tools = ToolSet()
        user_spec = AgentSpec(
            name="user",
            prompt=(
                f"You are the user agent. When you receive a message, wait for the human to respond. "
                f"The human's response will be delivered to you automatically. "
                f"Then forward it to {manager} using send_message."
            ),
            system_prompt=(
                f"You are the bridge between the human user and {manager}. "
                f"When {manager} sends you a message, the human sees it. "
                f"When the human types a response, you receive it and forward it to {manager}. "
                f"Always use send_message(to='{manager}', message=<response>)."
            ),
            tools=user_tools,
            visibility={"visible_to": [manager], "can_see": [manager]},
            reply_only=False,
            ignore_stall=True,
            description=f"Human user. Only {manager} communicates here.",
        )
        user_spec._is_virtual = True  # type: ignore[attr-defined]
        self._registry.add(user_spec)

    async def run(self, mode: str = ExecutionMode.AWAIT_ALL) -> dict[str, AgentResult[Any]]:
        # Register the "user" virtual agent before building visibility
        self._register_user_agent()

        logger.info(f"[SWARM] Building visibility graph for {len(self._registry.nodes)} nodes...")
        try:
            self._build_visibility_graph()
        except Exception as e:
            logger.error(f"[SWARM] Visibility graph failed: {e}")
            import traceback
            traceback.print_exc()

        # Give nudge monitor access to swarm (and thus registry) state
        self._nudge_monitor._swarm = self
        self._nudge_monitor.start()
        logger.info(f"[SWARM] Visibility graph built. Starting agents...")

        for name, node in self._registry.nodes.items():
            if not node.spec.auto_start:
                logger.info(f"[SWARM] Skipping auto-start for: {name}")
                continue
            logger.info(f"[SWARM] Creating task for: {name}")
            task = asyncio.create_task(self._run_node(name), name=f"swarm:{name}")
            self._registry.tasks[name] = task

        if mode == ExecutionMode.AWAIT_ALL:
            await asyncio.gather(*self._registry.tasks.values(), return_exceptions=True)

        elif mode == ExecutionMode.AWAIT_FIRST:
            done, pending = await asyncio.wait(
                self._registry.tasks.values(), return_when=asyncio.FIRST_COMPLETED
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

        return dict(self._registry.results)
