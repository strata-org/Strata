"""
MCP tool for SuperAgents to spawn sub-agents at runtime.

Sub-agents inherit permissions from the parent and can have additional
restrictions applied by the parent.
"""

from __future__ import annotations

import asyncio
import logging
from pathlib import Path
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._channels import ChannelBus, ChannelMessage
from ._tools import ToolSet
from ._types import AgentSpec

logger = logging.getLogger("strataswarm.spawn")


def _infer_directory(write_pattern: str) -> str:
    """Infer the root directory from a workspace write path pattern.

    Strips glob patterns (e.g. '**/*.lean') to get the base directory.
    Examples:
        'src/**/*.lean' -> 'src'
        'Strata/**' -> 'Strata'
        '/abs/path/*.lean' -> '/abs/path'
        'single_dir' -> 'single_dir'
    """
    p = Path(write_pattern)
    # Walk up the path until we find a component without glob characters
    parts = list(p.parts)
    clean_parts: list[str] = []
    for part in parts:
        if "*" in part or "?" in part or "[" in part:
            break
        clean_parts.append(part)
    if not clean_parts:
        return "."
    return str(Path(*clean_parts))


def create_spawn_server(
    parent_name: str,
    parent_spec: AgentSpec,
    channel_bus: ChannelBus,
    swarm: Any,
):
    """
    Create an MCP server exposing the spawn_agent tool.
    Only available to SuperAgents.
    """

    @tool(
        name="spawn_agent",
        description=(
            "Create and start a new sub-agent. The sub-agent inherits your tool permissions "
            "exactly. It runs concurrently and can communicate with you and other agents "
            "via messaging. The sub-agent's budget must be <= your budget."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "name": {
                    "type": "string",
                    "description": "Unique name for the sub-agent.",
                },
                "folder": {
                    "type": "string",
                    "description": (
                        "Folder name for the child's workspace. Relative to YOUR "
                        "workspace directory. The child gets full read/write/edit "
                        "access to this subfolder."
                    ),
                },
                "system_prompt": {
                    "type": "string",
                    "description": "System prompt describing the sub-agent's role.",
                },
                "prompt": {
                    "type": "string",
                    "description": "The task prompt for the sub-agent.",
                },
                "recursive": {
                    "type": "boolean",
                    "description": (
                        "If true, child is a SuperAgent that can spawn its own "
                        "sub-agents within its folder. Default: false."
                    ),
                },
            },
            "required": ["name", "folder", "system_prompt", "prompt"],
        },
    )
    async def spawn_agent(input: dict[str, Any]) -> dict[str, Any]:
        name = input["name"]
        folder_name = input["folder"]
        system_prompt = input["system_prompt"]
        prompt = input["prompt"]
        recursive = input.get("recursive", False)
        # Inherit budget/turns/timeout from parent
        max_budget = parent_spec.max_budget_usd
        max_turns = parent_spec.max_turns
        timeout = parent_spec.timeout_seconds

        # Validate name uniqueness
        if name in swarm._nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{name}' already exists."}]}

        # --- Workspace scoping: child gets a subdirectory of parent's workspace ---
        workspace = parent_spec.workspace
        if not workspace or not workspace.write:
            return {"content": [{"type": "text", "text": (
                "ERROR: Parent has no workspace write paths configured."
            )}]}

        write_root = _infer_directory(workspace.write[0])
        child_dir = f"{write_root}/{folder_name}"

        # Create the subdirectory
        base_dir = Path.cwd()
        (base_dir / child_dir).mkdir(parents=True, exist_ok=True)

        # Child workspace: full access to its subdirectory + read parent's workspace
        from ._types import Workspace
        child_workspace = Workspace(
            read=[f"{child_dir}/**", f"{write_root}/**"],
            write=[f"{child_dir}/**"],
            edit=[f"{child_dir}/**"],
        )

        child_tools = ToolSet()
        child_tools.allow(f"Read({child_dir}/**)")
        child_tools.allow(f"Read({write_root}/**)")
        child_tools.allow(f"Write({child_dir}/**)")
        child_tools.allow(f"Edit({child_dir}/**)")
        # Inherit all disallowed tools from parent
        if parent_spec.tools and parent_spec.tools.disallowed:
            for d in parent_spec.tools.disallowed:
                child_tools.disallow(d.to_claude_format())

        # Build child's system prompt
        child_system_prompt = ""
        if parent_spec.child_prefix:
            child_system_prompt += parent_spec.child_prefix + "\n\n"
        child_system_prompt += f"Your workspace: {child_dir}/\n"
        child_system_prompt += f"Create and edit files freely in this folder.\n"
        if recursive:
            child_system_prompt += f"You are a SuperAgent (recursive=true). You can spawn sub-agents and call designate_successor.\n"
        else:
            child_system_prompt += f"You are a leaf agent (recursive=false). You cannot spawn sub-agents or call designate_successor.\n"
        child_system_prompt += f"When done, report result file path to your parent.\n\n"
        child_system_prompt += system_prompt

        child_spec = AgentSpec(
            name=name,
            system_prompt=child_system_prompt,
            prompt=prompt,
            tools=child_tools,
            max_turns=max_turns,
            max_budget_usd=max_budget,
            timeout_seconds=timeout,
            is_super_agent=recursive,
            workspace=child_workspace if recursive else None,
            child_prefix=parent_spec.child_prefix if recursive else None,
        )
        # Tag as spawned (for UI display, not saved)
        child_spec._spawned_by = parent_name  # type: ignore[attr-defined]

        # Register and start the sub-agent in the swarm
        logger.info(f"[SPAWN] {parent_name} spawning sub-agent '{name}' (budget=${max_budget})")

        swarm.add(child_spec)

        # Update visibility graph so the child can participate in messaging
        swarm._on_agent_spawned(child_name=name, parent_name=parent_name)

        from ._tokens import PauseToken
        swarm._pause_tokens[name] = PauseToken()

        # Emit event so the UI shows the new agent immediately
        if swarm._event_callback:
            from ._types import AgentEvent
            import time as _time
            event = AgentEvent(
                agent_name=name,
                event_type="status_change",
                data="pending",
                timestamp_ms=int(_time.time() * 1000),
            )
            asyncio.ensure_future(swarm._event_callback(event))

        # Start the sub-agent as a new task (with stagger delay to avoid resource contention)
        num_existing_children = sum(
            1 for n in swarm._nodes
            if getattr(swarm._nodes[n].spec, "_spawned_by", None) == parent_name
        )
        stagger_delay = num_existing_children * 5.0  # 5s between each child startup

        async def run_child():
            if stagger_delay > 0:
                await asyncio.sleep(stagger_delay)
            return await swarm._run_node(name)

        task = asyncio.create_task(run_child(), name=f"swarm:{name}")
        swarm._tasks[name] = task

        budget_str = f"${max_budget}" if max_budget is not None else "unlimited"
        turns_str = str(max_turns) if max_turns is not None else "unlimited"
        return {"content": [{"type": "text", "text": (
            f"Sub-agent '{name}' spawned successfully. "
            f"It is now running and you can communicate with it via send_message. "
            f"Workspace: {child_dir}/, Budget: {budget_str}, Turns: {turns_str}"
        )}]}

    @tool(
        name="check_sub_agents",
        description=(
            "Check the status of all sub-agents you have spawned. "
            "Returns each sub-agent's name, status (running/completed/failed/etc), "
            "and cost so far."
        ),
        input_schema={
            "type": "object",
            "properties": {},
            "required": [],
        },
    )
    async def check_sub_agents(input: dict[str, Any]) -> dict[str, Any]:
        lines = []
        for name_key, node in swarm._nodes.items():
            if getattr(node.spec, "_spawned_by", None) != parent_name:
                continue
            # Get status from results if available
            if name_key in swarm._results:
                r = swarm._results[name_key]
                status = r.status.value if hasattr(r.status, "value") else str(r.status)
                cost = f"${r.cost_usd:.4f}" if r.cost_usd else "N/A"
                turns = r.num_turns
                halted = r.halted_by if r.halted_by != "completion" else ""
            elif name_key in swarm._tasks:
                task = swarm._tasks[name_key]
                if task.done():
                    status = "done"
                else:
                    status = "running"
                cost = "N/A"
                turns = 0
                halted = ""
            else:
                status = "pending"
                cost = "N/A"
                turns = 0
                halted = ""
            line = f"- {name_key}: {status}"
            if cost != "N/A":
                line += f" | cost={cost}"
            if turns:
                line += f" | turns={turns}"
            if halted:
                line += f" | halted_by={halted}"
            lines.append(line)

        if not lines:
            return {"content": [{"type": "text", "text": "No sub-agents spawned yet."}]}

        from datetime import datetime
        ts = datetime.now().strftime("%H:%M:%S")
        return {"content": [{"type": "text", "text": f"[{ts}] Sub-agent status:\n" + "\n".join(lines)}]}

    @tool(
        name="sleep",
        description=(
            "Sleep until a message arrives OR the timeout expires — whichever comes first. "
            "Use this to control your polling interval. If sub-agents need more time, "
            "set a longer timeout (e.g. 60-120s). You will wake up IMMEDIATELY if a "
            "message arrives before the timeout."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "seconds": {
                    "type": "number",
                    "description": "Maximum time to sleep in seconds. Wakes early if a message arrives. Range: 5-300.",
                },
            },
            "required": ["seconds"],
        },
    )
    async def sleep_tool(input: dict[str, Any]) -> dict[str, Any]:
        seconds = min(max(input.get("seconds", 30), 5), 300)
        logger.debug(f"[SLEEP] {parent_name}: sleeping up to {seconds}s")
        messages_ch = channel_bus.get_or_create(f"{parent_name}:messages")

        # Wait for a message OR timeout — whichever first
        import time as _time
        start = _time.monotonic()
        msg = await messages_ch.receive(timeout=seconds)
        elapsed = _time.monotonic() - start

        from datetime import datetime
        ts = datetime.now().strftime("%H:%M:%S")

        if msg:
            # Woke early because a message arrived — put it back for check_messages
            await messages_ch.send(msg)
            return {"content": [{"type": "text", "text": (
                f"[{ts}] Woke up after {elapsed:.0f}s (message arrived). "
                f"You have {messages_ch.pending_count} pending message(s). "
                f"Use check_messages to read them."
            )}]}

        # Timeout expired, check if anything arrived in the meantime
        pending = messages_ch.pending_count
        if pending > 0:
            return {"content": [{"type": "text", "text": (
                f"[{ts}] Woke up after {seconds}s. "
                f"You have {pending} pending message{'s' if pending > 1 else ''}. "
                f"Use check_messages to read them."
            )}]}
        return {"content": [{"type": "text", "text": (
            f"[{ts}] Woke up after {seconds}s. No new messages."
        )}]}

    @tool(
        name="designate_successor",
        description=(
            "Hand off to a fresh agent instance. Write a handoff file in your workspace "
            "first (e.g., 'handoff.md'), then call this with just the filename. "
            "Your session ends and a successor starts with fresh context, automatically "
            "instructed to read your handoff file before doing anything else."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "handoff_file": {
                    "type": "string",
                    "description": (
                        "Filename of handoff notes in your workspace (e.g., 'handoff.md'). "
                        "Must already exist. Write it with the Write tool before calling this."
                    ),
                },
            },
            "required": ["handoff_file"],
        },
    )
    async def designate_successor(input: dict[str, Any]) -> dict[str, Any]:
        handoff_filename = input["handoff_file"]

        # Resolve handoff file path within workspace
        workspace = parent_spec.workspace
        if workspace and workspace.write:
            write_root = _infer_directory(workspace.write[0])
            handoff_path = Path.cwd() / write_root / handoff_filename
        else:
            handoff_path = Path.cwd() / handoff_filename

        if not handoff_path.exists():
            return {"content": [{"type": "text", "text": (
                f"ERROR: Handoff file '{handoff_path}' does not exist. "
                f"Write it first (in your workspace) before calling designate_successor."
            )}]}

        # Successor inherits everything; prompt tells it to read handoff first
        relative_handoff = str(handoff_path.relative_to(Path.cwd()))
        successor_prompt = (
            f"You are resuming work from a previous instance. "
            f"FIRST: Read the handoff file at '{relative_handoff}' — it contains "
            f"what's been done, what's left, what approaches worked/failed, and your next steps. "
            f"Read it before doing anything else, then continue the work described there."
        )

        successor_spec = AgentSpec(
            name=f"__{parent_name}_successor",
            system_prompt=parent_spec.system_prompt,
            prompt=successor_prompt,
            tools=parent_spec.tools,
            workspace=parent_spec.workspace,
            is_super_agent=parent_spec.is_super_agent,
            child_prefix=parent_spec.child_prefix,
            description=parent_spec.description,
            visibility=parent_spec.visibility,
        )

        swarm._pending_successions[parent_name] = successor_spec

        logger.info(f"[SUCCESSION] {parent_name}: successor registered (handoff={relative_handoff})")

        return {"content": [{"type": "text", "text": (
            f"Successor registered. Your session will end after this turn. "
            f"The successor will start fresh and read '{relative_handoff}' automatically."
        )}]}

    @tool(
        name="broadcast",
        description="Send a message to ALL your living sub-agents at once.",
        input_schema={
            "type": "object",
            "properties": {
                "message": {
                    "type": "string",
                    "description": "Message to broadcast to all children.",
                },
            },
            "required": ["message"],
        },
    )
    async def broadcast(input: dict[str, Any]) -> dict[str, Any]:
        message = input["message"]

        # Find all living children of this parent
        children = [
            name for name, node in swarm._nodes.items()
            if getattr(node.spec, "_spawned_by", None) == parent_name
            and name in swarm._tasks and not swarm._tasks[name].done()
        ]

        if not children:
            return {"content": [{"type": "text", "text": "No living sub-agents to broadcast to."}]}

        for child in children:
            await channel_bus.send_to(
                f"{child}:messages",
                sender=parent_name,
                payload=f"[BROADCAST]: {message}",
            )

        return {"content": [{"type": "text", "text": f"Broadcast sent to {len(children)} agents: {children}"}]}

    @tool(
        name="interrupt_agent",
        description=(
            "Interrupt a sub-agent and redirect it with a new message. "
            "Stops the agent's current work and sends it your message immediately. "
            "Use this when a sub-agent is taking too long or going in the wrong direction."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "name": {
                    "type": "string",
                    "description": "Name of the sub-agent to interrupt.",
                },
                "message": {
                    "type": "string",
                    "description": "New instructions for the agent after interruption.",
                },
            },
            "required": ["name", "message"],
        },
    )
    async def interrupt_agent(input: dict[str, Any]) -> dict[str, Any]:
        target = input["name"]
        message = input["message"]

        # Verify ownership
        if target not in swarm._nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{target}' does not exist."}]}
        target_node = swarm._nodes[target]
        spawned_by = getattr(target_node.spec, "_spawned_by", None)
        if spawned_by != parent_name:
            return {"content": [{"type": "text", "text": (
                f"ERROR: You do not own '{target}'. You can only interrupt agents you spawned."
            )}]}

        # Interrupt the backend (kills current response stream)
        if target in swarm._tasks:
            task = swarm._tasks[target]
            if not task.done():
                # Cancel the current task — the agent will be restarted
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass

        # Send the redirect message to the agent's channel
        await channel_bus.send_to(
            f"{target}:messages",
            sender=parent_name,
            payload=f"[INTERRUPT — CHANGE DIRECTION]: {message}",
        )

        # Restart the agent task (it will wake up, see the message, and follow new instructions)
        async def run_child():
            return await swarm._run_node(target)

        new_task = asyncio.create_task(run_child(), name=f"swarm:{target}")
        swarm._tasks[target] = new_task

        logger.info(f"[INTERRUPT] {parent_name} interrupted '{target}' with new direction")
        return {"content": [{"type": "text", "text": (
            f"Agent '{target}' interrupted and redirected. It will restart and see your message."
        )}]}

    @tool(
        name="kill_agent",
        description=(
            "Kill a sub-agent you spawned. The agent will be cancelled and removed. "
            "You can only kill agents you own (that you spawned)."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "name": {
                    "type": "string",
                    "description": "Name of the sub-agent to kill.",
                },
            },
            "required": ["name"],
        },
    )
    async def kill_agent(input: dict[str, Any]) -> dict[str, Any]:
        target = input["name"]

        # Verify ownership
        if target not in swarm._nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{target}' does not exist."}]}
        target_node = swarm._nodes[target]
        spawned_by = getattr(target_node.spec, "_spawned_by", None)
        if spawned_by != parent_name:
            return {"content": [{"type": "text", "text": (
                f"ERROR: You do not own '{target}'. You can only kill agents you spawned."
            )}]}

        # Cancel the task
        if target in swarm._tasks:
            task = swarm._tasks[target]
            if not task.done():
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
            del swarm._tasks[target]

        # Remove from nodes
        del swarm._nodes[target]

        # Remove from visibility graph
        swarm._visibility_graph.pop(target, None)
        for visible_set in swarm._visibility_graph.values():
            visible_set.discard(target)

        # Remove from nudge monitor tracking
        swarm._nudge_monitor._agents.discard(target)
        swarm._nudge_monitor._super_agents.discard(target)
        swarm._nudge_monitor._reply_only_agents.discard(target)
        swarm._nudge_monitor._agent_token_usage.pop(target, None)

        # Remove from swarm state tracking
        swarm._agent_start_times.pop(target, None)
        swarm._agent_backends.pop(target, None)
        swarm._live_costs.pop(target, None)

        logger.info(f"[KILL] {parent_name} killed sub-agent '{target}'")
        return {"content": [{"type": "text", "text": f"Agent '{target}' killed and removed."}]}

    @tool(
        name="my_workspace",
        description="View your workspace directory path and permissions.",
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def my_workspace(input: dict[str, Any]) -> dict[str, Any]:
        ws = parent_spec.workspace
        if not ws:
            return {"content": [{"type": "text", "text": "No workspace configured."}]}
        info = (
            f"Workspace:\n"
            f"  Read:  {ws.read}\n"
            f"  Write: {ws.write}\n"
            f"  Edit:  {ws.edit}\n"
        )
        return {"content": [{"type": "text", "text": info}]}

    return create_sdk_mcp_server(
        name="agent_spawn",
        version="1.0.0",
        tools=[spawn_agent, check_sub_agents, sleep_tool, broadcast, interrupt_agent, designate_successor, kill_agent, my_workspace],
    )
