"""
MCP tool for SuperAgents to spawn sub-agents at runtime.

Sub-agents inherit permissions from the parent and can have additional
restrictions applied by the parent.
"""

from __future__ import annotations

import asyncio
import logging
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._channels import ChannelBus
from ._tools import ToolSet
from ._types import AgentSpec

logger = logging.getLogger("strataswarm.spawn")


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
                "system_prompt": {
                    "type": "string",
                    "description": "System prompt describing the sub-agent's role and collaborators.",
                },
                "prompt": {
                    "type": "string",
                    "description": "The task prompt for the sub-agent.",
                },
                "max_budget_usd": {
                    "type": "number",
                    "description": "Maximum budget for the sub-agent in USD. Must be <= your own budget.",
                },
                "max_turns": {
                    "type": "integer",
                    "description": "Maximum turns for the sub-agent.",
                },
                "timeout_seconds": {
                    "type": "number",
                    "description": "Timeout in seconds for the sub-agent.",
                },
            },
            "required": ["name", "system_prompt", "prompt"],
        },
    )
    async def spawn_agent(input: dict[str, Any]) -> dict[str, Any]:
        name = input["name"]
        system_prompt = input["system_prompt"]
        prompt = input["prompt"]
        max_budget = input.get("max_budget_usd")
        max_turns = input.get("max_turns")
        timeout = input.get("timeout_seconds")

        # Validate name uniqueness
        if name in swarm._nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{name}' already exists."}]}

        # Validate budget constraint
        parent_budget = parent_spec.max_budget_usd
        if max_budget is not None and parent_budget is not None:
            if max_budget > parent_budget:
                return {"content": [{"type": "text", "text": (
                    f"ERROR: Sub-agent budget (${max_budget}) exceeds your budget (${parent_budget})."
                )}]}
        elif max_budget is None and parent_budget is not None:
            max_budget = parent_budget

        # Inherit tools exactly from parent — no path re-resolution
        child_tools = ToolSet()
        for t in parent_spec.tools.allowed:
            child_tools.allowed.append(t)
        for t in parent_spec.tools.disallowed:
            child_tools.disallowed.append(t)

        child_allowed = [t.to_claude_format() for t in child_tools.allowed]

        # Create child spec
        child_spec = AgentSpec(
            name=name,
            system_prompt=system_prompt,
            prompt=prompt,
            tools=child_tools,
            max_turns=max_turns,
            max_budget_usd=max_budget,
            timeout_seconds=timeout,
            is_super_agent=False,
        )
        # Tag as spawned (for UI display, not saved)
        child_spec._spawned_by = parent_name  # type: ignore[attr-defined]

        # Register and start the sub-agent in the swarm
        logger.info(f"[SPAWN] {parent_name} spawning sub-agent '{name}' (budget=${max_budget})")

        swarm.add(child_spec)

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

        # Start the sub-agent as a new task
        async def run_child():
            return await swarm._run_node(name)

        task = asyncio.create_task(run_child(), name=f"swarm:{name}")
        swarm._tasks[name] = task

        return {"content": [{"type": "text", "text": (
            f"Sub-agent '{name}' spawned successfully. "
            f"It is now running and you can communicate with it via send_message. "
            f"Tools: {child_allowed}, Budget: ${max_budget}, Turns: {max_turns}"
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

    return create_sdk_mcp_server(
        name="agent_spawn",
        version="1.0.0",
        tools=[spawn_agent, check_sub_agents, sleep_tool],
    )
