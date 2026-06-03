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
            "Create and start a new sub-agent. Rules:\n"
            "- recursive=true (SuperAgent): Inherits YOUR system prompt. Do NOT provide system_prompt.\n"
            "- recursive=false (leaf): You MUST provide system_prompt describing the leaf's specific role.\n"
            "The sub-agent runs concurrently and can communicate with other agents via messaging."
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
                    "description": (
                        "System prompt for LEAF agents only (recursive=false). "
                        "Describes the agent's specific role and constraints. "
                        "Do NOT provide this when recursive=true — it will error."
                    ),
                },
                "prompt": {
                    "type": "string",
                    "description": (
                        "The task for the sub-agent. Include ALL context: theorem statement, "
                        "definitions, available tactics, recommended approach, relevant lemmas."
                    ),
                },
                "recursive": {
                    "type": "boolean",
                    "description": (
                        "If true: child is a SuperAgent (inherits your system prompt, can spawn its own agents). "
                        "If false: child is a leaf (uses system_prompt you provide, writes proofs directly). "
                        "Default to true for complex tasks."
                    ),
                },
            },
            "required": ["name", "folder", "prompt"],
        },
    )
    async def spawn_agent(input: dict[str, Any]) -> dict[str, Any]:
        name = input["name"]
        folder_name = input["folder"]
        system_prompt = input.get("system_prompt")
        prompt = input["prompt"]
        recursive = input.get("recursive", False)

        # Validate: recursive=true must NOT have system_prompt, recursive=false MUST have it
        if recursive and system_prompt:
            return {"content": [{"type": "text", "text": (
                "ERROR: Do not provide system_prompt when recursive=true. "
                "SuperAgent children inherit your system prompt automatically."
            )}]}
        if not recursive and not system_prompt:
            return {"content": [{"type": "text", "text": (
                "ERROR: You must provide system_prompt when recursive=false. "
                "Leaf agents need a specific role description."
            )}]}
        # Inherit budget/turns/timeout from parent
        max_budget = parent_spec.max_budget_usd
        max_turns = parent_spec.max_turns
        timeout = parent_spec.timeout_seconds

        # Ensure name uniqueness — auto-suffix if collision
        original_name = name
        if name in swarm._registry.nodes:
            suffix = len(swarm._registry.nodes)
            while f"{original_name}_{suffix}" in swarm._registry.nodes:
                suffix += 1
            name = f"{original_name}_{suffix}"

        # --- Workspace scoping: child gets a subdirectory of parent's workspace ---
        workspace = parent_spec.workspace
        if not workspace or not workspace.write:
            return {"content": [{"type": "text", "text": (
                "ERROR: Parent has no workspace write paths configured."
            )}]}

        write_root = _infer_directory(workspace.write[0])
        child_dir = f"{write_root}/{folder_name}"

        # Validate: prompt should not reference files outside child's workspace
        import re
        lean_file_refs = re.findall(r'\S+\.lean', prompt)
        outside_refs = [
            f for f in lean_file_refs
            if not f.startswith(child_dir) and not f.startswith(f"{folder_name}/")
            and "/" in f  # ignore bare filenames like "proof.lean"
        ]
        if outside_refs:
            return {"content": [{"type": "text", "text": (
                f"ERROR: Your prompt references files outside the child's workspace: "
                f"{outside_refs[:3]}. The child can ONLY access '{child_dir}/'. "
                f"Do NOT tell the child to edit files outside its folder. "
                f"The child should create its own .lean file in its workspace and write the proof there. "
                f"You (the parent) will later copy the proven code into the main file."
            )}]}

        # Create the subdirectory and write prompt as context file
        base_dir = Path.cwd()
        (base_dir / child_dir).mkdir(parents=True, exist_ok=True)
        # Auto-write the prompt as context.md so child can reference it via Read
        context_path = base_dir / child_dir / "context.md"
        context_path.write_text(f"# Task from {parent_name}\n\n{prompt}\n")

        # Child workspace: full access to its subdirectory ONLY (no parent read access)
        from ._types import Workspace
        child_workspace = Workspace(
            read=[f"{child_dir}/**"],
            write=[f"{child_dir}/**"],
            edit=[f"{child_dir}/**"],
        )

        child_tools = ToolSet()
        child_tools.allow(f"Read({child_dir}/**)")
        child_tools.allow(f"Write({child_dir}/**)")
        child_tools.allow(f"Edit({child_dir}/**)")
        # Inherit all disallowed tools from parent
        if parent_spec.tools and parent_spec.tools.disallowed:
            for d in parent_spec.tools.disallowed:
                child_tools.disallow(d.to_claude_format())

        # Build child's system prompt
        if recursive:
            # SuperAgent children inherit the BASE system prompt (not the composed one)
            # This prevents cascading workspace headers and file references from parent
            base_prompt = parent_spec._base_system_prompt or parent_spec.system_prompt
            child_system_prompt = (
                f"Your workspace: {child_dir}/\n"
                f"You are a SuperAgent spawned by '{parent_name}'. "
                f"You coordinate proof work in your subdirectory — spawn sub-agents, delegate, assemble.\n"
                f"When done, report result file path to your parent ('{parent_name}').\n\n"
                f"YOUR TASK IS IN THE USER PROMPT BELOW. Your parent has already provided "
                f"context (definitions, tactics, approach). Do NOT re-gather context that's "
                f"already in your prompt — go straight to decomposing and spawning.\n\n"
                f"ISOLATION: You CANNOT read files outside your folder ({child_dir}/). "
                f"Do NOT try to read the main proof file or your parent's workspace — it will fail.\n"
                f"Your parent may have written context files in your folder before spawning you. "
                f"Check for context.md or .lean files in your workspace first.\n\n"
            )
            child_system_prompt += base_prompt
        else:
            # Leaf children get child_prefix (rules/constraints) + provided system_prompt
            child_system_prompt = ""
            if parent_spec.child_prefix:
                child_system_prompt += parent_spec.child_prefix + "\n\n"
            child_system_prompt += (
                f"Your workspace: {child_dir}/\n"
                f"You are a leaf agent (recursive=false). You cannot spawn sub-agents.\n"
                f"Write proofs directly in your workspace. When done, report result file path "
                f"to your parent ('{parent_name}').\n\n"
            )
            child_system_prompt += system_prompt  # type: ignore[operator]

        # Preserve the base system prompt for further inheritance
        base_for_child = parent_spec._base_system_prompt or parent_spec.system_prompt

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
            _base_system_prompt=base_for_child if recursive else None,
        )
        # Tag as spawned (for UI display, not saved)
        child_spec._spawned_by = parent_name  # type: ignore[attr-defined]

        # Register and start the sub-agent in the swarm
        logger.info(f"[SPAWN] {parent_name} spawning sub-agent '{name}' (budget=${max_budget})")

        await swarm._registry.add_async(child_spec)

        # Update visibility graph so the child can participate in messaging
        swarm._on_agent_spawned(child_name=name, parent_name=parent_name)

        from ._tokens import PauseToken
        swarm._registry.pause_tokens[name] = PauseToken()

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
            1 for n in swarm._registry.nodes
            if getattr(swarm._registry.nodes[n].spec, "_spawned_by", None) == parent_name
        )
        stagger_delay = num_existing_children * 5.0  # 5s between each child startup

        async def run_child():
            if stagger_delay > 0:
                await asyncio.sleep(stagger_delay)
            return await swarm._run_node(name)

        task = asyncio.create_task(run_child(), name=f"swarm:{name}")
        swarm._registry.tasks[name] = task

        budget_str = f"${max_budget}" if max_budget is not None else "unlimited"
        turns_str = str(max_turns) if max_turns is not None else "unlimited"
        rename_note = f" (renamed from '{original_name}' to avoid collision)" if name != original_name else ""
        return {"content": [{"type": "text", "text": (
            f"Sub-agent '{name}' spawned successfully.{rename_note} "
            f"It is now running and you can communicate with it via send_message(to='{name}', ...). "
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
        for name_key, node in swarm._registry.nodes.items():
            if getattr(node.spec, "_spawned_by", None) != parent_name:
                continue
            # Get status from results if available
            if name_key in swarm._registry.results:
                r = swarm._registry.results[name_key]
                status = r.status.value if hasattr(r.status, "value") else str(r.status)
                cost = f"${r.cost_usd:.4f}" if r.cost_usd else "N/A"
                turns = r.num_turns
                halted = r.halted_by if r.halted_by != "completion" else ""
            elif name_key in swarm._registry.tasks:
                task = swarm._registry.tasks[name_key]
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

        # Discover living children
        living_children = [
            n for n, node in swarm._registry.nodes.items()
            if getattr(node.spec, "_spawned_by", None) == parent_name
            and n in swarm._registry.tasks and not swarm._registry.tasks[n].done()
        ]

        children_note = ""
        if living_children:
            children_note = (
                f"\n\nLIVING SUB-AGENTS (inherited from your predecessor):\n"
                f"These sub-agents are still running and report to you:\n"
                + "\n".join(f"- {c}" for c in living_children) + "\n"
                f"Call check_sub_agents() immediately after reading the handoff file "
                f"to see their current status.\n"
            )

        successor_prompt = (
            f"You are resuming work from a previous instance. "
            f"FIRST: Read the handoff file at '{relative_handoff}' — it contains "
            f"what's been done, what's left, what approaches worked/failed, and your next steps. "
            f"Read it before doing anything else, then continue the work described there."
            f"{children_note}"
            f"\nSTART WORKING IMMEDIATELY after reading the handoff. Do not wait for instructions."
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
            max_budget_usd=parent_spec.max_budget_usd,
            max_turns=parent_spec.max_turns,
            timeout_seconds=parent_spec.timeout_seconds,
            model=parent_spec.model,
            mcp_servers=parent_spec.mcp_servers,
            _base_system_prompt=parent_spec._base_system_prompt,
            max_inbound_length=parent_spec.max_inbound_length,
            max_inbound_response=parent_spec.max_inbound_response,
            max_outbound_length=parent_spec.max_outbound_length,
            max_outbound_response=parent_spec.max_outbound_response,
            reply_only=parent_spec.reply_only,
        )

        # Preserve _spawned_by so orphan detection still works
        if hasattr(parent_spec, "_spawned_by"):
            successor_spec._spawned_by = parent_spec._spawned_by  # type: ignore[attr-defined]

        swarm._registry.pending_successions[parent_name] = successor_spec
        # Signal the agent loop to exit (same mechanism as done())
        swarm._registry.exit_signals[parent_name] = True

        logger.info(f"[SUCCESSION] {parent_name}: successor registered (handoff={relative_handoff})")

        return {"content": [{"type": "text", "text": (
            f"Successor registered. Your session will end now. "
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
            name for name, node in swarm._registry.nodes.items()
            if getattr(node.spec, "_spawned_by", None) == parent_name
            and name in swarm._registry.tasks and not swarm._registry.tasks[name].done()
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
        if target not in swarm._registry.nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{target}' does not exist."}]}
        target_node = swarm._registry.nodes[target]
        spawned_by = getattr(target_node.spec, "_spawned_by", None)
        if spawned_by != parent_name:
            return {"content": [{"type": "text", "text": (
                f"ERROR: You do not own '{target}'. You can only interrupt agents you spawned."
            )}]}

        # Interrupt the backend (kills current response stream)
        if target in swarm._registry.tasks:
            task = swarm._registry.tasks[target]
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
        swarm._registry.tasks[target] = new_task

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
        if target not in swarm._registry.nodes:
            return {"content": [{"type": "text", "text": f"ERROR: Agent '{target}' does not exist."}]}
        target_node = swarm._registry.nodes[target]
        spawned_by = getattr(target_node.spec, "_spawned_by", None)
        if spawned_by != parent_name:
            return {"content": [{"type": "text", "text": (
                f"ERROR: You do not own '{target}'. You can only kill agents you spawned."
            )}]}

        await swarm._remove_agent(target)
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

    @tool(
        name="done",
        description=(
            "Call this when you believe your work is complete. Sends your result summary "
            "to your parent and waits for their confirmation. Returns whether you should "
            "exit (true) or continue working (false). Only call when you've finished "
            "your assigned task and have a result to report."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "summary": {
                    "type": "string",
                    "description": (
                        "Brief summary of what you accomplished. Include file paths "
                        "of any proof files you created."
                    ),
                },
            },
            "required": ["summary"],
        },
    )
    async def done_tool(input: dict[str, Any]) -> dict[str, Any]:
        summary = input["summary"]

        # Top-level agents: silently acknowledge (no parent to confirm with)
        spawned_by = getattr(parent_spec, "_spawned_by", None)
        if not spawned_by:
            return {"content": [{"type": "text", "text":
                f"Acknowledged. Summary recorded: {summary[:200]}"}]}

        # Send structured done message to parent
        done_msg = (
            f"[DONE_REQUEST] Child '{parent_name}' reports completion:\n"
            f"{summary}\n\n"
            f"Please respond with EXACTLY one of:\n"
            f"- [CONFIRMED_DONE] — if the work is satisfactory\n"
            f"- [NOT_DONE: <instructions>] — if more work is needed (include what to do next)"
        )
        sender_display = parent_name
        physical_parent = spawned_by
        parent_channel = f"{physical_parent}:messages"
        await channel_bus.send_to(parent_channel, sender=sender_display, payload=done_msg)

        # Wait for parent's binary response (block up to 5 min)
        import time as _time
        my_channel = channel_bus.get_or_create(f"{parent_name}:messages")
        deadline = _time.monotonic() + 300  # 5 min max wait

        while _time.monotonic() < deadline:
            msg = await my_channel.receive(timeout=30)
            if msg and msg.sender == spawned_by:
                payload = msg.payload.strip()
                if "[CONFIRMED_DONE]" in payload:
                    # === CONFIRMED: agent will exit ===
                    # Send final goodbye to parent
                    final_msg = (
                        f"[EXITING] '{parent_name}' exiting. Final result: {summary}\n"
                        f"My workspace files remain at their current location for you to read."
                    )
                    await channel_bus.send_to(parent_channel, sender=sender_display, payload=final_msg)

                    # Set exit signal — agent loop will break on next iteration
                    swarm._registry.exit_signals[parent_name] = True

                    return {"content": [{"type": "text", "text": (
                        f"DONE = true\n"
                        f"Parent confirmed you are done. Your session will end after this response.\n"
                        f"Do not start any new work."
                    )}]}

                elif "[NOT_DONE" in payload:
                    # === NOT DONE: extract parent's instructions ===
                    # Parse reason after [NOT_DONE: ...]
                    if ":" in payload.split("[NOT_DONE")[1]:
                        reason = payload.split("[NOT_DONE")[1].split(":", 1)[-1].strip().rstrip("]")
                    else:
                        reason = payload.split("[NOT_DONE")[1].strip("]").strip()

                    return {"content": [{"type": "text", "text": (
                        f"DONE = false\n"
                        f"Parent says more work is needed.\n"
                        f"Instructions from parent: {reason}\n"
                        f"Continue working on the above."
                    )}]}
                else:
                    # Non-confirmation message — put back and keep waiting
                    await my_channel.send(msg)
            elif msg:
                # Message from someone else — put back
                await my_channel.send(msg)

        # Timeout — parent didn't respond
        return {"content": [{"type": "text", "text": (
            "DONE = timeout\n"
            "Parent did not respond within 5 minutes. "
            "Send a status update to your parent and try calling done() again later."
        )}]}

    return create_sdk_mcp_server(
        name="agent_spawn",
        version="1.0.0",
        tools=[spawn_agent, check_sub_agents, sleep_tool, broadcast, interrupt_agent, designate_successor, kill_agent, my_workspace, done_tool],
    )
