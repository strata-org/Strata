"""Helper functions for quick agent operations.

These wrap SwarmAgent creation + run into single async calls.
Designed for use in orchestrator modules and custom workflows.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, TypeVar

import yaml

from ._agent import SwarmAgent
from ._types import AgentResult, AgentSpec

T = TypeVar("T")

AGENT_SPECS_DIR = Path(__file__).parent / "agent_specs" / "agents"


# ─── Agent creation from YAML ────────────────────────────────────────────────

def agent_from_yaml(path: str | Path, cwd: str | None = None, **overrides) -> SwarmAgent:
    """Create a SwarmAgent from an absolute or relative YAML file path.

    Args:
        path: Path to agent YAML spec file.
        cwd: Working directory for file operations.
        **overrides: Override any spec field (e.g., name="custom_name", stateless=True).

    Returns:
        Ready-to-run SwarmAgent instance.

    Example:
        agent = agent_from_yaml("/path/to/my_agent.yaml", cwd="/project")
        result = await agent.run(inp=..., result_type=...)
    """
    return SwarmAgent(spec=_load_spec(Path(path), overrides), cwd=cwd)


def agent_from_name(name: str, cwd: str | None = None, **overrides) -> SwarmAgent:
    """Create a SwarmAgent from an agent name in agent_specs/agents/.
    For agents that need swarm registration (messaging), use `swarm_agent()` context manager.

    Args:
        name: Agent config name (without .yaml extension).
        cwd: Working directory for file operations.
        **overrides: Override any spec field.

    Returns:
        Ready-to-run SwarmAgent instance (standalone, not registered in any swarm).
    """
    path = AGENT_SPECS_DIR / f"{name}.yaml"
    if not path.exists():
        raise FileNotFoundError(
            f"Agent spec '{name}' not found at {path}. "
            f"Available: {[f.stem for f in AGENT_SPECS_DIR.glob('*.yaml')]}"
        )
    return SwarmAgent(spec=_load_spec(path, overrides), cwd=cwd)


class swarm_agent:
    """Context manager: creates an agent registered in the swarm, removes on exit.

    Registers the agent in the swarm registry and visibility graph on entry.
    Other agents can message it while it's alive. On exit, removes it cleanly.

    Usage:
        async with swarm_agent("counter_example", swarm=agent.swarm, cwd=cwd) as cea:
            result = await cea.run(inp=..., result_type=Verdict)

        # With workspace scoping (agent can only access files in scope_dir):
        async with swarm_agent("proof_writer", swarm=agent.swarm, cwd=cwd,
                               workspace="StrataAgent/Sandbox/lemma_1") as writer:
            result = await writer.run(inp=..., result_type=...)

    The agent gets a unique name (suffixed with timestamp) to avoid collisions.
    """

    def __init__(self, name: str, swarm: Any, cwd: str | None = None, workspace: str | None = None,
                 template_vars: dict[str, str] | None = None, can_see: list[str] | None = None, **overrides):
        import time as _time
        self._swarm = swarm
        self._cwd = cwd
        self._spec_name = name
        self._workspace = workspace
        self._template_vars = template_vars or {}
        self._can_see = can_see  # if set, restrict visibility to these agents only
        self._overrides = overrides
        self._unique_name: str | None = None
        self._agent: SwarmAgent | None = None

    async def __aenter__(self) -> SwarmAgent:
        import time as _time
        path = AGENT_SPECS_DIR / f"{self._spec_name}.yaml"
        if not path.exists():
            raise FileNotFoundError(
                f"Agent spec '{self._spec_name}' not found at {path}. "
                f"Available: {[f.stem for f in AGENT_SPECS_DIR.glob('*.yaml')]}"
            )
        spec = _load_spec(path, self._overrides)

        # Render Jinja template variables in system_prompt
        if self._template_vars and spec.system_prompt:
            from jinja2 import Template
            spec.system_prompt = Template(spec.system_prompt).render(**self._template_vars)

        # Workspace scoping: override spec's workspace and tool permissions
        if self._workspace:
            from ._types import Workspace
            from ._tools import ToolSet

            scope = f"{self._workspace}/**"
            spec.workspace = Workspace(read=[scope], write=[scope], edit=[scope])

            # Tools that must be scoped (generic versions stripped, scoped versions added)
            _MUST_SCOPE = ("Read", "Write", "Edit", "Bash", "Grep", "Glob")

            # Rebuild tools: only scoped access + non-filesystem tools from spec
            tools = ToolSet()
            tools.allow(f"Read({scope})")
            tools.allow(f"Write({scope})")
            tools.allow(f"Edit({scope})")
            if spec.tools:
                for t in spec.tools.allowed:
                    if t.name in _MUST_SCOPE:
                        # Drop generic and unscoped — only keep if already scoped to our workspace
                        if t.pattern and t.pattern.startswith(self._workspace):
                            tools.allow(t.to_claude_format())
                        # Otherwise skip (replaced by our scoped versions above)
                    else:
                        tools.allow(t.to_claude_format())
                for t in spec.tools.disallowed:
                    tools.disallow(t.to_claude_format())
            spec.tools = tools

            # Create workspace directory
            from pathlib import Path as _P
            _P(self._cwd or ".").joinpath(self._workspace).mkdir(parents=True, exist_ok=True)

        # Workspace enforcement hook: deny access outside allowed paths
        workspace_hooks = None
        if self._workspace:
            from .modules.hooks import workspace_hooks as _ws_hooks
            workspace_hooks = _ws_hooks(self._workspace)

        # Unique name
        # Use a global counter to avoid collisions for agents spawned in the same second
        swarm_agent._counter = getattr(swarm_agent, '_counter', 0) + 1
        self._unique_name = f"{spec.name}_{swarm_agent._counter}"
        spec.name = self._unique_name

        # Build MCP servers (messaging + any from spec)
        from ._messaging import create_messaging_server
        from ._directory import create_directory_server

        mcp_servers = dict(spec.mcp_servers or {})
        messaging_server = create_messaging_server(
            agent_name=self._unique_name,
            channel_bus=self._swarm._channel_bus,
            known_agents=[n for n in self._swarm._registry.nodes if n != self._unique_name],
            can_message=self._swarm.can_message,
            route_message=self._swarm._route_message,
            get_sender_display=self._swarm._get_sender_display,
            on_tool_call=self._swarm._record_tool_call,
            reply_only_mode=spec.reply_only,
            known_service_agents=set(),
            start_time=None,
            is_agent_alive=lambda r: r in self._swarm._registry.nodes or r in self._swarm._registry.sharded_agents,
            outbound_limit=spec.max_outbound_length,
            outbound_limit_response=spec.max_outbound_response,
            get_inbound_limit=self._swarm._get_inbound_limit,
        )
        mcp_servers["agent_messaging"] = messaging_server
        mcp_servers["agent_directory"] = create_directory_server(
            agent_name=self._unique_name, swarm=self._swarm,
        )

        # Inject lean_tools MCP for agents that need verified file operations
        if self._workspace:
            from ._lean_tools_mcp import create_lean_tools_server
            mcp_servers["lean_tools"] = create_lean_tools_server(workspace=self._workspace)

        # Get event callback from swarm for dashboard visibility
        on_event = getattr(self._swarm, '_on_event_with_telemetry', None)

        # Create agent with full swarm integration
        self._agent = SwarmAgent(
            spec=spec,
            channel_bus=self._swarm._channel_bus,
            cwd=self._cwd,
            on_event=on_event,
            mcp_servers_override=mcp_servers,
            backend_factory=self._swarm._backend_factory,
        )
        self._agent.swarm = self._swarm

        # Combine workspace hooks + spec-level hooks + tool_error_reminder hooks
        combined_hooks = workspace_hooks
        if spec.hooks:
            from ._swarm import _resolve_hooks
            spec_hooks = _resolve_hooks(spec.hooks)
            if spec_hooks:
                if combined_hooks:
                    for event, matchers in spec_hooks.items():
                        if event in combined_hooks:
                            combined_hooks[event].extend(matchers)
                        else:
                            combined_hooks[event] = matchers
                else:
                    combined_hooks = spec_hooks

        # Add tool_error_reminder as a PostToolUseFailure hook
        if spec.tool_error_reminder:
            from .modules.hooks import tool_error_reminder_hooks
            reminder_hooks = tool_error_reminder_hooks(spec.tool_error_reminder)
            if combined_hooks:
                for event, matchers in reminder_hooks.items():
                    if event in combined_hooks:
                        combined_hooks[event].extend(matchers)
                    else:
                        combined_hooks[event] = matchers
            else:
                combined_hooks = reminder_hooks

        # Add budget warning as a PreToolUse hook (fires when turns running low)
        if spec.max_turns:
            from .modules.hooks import budget_warning_hooks
            budget_hooks = budget_warning_hooks(self._agent)
            if combined_hooks:
                for event, matchers in budget_hooks.items():
                    if event in combined_hooks:
                        combined_hooks[event].extend(matchers)
                    else:
                        combined_hooks[event] = matchers
            else:
                combined_hooks = budget_hooks

        self._agent._hooks = combined_hooks

        # Register in swarm
        self._swarm._registry.add(spec)
        self._swarm._registry.agents[self._unique_name] = self._agent

        # Add to visibility graph
        if self._can_see is not None:
            # Restricted visibility: only see specified agents
            visible_to_me = set()
            for target in self._can_see:
                # Match by logical name or exact name
                for node_name in self._swarm._registry.visibility_graph:
                    if node_name == target or node_name.startswith(f"{target}_"):
                        visible_to_me.add(node_name)
                # Also check sharded agents
                if target in self._swarm._registry.sharded_agents:
                    visible_to_me.add(target)
            self._swarm._registry.visibility_graph[self._unique_name] = visible_to_me
        else:
            # Default: can see all
            self._swarm._registry.visibility_graph[self._unique_name] = set(
                self._swarm._registry.visibility_graph.keys()
            )
        # Everyone can see this agent
        for visible_set in self._swarm._registry.visibility_graph.values():
            visible_set.add(self._unique_name)

        return self._agent

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        if self._unique_name and self._swarm:
            # Clean removal from swarm (nodes, visibility, all state)
            await self._swarm._registry.remove(self._unique_name, cancel_task=False)
            # Remove the channel to avoid message buildup from dead agents
            channel_name = f"{self._unique_name}:messages"
            self._swarm._channel_bus._channels.pop(channel_name, None)
            # Drop local references for GC
            self._agent = None
        return False


def _load_spec(path: Path, overrides: dict[str, Any]) -> AgentSpec:
    """Load an AgentSpec from a YAML file with optional overrides."""
    from ._tools import ToolSet

    with open(path) as f:
        raw = yaml.safe_load(f)

    # Apply overrides
    raw.update(overrides)

    # Build tools
    tools = None
    if raw.get("allowed_tools") or raw.get("disallowed_tools"):
        tools = ToolSet()
        for t in raw.get("allowed_tools", []):
            tools.allow(t)
        for t in raw.get("disallowed_tools", []):
            tools.disallow(t)

    return AgentSpec(
        name=raw.get("name", path.stem),
        stateless=raw.get("stateless", False),
        reply_only=raw.get("reply_only", False),
        module=raw.get("module"),
        checkpointable=raw.get("checkpointable", False),
        checkpoint_prompt=raw.get("checkpoint_prompt"),
        auto_start=raw.get("auto_start", True),
        system_prompt=raw.get("system_prompt", ""),
        prompt=raw.get("prompt", ""),
        model=raw.get("model"),
        tools=tools,
        mcp_servers=raw.get("mcp_servers", {}),
        max_turns=raw.get("max_turns"),
        max_budget_usd=raw.get("max_budget_usd"),
        timeout_seconds=raw.get("timeout_seconds"),
        max_inbound_length=raw.get("max_inbound_length"),
        max_inbound_response=raw.get("max_inbound_response"),
        max_outbound_length=raw.get("max_outbound_length"),
        max_outbound_response=raw.get("max_outbound_response"),
        description=raw.get("description", ""),
        hooks=raw.get("hooks"),
        tool_error_reminder=raw.get("tool_error_reminder"),
        resume_session_id=raw.get("resume_session_id"),
    )


async def ask(
    prompt: str = "",
    inp: Any = None,
    result_type: type[T] | None = None,
    system_prompt: str = "You are a helpful assistant. Respond according to the output schema.",
    cwd: str | None = None,
    model: str | None = None,
    mcp_servers: dict[str, Any] | None = None,
    allowed_tools: list[str] | None = None,
) -> AgentResult[T]:
    """One-shot stateless LLM call with typed output.

    The simplest way to get a typed response from an LLM. Creates a stateless
    agent, runs it, returns the result. No boilerplate.

    Args:
        prompt: System prompt override (role description).
        inp: Input data — str(inp) becomes the task prompt. Can be dict, dataclass, str.
        result_type: Expected return type. Enforced via JSON schema on the LLM.
        system_prompt: Agent's role description.
        cwd: Working directory for file operations.
        model: Model override (e.g., "haiku" for cheap decisions).
        mcp_servers: MCP server configs if tools are needed.
        allowed_tools: Tool allowlist if the agent needs tools.

    Returns:
        AgentResult[T] with result.output typed as T.

    Examples:
        # Simple typed decision
        choice = await ask(
            inp={"theorem": "n + 0 = n", "tactics": ["omega", "simp", "rfl"]},
            result_type=bool,
            system_prompt="Does any of the listed tactics prove the theorem? Return true/false.",
        )

        # Structured output
        @dataclass
        class Plan:
            steps: list[str]
            estimated_lines: int

        plan = await ask(
            inp="Prove that list append is associative",
            result_type=Plan,
            system_prompt="Suggest a proof plan.",
        )
        # plan.output.steps, plan.output.estimated_lines
    """
    from ._tools import ToolSet

    tools = None
    if allowed_tools:
        tools = ToolSet()
        for t in allowed_tools:
            tools.allow(t)

    spec = AgentSpec(
        name=f"_ask_{id(inp) % 10000}",
        stateless=True,
        system_prompt=system_prompt,
        prompt=prompt or "",
        model=model,
        tools=tools,
        mcp_servers=mcp_servers or {},
    )

    agent = SwarmAgent(spec=spec, cwd=cwd)
    return await agent.run(inp=inp, result_type=result_type)


async def compile_check(
    file_path: str,
    cwd: str | None = None,
) -> AgentResult[bool]:
    """Quick stateless compile check. Returns True if file compiles without errors."""
    return await ask(
        inp={"file": file_path, "action": "compile and report pass/fail"},
        result_type=bool,
        system_prompt="Run lean_verify on the file. Return true if it compiles without errors, false otherwise.",
        cwd=cwd,
        mcp_servers={"lean_lsp": {"command": "uvx", "args": ["lean-lsp-mcp"], "type": "stdio"}},
        allowed_tools=["mcp__lean_lsp__lean_verify", "Read"],
    )


async def has_sorry(
    file_path: str,
    cwd: str | None = None,
) -> AgentResult[bool]:
    """Quick stateless sorry check. Returns True if file has any sorry."""
    return await ask(
        inp={"file": file_path, "action": "check for sorry usage"},
        result_type=bool,
        system_prompt="Check if the file contains any 'sorry'. Return true if sorry found, false if clean.",
        cwd=cwd,
        allowed_tools=["Read"],
    )
