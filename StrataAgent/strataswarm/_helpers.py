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

    Args:
        name: Agent config name (without .yaml extension).
              e.g., "deep_proof_validator", "proof_compiler", "search_agent"
        cwd: Working directory for file operations.
        **overrides: Override any spec field.

    Returns:
        Ready-to-run SwarmAgent instance.

    Example:
        agent = agent_from_name("deep_proof_validator", cwd="/project")
        result = await agent.run(inp={"stub_file": ..., "complete_file": ...}, result_type=bool)
    """
    path = AGENT_SPECS_DIR / f"{name}.yaml"
    if not path.exists():
        raise FileNotFoundError(
            f"Agent spec '{name}' not found at {path}. "
            f"Available: {[f.stem for f in AGENT_SPECS_DIR.glob('*.yaml')]}"
        )
    return SwarmAgent(spec=_load_spec(path, overrides), cwd=cwd)


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
