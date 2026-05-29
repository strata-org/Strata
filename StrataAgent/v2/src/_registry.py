"""SwarmRegistry: single source of truth for all per-agent topology state."""

from __future__ import annotations

import asyncio
import logging
from dataclasses import dataclass, field
from typing import Any

from ._tokens import PauseToken
from ._types import AgentResult, AgentSpec, ShardConfig

logger = logging.getLogger("strataswarm.registry")


@dataclass
class AgentNode:
    spec: AgentSpec[Any]
    depends_on: list[str] = field(default_factory=list)
    render_vars: dict[str, Any] = field(default_factory=dict)


class SwarmRegistry:
    """Centralized registry of all agent state. Single source of truth."""

    def __init__(self):
        # Core topology
        self.nodes: dict[str, AgentNode] = {}
        self.tasks: dict[str, asyncio.Task] = {}
        self.results: dict[str, AgentResult[Any]] = {}
        self.pause_tokens: dict[str, PauseToken] = {}
        self.pending_successions: dict[str, AgentSpec[Any]] = {}

        # Visibility & routing
        self.visibility_graph: dict[str, set[str]] = {}
        self.sharded_agents: dict[str, ShardConfig] = {}
        self.shard_counters: dict[str, int] = {}
        self.affinities: dict[tuple[str, str], str] = {}

        # Per-agent runtime state
        self.session_ids: dict[str, str] = {}
        self.session_history: dict[str, list[str]] = {}
        self.models: dict[str, str] = {}
        self.backends: dict[str, Any] = {}
        self.start_times: dict[str, Any] = {}
        self.costs: dict[str, float] = {}

        # Nudge-specific (but centrally owned)
        self.token_usage: dict[str, float] = {}  # context % per agent
        self.stalled_agents: dict[str, float] = {}  # stall timestamps
        self.last_nudge_time: dict[str, float] = {}

    # --- Query methods ---

    def agent_exists(self, name: str) -> bool:
        return name in self.nodes

    def is_alive(self, name: str) -> bool:
        return name in self.nodes or name in self.sharded_agents

    def get_spec(self, name: str) -> AgentSpec | None:
        node = self.nodes.get(name)
        return node.spec if node else None

    def get_children(self, parent_name: str) -> list[str]:
        return [
            n for n, node in self.nodes.items()
            if getattr(node.spec, "_spawned_by", None) == parent_name
        ]

    def get_living_children(self, parent_name: str) -> list[str]:
        return [
            n for n in self.get_children(parent_name)
            if n in self.tasks and not self.tasks[n].done()
        ]

    @property
    def agent_names(self) -> set[str]:
        return set(self.nodes.keys())

    @property
    def super_agents(self) -> set[str]:
        return {n for n, nd in self.nodes.items() if nd.spec.is_super_agent}

    @property
    def reply_only_agents(self) -> set[str]:
        return {n for n, nd in self.nodes.items() if nd.spec.reply_only}

    # --- Mutation methods ---

    def add(self, spec: AgentSpec, depends_on: list[str] | None = None,
            render_vars: dict[str, Any] | None = None) -> None:
        node = AgentNode(spec=spec, depends_on=depends_on or [], render_vars=render_vars or {})
        self.nodes[spec.name] = node
        self.pause_tokens[spec.name] = PauseToken()

    async def remove(self, name: str, cancel_task: bool = True) -> None:
        """Remove an agent and ALL associated state."""
        # Cancel task
        if cancel_task and name in self.tasks:
            task = self.tasks[name]
            if not task.done():
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
            del self.tasks[name]

        # Core topology
        self.nodes.pop(name, None)
        self.visibility_graph.pop(name, None)
        for visible_set in self.visibility_graph.values():
            visible_set.discard(name)

        # Runtime state
        self.start_times.pop(name, None)
        self.backends.pop(name, None)
        self.costs.pop(name, None)
        self.session_ids.pop(name, None)
        self.models.pop(name, None)
        self.pause_tokens.pop(name, None)
        self.pending_successions.pop(name, None)

        # Nudge state
        self.token_usage.pop(name, None)
        self.stalled_agents.pop(name, None)
        self.last_nudge_time.pop(name, None)

        logger.info(f"[REGISTRY] Agent '{name}' removed")

    def clear_agent_runtime(self, name: str) -> None:
        """Clear runtime state for succession (agent stays in nodes)."""
        old_session = self.session_ids.get(name)
        self.session_history.setdefault(name, []).append(old_session or f"pre_swap_{name}")
        self.session_ids.pop(name, None)
        self.models.pop(name, None)
        self.costs.pop(name, None)
        self.backends.pop(name, None)
        self.start_times.pop(name, None)
        self.results.pop(name, None)
