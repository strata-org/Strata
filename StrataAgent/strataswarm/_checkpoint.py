"""Checkpoint manager for swarm state persistence.

Saves: session IDs, visibility graph, session history, and the entire workspace
folder. No hardcoded task-specific paths — workspace is derived from agent specs.
"""

from __future__ import annotations

import logging
import shutil
import time
from pathlib import Path
from typing import Any

import yaml

logger = logging.getLogger("strataswarm.checkpoint")


class CheckpointManager:
    """Creates and restores swarm checkpoints (state + workspace snapshot)."""

    def __init__(self, swarm: Any, checkpoint_dir: Path, workspace_dir: str | None = None):
        self._swarm = swarm
        self._dir = checkpoint_dir
        self._dir.mkdir(parents=True, exist_ok=True)
        self._last_checkpoint = time.time()
        self._workspace_dir = workspace_dir

    def _resolve_workspace_dir(self) -> Path | None:
        """Derive workspace root from agent specs, or use explicit override."""
        if self._workspace_dir:
            cwd = Path(self._swarm._cwd) if self._swarm._cwd else Path.cwd()
            return cwd / self._workspace_dir

        # Infer from agent workspaces — find the common root of all write paths
        all_write_paths: set[str] = set()
        for node in self._swarm._registry.nodes.values():
            ws = getattr(node.spec, "workspace", None)
            if ws and ws.write:
                for p in ws.write:
                    # Strip glob patterns to get directory
                    clean = p.rstrip("*").rstrip("/")
                    all_write_paths.add(clean)

        if not all_write_paths:
            return None

        cwd = Path(self._swarm._cwd) if self._swarm._cwd else Path.cwd()
        # Use the shortest common path as workspace root
        sorted_paths = sorted(all_write_paths, key=len)
        return cwd / sorted_paths[0]

    def _get_session_ids(self) -> dict[str, str | None]:
        """Get current session IDs for all agents from their results."""
        sessions: dict[str, str | None] = {}
        for name, node in self._swarm._registry.nodes.items():
            if getattr(node.spec, '_is_virtual', False):
                continue
            sessions[name] = self._swarm.get_agent_session_id(name)
        return sessions

    async def create(self, reason: str = "periodic") -> Path:
        """Create a checkpoint. Saves handoff notes from checkpointable agents."""
        ts = int(time.time())
        name = f"{self._swarm._name}_{ts}"
        cp_dir = self._dir / name
        cp_dir.mkdir(parents=True)

        # Collect spawned agent info for restoration
        spawned_agents: list[dict[str, Any]] = []
        for node_name, node in self._swarm._registry.nodes.items():
            spawned_by = getattr(node.spec, "_spawned_by", None)
            if spawned_by:
                spawned_agents.append({
                    "name": node_name,
                    "spawned_by": spawned_by,
                    "is_super_agent": node.spec.is_super_agent,
                    "system_prompt": node.spec.system_prompt,
                    "prompt": node.spec.prompt,
                    "workspace": {
                        "read": node.spec.workspace.read if node.spec.workspace else [],
                        "write": node.spec.workspace.write if node.spec.workspace else [],
                        "edit": node.spec.workspace.edit if node.spec.workspace else [],
                    } if node.spec.workspace else None,
                })

        # Save state
        state: dict[str, Any] = {
            "swarm_name": self._swarm._name,
            "timestamp": ts,
            "reason": reason,
            "sessions": self._get_session_ids(),
            "session_history": self._swarm._registry.session_history,
            "visibility_graph": {
                k: list(v) for k, v in self._swarm._registry.visibility_graph.items()
            },
            "sharded_agents": {
                k: {"replicas": v.replicas, "routing": v.routing, "routing_key": v.routing_key}
                for k, v in self._swarm._registry.sharded_agents.items()
            },
            "agent_affinities": {
                f"{sender}:{logical}": physical
                for (sender, logical), physical in self._swarm._registry.affinities.items()
            },
            "spawned_agents": spawned_agents,
        }
        (cp_dir / "state.yaml").write_text(
            yaml.dump(state, default_flow_style=False)
        )

        # Collect handoff notes from all checkpointable agents in visibility graph
        agents_dir = cp_dir / "agents"
        agents_dir.mkdir(exist_ok=True)
        for node_name in self._swarm._registry.visibility_graph:
            node = self._swarm._registry.nodes.get(node_name)
            if not node:
                continue
            if getattr(node.spec, '_is_virtual', False):
                continue
            if not getattr(node.spec, 'checkpointable', False):
                continue
            if getattr(node.spec, 'stateless', False):
                continue
            agent_instance = self._swarm._registry.agents.get(node_name)
            if not agent_instance:
                continue
            try:
                handoff = await agent_instance.run_checkpoint()
                if handoff:
                    (agents_dir / f"{node_name}.md").write_text(handoff)
            except Exception as e:
                logger.warning(f"Checkpoint handoff failed for {node_name}: {e}")

        # Snapshot the workspace folder (entire directory)
        workspace_root = self._resolve_workspace_dir()
        if workspace_root and workspace_root.exists():
            files_dir = cp_dir / "workspace"
            shutil.copytree(workspace_root, files_dir, dirs_exist_ok=True)
            logger.info(f"Workspace snapshot: {workspace_root} → {files_dir}")

        self._last_checkpoint = time.time()
        logger.info(f"Checkpoint created: {cp_dir} (reason: {reason})")
        return cp_dir

    def list_checkpoints(self) -> list[str]:
        """List available checkpoint names."""
        return sorted([d.name for d in self._dir.iterdir() if d.is_dir()])

    def should_checkpoint_periodic(self, interval_seconds: float = 300) -> bool:
        """Check if enough time has passed for a periodic checkpoint."""
        return time.time() - self._last_checkpoint >= interval_seconds

    def restore(self, checkpoint_name: str) -> dict[str, Any]:
        """Restore workspace from checkpoint and return the state dict."""
        cp_dir = self._dir / checkpoint_name
        if not cp_dir.exists():
            raise FileNotFoundError(f"Checkpoint not found: {checkpoint_name}")

        state = yaml.safe_load((cp_dir / "state.yaml").read_text())

        # Restore workspace folder
        workspace_snapshot = cp_dir / "workspace"
        if workspace_snapshot.exists():
            workspace_root = self._resolve_workspace_dir()
            if workspace_root:
                if workspace_root.exists():
                    shutil.rmtree(workspace_root)
                shutil.copytree(workspace_snapshot, workspace_root)
                logger.info(f"Workspace restored: {workspace_snapshot} → {workspace_root}")

        logger.info(f"Checkpoint restored: {checkpoint_name}")
        return state
