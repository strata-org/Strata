"""Persistent per-agent session logging.

Appends every agent event to a JSONL file, one file per agent per run.
Survives agent GC, crashes, context handoffs — the log is append-only.

Layout:
  strataswarm/temp/sessions/<run_timestamp>/<swarm_name>/
    SearchAgent.jsonl
    TaskManager.jsonl
    Prover_2.jsonl
    proof_writer_3.jsonl
    ...
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any

from ._types import AgentEvent


class SessionLogger:
    """Append-only JSONL logger for all agent events in a swarm run."""

    def __init__(self, base_dir: Path, swarm_name: str):
        ts = time.strftime("%Y-%m-%d_%H-%M-%S")
        self._dir = base_dir / "sessions" / ts / (swarm_name or "default")
        self._dir.mkdir(parents=True, exist_ok=True)
        self._handles: dict[str, Any] = {}

    @property
    def session_dir(self) -> Path:
        return self._dir

    def log(self, event: AgentEvent) -> None:
        """Append one event to the agent's JSONL file."""
        name = event.agent_name
        if name not in self._handles:
            path = self._dir / f"{_safe_filename(name)}.jsonl"
            self._handles[name] = open(path, "a", buffering=1)  # line-buffered

        entry = {
            "ts": event.timestamp_ms,
            "type": event.event_type,
            "data": _serialize_data(event.data),
        }
        self._handles[name].write(json.dumps(entry, ensure_ascii=False) + "\n")

    def log_raw(self, agent_name: str, event_type: str, data: Any) -> None:
        """Log without an AgentEvent object (for framework-level events)."""
        if agent_name not in self._handles:
            path = self._dir / f"{_safe_filename(agent_name)}.jsonl"
            self._handles[agent_name] = open(path, "a", buffering=1)

        entry = {
            "ts": int(time.time() * 1000),
            "type": event_type,
            "data": _serialize_data(data),
        }
        self._handles[agent_name].write(json.dumps(entry, ensure_ascii=False) + "\n")

    def close(self) -> None:
        """Flush and close all file handles."""
        for handle in self._handles.values():
            try:
                handle.close()
            except Exception:
                pass
        self._handles.clear()

    def __del__(self):
        self.close()


def _safe_filename(name: str) -> str:
    """Convert agent name to a safe filename."""
    return name.replace("/", "_").replace("\\", "_").replace(" ", "_")


def _serialize_data(data: Any) -> Any:
    """Make data JSON-serializable."""
    if data is None:
        return None
    if isinstance(data, (str, int, float, bool)):
        return data
    if isinstance(data, dict):
        return {k: _serialize_data(v) for k, v in data.items()}
    if isinstance(data, (list, tuple)):
        return [_serialize_data(v) for v in data]
    return str(data)
