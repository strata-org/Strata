"""Destructive, Sandbox-wide snapshot MCP for the BigSur repair agent.

The normal snapshot server (`_snapshot_mcp.create_snapshot_server`) is scoped to
ONE entry's `Stub.lean` and can only save/list/read — never delete. BigSur, by
contrast, must clear snapshots that have gone stale after it rewrites a signature
or removes a decomposition (a banked "compiling" state for the OLD contract is
misleading once the contract changes). So this server is:

  - Sandbox-WIDE: it discovers every `stub_versions/` directory beneath the
    Sandbox root, across all workspaces/decompositions.
  - DESTRUCTIVE: it can delete individual snapshots or an entire workspace's
    snapshot history.

Only BigSur gets this server. Snapshot layout is unchanged from `_snapshot_mcp`:
`<workspace>/stub_versions/<tag>.lean` + `index.json` (tag -> metadata).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool

from ._snapshot_mcp import _load_index, _safe_tag, _save_index


def _find_snapshot_dirs(sandbox_root: Path) -> list[Path]:
    """All `stub_versions/` directories anywhere beneath the Sandbox root."""
    if not sandbox_root.exists():
        return []
    return sorted(p for p in sandbox_root.rglob("stub_versions") if p.is_dir())


def create_bigsur_snapshot_mcp_server(sandbox_root: Path):
    """Create a Sandbox-wide, WRITE/DELETE-capable snapshot MCP for BigSur.

    Args:
        sandbox_root: absolute path to the Sandbox directory to scan.
    """
    sandbox_root = Path(sandbox_root)

    def _text(payload: Any) -> dict[str, Any]:
        return {"content": [{"type": "text",
                             "text": json.dumps(payload, indent=2) if not isinstance(payload, str) else payload}]}

    def _rel(p: Path) -> str:
        try:
            return str(p.relative_to(sandbox_root))
        except ValueError:
            return str(p)

    def _resolve_dir(workspace: str) -> Path:
        """Map a workspace token (as reported by list_all_snapshots) back to its
        stub_versions dir. Accepts either the workspace-relative path or the
        stub_versions path itself, relative to the Sandbox root."""
        cand = sandbox_root / workspace
        if cand.name == "stub_versions":
            return cand
        return cand / "stub_versions"

    @tool(
        name="list_all_snapshots",
        description=(
            "List EVERY banked proof snapshot across the entire Sandbox, grouped by "
            "workspace. Each group shows the workspace path and its snapshots with "
            "remaining sorry counts and notes. Use this first to find snapshots that "
            "have gone stale after you changed a signature or removed a decomposition."),
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def list_all_snapshots(input: dict[str, Any]) -> dict[str, Any]:
        groups = []
        for snap_dir in _find_snapshot_dirs(sandbox_root):
            index = _load_index(snap_dir)
            if not index:
                continue
            rows = sorted(index.items(), key=lambda kv: kv[1].get("ts", 0))
            groups.append({
                "workspace": _rel(snap_dir.parent),
                "stub_versions": _rel(snap_dir),
                "count": len(index),
                "snapshots": [{
                    "tag": tag,
                    "sorry_count": meta.get("sorry_count", "?"),
                    "note": meta.get("note", ""),
                } for tag, meta in rows],
            })
        if not groups:
            return _text("No snapshots anywhere in the Sandbox.")
        return _text({"total_workspaces": len(groups),
                      "total_snapshots": sum(g["count"] for g in groups),
                      "groups": groups})

    @tool(
        name="read_snapshot",
        description=(
            "Read the full Lean source of one banked snapshot. Identify it by the "
            "workspace path (as shown by list_all_snapshots) and its tag. Use this to "
            "confirm a snapshot really is stale before deleting it."),
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string",
                              "description": "Workspace path from list_all_snapshots."},
                "tag": {"type": "string", "description": "The snapshot tag."},
            },
            "required": ["workspace", "tag"],
        },
    )
    async def read_snapshot(input: dict[str, Any]) -> dict[str, Any]:
        snap_dir = _resolve_dir(input["workspace"])
        tag = _safe_tag(input["tag"])
        f = snap_dir / f"{tag}.lean"
        if not f.exists():
            index = _load_index(snap_dir)
            avail = ", ".join(index.keys()) or "(none)"
            return _text(f"No snapshot '{tag}' in {_rel(snap_dir)}. Available: {avail}")
        return _text(f.read_text())

    @tool(
        name="delete_snapshot",
        description=(
            "DELETE one banked snapshot (its .lean file and its index entry). Use for a "
            "snapshot that captured a compiling state of a contract you have since "
            "changed — it would mislead a future prover into 'restoring' the wrong "
            "shape. Identify it by workspace path + tag."),
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string",
                              "description": "Workspace path from list_all_snapshots."},
                "tag": {"type": "string", "description": "The snapshot tag to delete."},
            },
            "required": ["workspace", "tag"],
        },
    )
    async def delete_snapshot(input: dict[str, Any]) -> dict[str, Any]:
        snap_dir = _resolve_dir(input["workspace"])
        index = _load_index(snap_dir)
        tag = input["tag"]
        # Accept both the raw tag and its sanitized form.
        key = tag if tag in index else _safe_tag(tag)
        if key not in index:
            avail = ", ".join(index.keys()) or "(none)"
            return _text(f"No snapshot '{tag}' in {_rel(snap_dir)}. Available: {avail}")
        f = snap_dir / f"{key}.lean"
        if f.exists():
            f.unlink()
        index.pop(key, None)
        _save_index(snap_dir, index)
        return _text(f"Deleted snapshot '{key}' from {_rel(snap_dir)}. "
                     f"{len(index)} snapshot(s) remain there.")

    @tool(
        name="delete_snapshots_for_workspace",
        description=(
            "DELETE ALL banked snapshots for one workspace (every .lean plus index.json). "
            "Use when you removed an entire decomposition — its whole snapshot history is "
            "now stale. Identify the workspace by its path from list_all_snapshots."),
        input_schema={
            "type": "object",
            "properties": {
                "workspace": {"type": "string",
                              "description": "Workspace path from list_all_snapshots."},
            },
            "required": ["workspace"],
        },
    )
    async def delete_snapshots_for_workspace(input: dict[str, Any]) -> dict[str, Any]:
        snap_dir = _resolve_dir(input["workspace"])
        if not snap_dir.exists():
            return _text(f"No stub_versions dir at {_rel(snap_dir)} — nothing to delete.")
        removed = 0
        for f in snap_dir.glob("*.lean"):
            f.unlink()
            removed += 1
        idx = snap_dir / "index.json"
        if idx.exists():
            idx.unlink()
        # Drop the now-empty dir so it doesn't reappear in listings.
        try:
            snap_dir.rmdir()
        except OSError:
            pass
        return _text(f"Deleted {removed} snapshot(s) and index for {_rel(snap_dir.parent)}.")

    return create_sdk_mcp_server(
        name="bigsur_snapshots",
        version="1.0.0",
        tools=[list_all_snapshots, read_snapshot, delete_snapshot,
               delete_snapshots_for_workspace],
    )
