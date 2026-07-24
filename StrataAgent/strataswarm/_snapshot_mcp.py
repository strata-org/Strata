"""MCP server for writer/guide proof snapshots.

Lets the proof writer bank a compiling proof state at a high-water mark so
partial progress is never lost when a later chunk regresses (e.g. the writer
reverts a half-built tactic chain back to bare `sorry` to keep the file
compiling). Snapshots are record-only — there is NO auto-restore. The writer
saves; both writer and guide can browse.

Snapshots live under `<workspace>/stub_versions/`:
  - <tag>.lean         a verbatim copy of Stub.lean at save time
  - index.json         tag -> {sorry_count, ts, hash} metadata

Scope is per-entry (each obligation/child has its own history), because the
server is created against a single entry's Stub.lean + workspace.
"""

from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Any

from claude_agent_sdk import create_sdk_mcp_server, tool


def _safe_tag(tag: str) -> str:
    """Sanitize a user tag into a safe filename stem."""
    stem = re.sub(r"[^A-Za-z0-9._-]+", "_", tag.strip()).strip("._-")
    return stem[:80] or "snapshot"


def _snapshot_dir(cwd: Path, workspace: str) -> Path:
    return cwd / workspace / "stub_versions"


def _load_index(snap_dir: Path) -> dict:
    idx = snap_dir / "index.json"
    if idx.exists():
        try:
            return json.loads(idx.read_text())
        except Exception:
            return {}
    return {}


def _save_index(snap_dir: Path, index: dict) -> None:
    (snap_dir / "index.json").write_text(json.dumps(index, indent=2))


def _sorry_count(tools, stub_rel: str) -> int:
    """Total literal sorry positions across all theorems in the file."""
    try:
        by_thm = tools.get_sorries_by_theorem(stub_rel)
        return sum(len(v) for v in by_thm.values())
    except Exception:
        return -1


def save_snapshot(stub_rel: str, workspace: str, cwd: Path,
                  tag: str, note: str = "") -> str:
    """Core snapshot save — shared by the writer's MCP tool and the guide-driven
    orchestrator save. Copies the entry's Stub.lean into `stub_versions/<tag>.lean`
    only if it currently compiles; dedups by content hash; auto-numbers tag
    collisions. Returns a human-readable status string.
    """
    from .modules.po_lean import get_lean_tools

    cwd = Path(cwd)
    tools = get_lean_tools()
    source = cwd / stub_rel
    if not source.exists():
        return f"Error: {stub_rel} does not exist"

    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return ("NOT SAVED: the file does not compile right now. Fix the errors "
                "first (sorry is fine, errors are not), then snapshot.")

    content = source.read_text()
    content_hash = hashlib.sha256(content.encode()).hexdigest()[:16]

    snap_dir = _snapshot_dir(cwd, workspace)
    snap_dir.mkdir(parents=True, exist_ok=True)
    index = _load_index(snap_dir)

    # Dedup by content hash
    for existing_tag, meta in index.items():
        if meta.get("hash") == content_hash:
            return (f"Already saved — this exact content is snapshot "
                    f"'{existing_tag}'. No new copy made.")

    tag = _safe_tag(tag)
    # Avoid clobbering a different snapshot that happens to share a tag
    if tag in index:
        n = 2
        while f"{tag}-{n}" in index:
            n += 1
        tag = f"{tag}-{n}"

    (snap_dir / f"{tag}.lean").write_text(content)
    sorries = _sorry_count(tools, stub_rel)
    index[tag] = {
        "sorry_count": sorries,
        "hash": content_hash,
        "ts": time.time(),
        "note": (note or "").strip(),
    }
    _save_index(snap_dir, index)

    return (f"✓ Snapshot '{tag}' saved ({sorries} sorry remaining). "
            f"{len(index)} snapshot(s) banked for this obligation.")


def snapshot_summary(cwd: Path, workspace: str) -> str:
    """One-line-per-snapshot digest for the guide handoff (no tool call needed).

    Returns "" when nothing is banked yet, so callers can append conditionally.
    """
    snap_dir = _snapshot_dir(Path(cwd), workspace)
    index = _load_index(snap_dir)
    if not index:
        return ""
    rows = sorted(index.items(), key=lambda kv: kv[1].get("ts", 0))
    parts = []
    for tag, meta in rows:
        note = f" ({meta['note']})" if meta.get("note") else ""
        parts.append(f"{tag}={meta.get('sorry_count', '?')}sorry{note}")
    return "Banked snapshots (oldest→newest): " + "; ".join(parts)


def create_snapshot_server(stub_rel: str, workspace: str, cwd: Path,
                           can_write: bool = True):
    """Create the snapshot MCP server.

    Args:
        stub_rel: repo-relative path to the entry's Stub.lean.
        workspace: repo-relative workspace dir (snapshots go under it).
        cwd: repository root (absolute).
        can_write: if True, expose snapshot_progress (writer). Guides get
                   only list/read.
    """
    from .modules.po_lean import get_lean_tools

    cwd = Path(cwd)

    @tool(
        name="snapshot_progress",
        description=(
            "Bank the CURRENT proof state as a named snapshot. Use this ONLY at a "
            "real high-water mark — the file compiles and you just closed a goal, "
            "landed a key lemma, or reached a structurally-better proof than before. "
            "It is your safety net: if a later attempt regresses, this compiling "
            "version is preserved. The file MUST compile (sorry warnings are fine, "
            "errors are not). Duplicate content is deduplicated automatically."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "tag": {
                    "type": "string",
                    "description": "Short label for this milestone, e.g. 'base-case-closed' or 'step3-done'.",
                },
                "note": {
                    "type": "string",
                    "description": "Optional one-line description of what progress this captures.",
                },
            },
            "required": ["tag"],
        },
    )
    async def snapshot_progress_tool(input: dict[str, Any]) -> dict[str, Any]:
        msg = save_snapshot(stub_rel, workspace, cwd,
                            input["tag"], input.get("note") or "")
        return {"content": [{"type": "text", "text": msg}]}

    @tool(
        name="list_snapshots",
        description=(
            "List all banked proof snapshots for the current obligation, with their "
            "remaining sorry counts and notes. Use this to see the proof's trajectory "
            "and spot regressions (a later state with MORE sorry than an earlier one)."
        ),
        input_schema={"type": "object", "properties": {}, "required": []},
    )
    async def list_snapshots_tool(input: dict[str, Any]) -> dict[str, Any]:
        snap_dir = _snapshot_dir(cwd, workspace)
        index = _load_index(snap_dir)
        if not index:
            return {"content": [{"type": "text", "text": "No snapshots saved yet."}]}
        # Order by save time
        rows = sorted(index.items(), key=lambda kv: kv[1].get("ts", 0))
        lines = ["Snapshots (oldest → newest):"]
        for tag, meta in rows:
            note = f" — {meta['note']}" if meta.get("note") else ""
            lines.append(f"  • {tag}: {meta.get('sorry_count', '?')} sorry{note}")
        return {"content": [{"type": "text", "text": "\n".join(lines)}]}

    @tool(
        name="read_snapshot",
        description=(
            "Read the full Lean source of a banked snapshot by tag. Use this to "
            "recover a proof fragment you regressed away from, or (as guide) to "
            "inspect what a milestone actually contained."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "tag": {"type": "string", "description": "The snapshot tag to read."},
            },
            "required": ["tag"],
        },
    )
    async def read_snapshot_tool(input: dict[str, Any]) -> dict[str, Any]:
        snap_dir = _snapshot_dir(cwd, workspace)
        tag = _safe_tag(input["tag"])
        f = snap_dir / f"{tag}.lean"
        if not f.exists():
            index = _load_index(snap_dir)
            avail = ", ".join(index.keys()) or "(none)"
            return {"content": [{"type": "text", "text":
                f"No snapshot '{tag}'. Available: {avail}"}]}
        return {"content": [{"type": "text", "text": f.read_text()}]}

    tools_list = [list_snapshots_tool, read_snapshot_tool]
    if can_write:
        tools_list.insert(0, snapshot_progress_tool)

    return create_sdk_mcp_server(
        name="snapshots",
        version="1.0.0",
        tools=tools_list,
    )
