"""PO Utilities: file operations, checkpointing, import rewriting.

Pure functions — no agents, no async, no swarm dependency.
"""

from __future__ import annotations

import json
import re
import shutil
from dataclasses import asdict
from pathlib import Path
from typing import Any


# ─── Import rewriting ────────────────────────────────────────────────────────

def rewrite_imports_for_child(child_stub: Path, parent_workspace: str, child_workspace: str,
                              root_workspace: str = ""):
    """Rewrite imports so child workspace compiles correctly.

    - Keep the ROOT's Stub.Def import (all files at any depth use the same Def)
    - Remove sibling decomposed imports (not available in child context)
    """
    if not child_stub.exists():
        return

    parent_module = parent_workspace.replace("/", ".")
    decomposed_prefix = f"{parent_module}.decomposed."

    # Find the root Stub.Def module (walk up to find the top-level workspace)
    root_ws = root_workspace or parent_workspace.split("/decomposed/")[0]
    root_module = root_ws.replace("/", ".")

    content = child_stub.read_text()
    new_lines = []
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            module = stripped.removeprefix("import ").strip()
            # Remove sibling decomposed imports
            if module.startswith(decomposed_prefix):
                continue
            # Rewrite any child/parent Stub.Def to ROOT's Stub.Def
            if ".Stub.Def" in module and module != f"{root_module}.Stub.Def":
                new_lines.append(f"import {root_module}.Stub.Def")
                continue
        new_lines.append(line)

    child_stub.write_text("\n".join(new_lines) + "\n")


# ─── Theorem extraction ─────────────────────────────────────────────────────

def find_sorry_theorems(lean_file: Path) -> list[tuple[str, str]]:
    """Find theorem blocks that contain sorry.
    Returns [(theorem_name, full_block_text), ...]"""
    if not lean_file.exists():
        return []
    content = lean_file.read_text()
    lines = content.splitlines()
    theorems = []
    current_name = ""
    current_start = -1

    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("theorem ") or stripped.startswith("private theorem "):
            if current_start >= 0 and current_name:
                block = "\n".join(lines[current_start:i])
                if "sorry" in block:
                    theorems.append((current_name, block))
            parts = stripped.split()
            idx = parts.index("theorem") + 1
            current_name = parts[idx].rstrip(":").rstrip("(") if idx < len(parts) else ""
            current_start = i

    if current_start >= 0 and current_name:
        block = "\n".join(lines[current_start:])
        if "sorry" in block:
            theorems.append((current_name, block))

    return theorems


def extract_imports(content: str) -> str:
    """Extract the import/open/variable header from a Lean file."""
    lines = []
    for line in content.splitlines():
        stripped = line.strip()
        if (stripped.startswith("import ") or stripped.startswith("open ") or
                stripped.startswith("variable ") or stripped.startswith("set_option") or
                stripped.startswith("/-!") or stripped.startswith("--") or not stripped):
            lines.append(line)
        else:
            break
    return "\n".join(lines)


# ─── Checkpointing ──────────────────────────────────────────────────────────

def write_checkpoint(cwd: Path, state: Any):
    """Persist ProverState as JSON for crash recovery."""
    workspace_abs = cwd / state.workspace
    workspace_abs.mkdir(parents=True, exist_ok=True)
    (workspace_abs / "po_checkpoint.json").write_text(json.dumps(asdict(state), indent=2))


def write_progress(cwd: Path, state: Any):
    """Write progress.md for monitoring."""
    workspace_abs = cwd / state.workspace
    workspace_abs.mkdir(parents=True, exist_ok=True)
    progress = workspace_abs / "progress.md"

    decomposed = getattr(state, 'decomposed_files', [])
    proved = getattr(state, 'proved_files', [])

    content = (
        f"# Proof Progress\n\n"
        f"- **Stage**: {state.stage.value}\n"
        f"- **Theorem**: {state.theorem_name}\n"
        f"- **Attempt**: {state.attempt + 1}/3\n"
        f"- **Depth**: {state.depth}/2\n"
        f"- **Decomposed**: {len(decomposed)}\n"
        f"- **Proved**: {len(proved)}\n"
        f"- **Details**: {state.last_failure_details or 'none'}\n\n"
        f"## Files\n"
    )
    for f in proved:
        content += f"- ✅ `{Path(f).name}`\n"
    for f in decomposed:
        if f not in proved:
            content += f"- ⏳ `{Path(f).name}`\n"

    progress.write_text(content)


def collect_progress(workspace: str, cwd: Path | None = None) -> str:
    """Recursively collect all progress.md files under a workspace.

    Returns a single string summarizing all PO activity — suitable for
    the TM monitor to check whether the system is still making progress.
    Also reports the most recently modified .lean file to detect silent work.
    """
    import time
    cwd = cwd or Path.cwd()
    root = cwd / workspace
    if not root.exists():
        return f"Workspace {workspace} not found."

    lines = [f"# Progress Report ({workspace})\n"]

    # Collect all progress.md files
    progress_files = sorted(root.rglob("progress.md"))
    if not progress_files:
        lines.append("No progress.md files found.\n")
    else:
        for pf in progress_files:
            rel = pf.relative_to(cwd)
            mtime = pf.stat().st_mtime
            age_min = (time.time() - mtime) / 60
            lines.append(f"## {rel} (updated {age_min:.0f}min ago)")
            lines.append(pf.read_text().strip())
            lines.append("")

    # Find most recently modified .lean file (indicates active work)
    lean_files = list(root.rglob("*.lean"))
    if lean_files:
        latest = max(lean_files, key=lambda f: f.stat().st_mtime)
        age_min = (time.time() - latest.stat().st_mtime) / 60
        lines.append(f"\n## Latest Activity")
        lines.append(f"Most recent .lean edit: `{latest.relative_to(cwd)}` ({age_min:.0f}min ago)")
        if age_min < 5:
            lines.append("**System is actively working.**")
        elif age_min < 15:
            lines.append("System was recently active.")
        else:
            lines.append(f"**No file edits for {age_min:.0f} minutes.**")

    return "\n".join(lines)


# ─── Child workspace setup ───────────────────────────────────────────────────

def setup_child_workspace(cwd: Path, lemma_file: str, parent_workspace: str) -> str:
    """Create child workspace, copy Stub.lean + Def.lean, rewrite imports.
    Returns the child workspace relative path.

    IDEMPOTENT: if the child workspace already has a po_checkpoint.json,
    it was previously set up and may have made progress. Don't overwrite.
    """
    lemma_path = Path(lemma_file)
    child_workspace = f"{lemma_path.parent}/{lemma_path.stem}"
    child_ws_path = cwd / child_workspace

    # If child already has a checkpoint, it was previously running — don't clobber
    if (child_ws_path / "po_checkpoint.json").exists():
        return child_workspace

    child_ws_path.mkdir(parents=True, exist_ok=True)

    # Copy as child's Stub.lean
    shutil.copy2(cwd / lemma_file, child_ws_path / "Stub.lean")

    # Do NOT copy Def.lean — all files import the root's Stub.Def directly
    # This avoids duplicate declaration conflicts in Lean

    # Rewrite imports: point to root Stub.Def, remove sibling imports
    child_stub = child_ws_path / "Stub.lean"
    root_workspace = parent_workspace.split("/decomposed/")[0]
    rewrite_imports_for_child(child_stub, parent_workspace, child_workspace,
                              root_workspace=root_workspace)

    return child_workspace
