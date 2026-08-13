"""Theorem discovery: expand a project's TargetSpecs into concrete
(project, file, theorem) work items, using the same Lean oracle the swarm uses.

A "work item" here is a LEMMA (before best-of-N fan-out). Each becomes N attempt
tasks in the planner.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .config import BenchConfig, ProjectSpec, TargetSpec


@dataclass(frozen=True)
class Lemma:
    project: str
    root: str          # absolute project root (str for hashability)
    file_rel: str      # file path RELATIVE to the project root
    theorem: str


def _iter_lean_files(root: Path, spec: TargetSpec) -> list[Path]:
    """Absolute .lean files selected by a TargetSpec (before theorem filtering)."""
    if spec.file:
        f = (root / spec.file)
        return [f] if f.exists() else []
    base = root / spec.subdir if spec.subdir else root
    if not base.exists():
        return []
    # Skip the installed StrataAgent tree and any build output.
    out = []
    for f in sorted(base.rglob("*.lean")):
        parts = set(f.relative_to(root).parts)
        if "StrataAgent" in parts or ".lake" in parts or "lake-packages" in parts:
            continue
        out.append(f)
    return out


# Per-project Lean tools instances (each rooted at THAT project). The global
# get_lean_tools() singleton is rooted at the RUNNING StrataAgent (a different
# project), so it cannot resolve a benchmark project's files — we key a tools
# instance to each project root instead.
_TOOLS_BY_ROOT: dict[str, object] = {}


def _tools_for(root: Path):
    from strataswarm.modules.po_lean import SwarmLeanTools
    key = str(root)
    inst = _TOOLS_BY_ROOT.get(key)
    if inst is None:
        inst = SwarmLeanTools(project_root=str(root))
        _TOOLS_BY_ROOT[key] = inst
    return inst


def _sorry_theorems(root: Path, file_abs: Path) -> tuple[list[str], str | None]:
    """(names of sorry-stubbed theorems in file_abs, error). Uses list_theorems on
    a tools instance ROOTED AT `root`, and passes the path relative to that root."""
    import os

    rel = os.path.relpath(file_abs, root)
    try:
        res = _tools_for(root).list_theorems(rel)
    except Exception as e:  # noqa: BLE001
        return [], f"list_theorems({rel}) raised: {e}"
    if getattr(res, "error", None):
        return [], f"list_theorems({rel}): {res.error}"
    return [t.name for t in res.theorems if t.status == "sorry"], None


def discover_project(cfg: BenchConfig, project: ProjectSpec,
                     warn) -> list[Lemma]:
    """All (file, theorem) lemmas selected by a project's targets. `warn(msg)` is
    called for skips (missing file/subdir, parse errors) so nothing fails silently."""
    lemmas: list[Lemma] = []
    seen: set[tuple[str, str]] = set()
    for spec in project.targets:
        files = _iter_lean_files(project.root, spec)
        if not files and (spec.file or spec.subdir):
            warn(f"[{project.name}] target matched no files: "
                 f"{spec.file or spec.subdir}")
        for f in files:
            names, err = _sorry_theorems(project.root, f)
            if err:
                warn(f"[{project.name}] {err}")
                continue
            # Explicit theorem list on a `file` target restricts to those names.
            if spec.file and spec.theorems:
                wanted = set(spec.theorems)
                missing = wanted - set(names)
                if missing:
                    warn(f"[{project.name}] {spec.file}: requested theorems not "
                         f"found or not sorry-stubbed: {sorted(missing)}")
                names = [n for n in names if n in wanted]
            import os
            rel = os.path.relpath(f, project.root)
            for n in names:
                key = (rel, n)
                if key in seen:
                    continue
                seen.add(key)
                lemmas.append(Lemma(project=project.name, root=str(project.root),
                                    file_rel=rel, theorem=n))
    return lemmas


def discover_all(cfg: BenchConfig, warn) -> list[Lemma]:
    lemmas: list[Lemma] = []
    for project in cfg.projects:
        lemmas.extend(discover_project(cfg, project, warn))
    return lemmas
