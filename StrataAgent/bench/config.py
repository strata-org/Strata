"""YAML config schema + parsing for the benchmark runner.

The config declares WHICH theorems to prove (per project, via `*` / subdir /
explicit file+theorems) and HOW MUCH parallelism (workers = total clones,
attempts = best-of-N per lemma). See bench/config.example.yaml.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class TargetSpec:
    """One targeting rule inside a project.

    Exactly one of {all_files, subdir, file} is active:
      - all_files=True         → every .lean under the project root ("*")
      - subdir="Valid"         → every .lean under <root>/Valid
      - file="Test/Bar.lean"   → that one file; `theorems` limits which theorems
                                 ("*" or absent → all sorry-theorems in the file).
    """
    all_files: bool = False
    subdir: str | None = None
    file: str | None = None
    theorems: list[str] | None = None  # None or ["*"] → all sorry-theorems


@dataclass
class ProjectSpec:
    name: str
    root: Path
    targets: list[TargetSpec]


@dataclass
class BenchConfig:
    clone_dir: Path
    persist_dir: Path
    report_dir: Path
    workers: int
    attempts: int
    per_attempt_minutes: float
    cheat_sheet: str
    seed: int
    projects: list[ProjectSpec] = field(default_factory=list)

    # Populated by the CLI, not the YAML.
    dry_run: bool = False


def _resolve_path(v: str) -> Path:
    """Expand ~ (home) AND $VARS (env), then resolve to an absolute path."""
    return Path(os.path.expandvars(os.path.expanduser(str(v)))).resolve()


def _as_path(v: str, field_name: str) -> Path:
    if not v:
        raise ValueError(f"config: '{field_name}' is required")
    return _resolve_path(v)


def _parse_targets(raw: Any, project_name: str) -> list[TargetSpec]:
    # `targets: "*"` → everything.
    if raw == "*" or raw is None:
        return [TargetSpec(all_files=True)]
    if not isinstance(raw, list):
        raise ValueError(
            f"project '{project_name}': `targets` must be \"*\" or a list, got {type(raw).__name__}")
    out: list[TargetSpec] = []
    for i, item in enumerate(raw):
        if item == "*":
            out.append(TargetSpec(all_files=True))
            continue
        if not isinstance(item, dict):
            raise ValueError(f"project '{project_name}': targets[{i}] must be a mapping or \"*\"")
        if "subdir" in item:
            out.append(TargetSpec(subdir=str(item["subdir"])))
        elif "file" in item:
            thms = item.get("theorems")
            if thms == "*" or thms is None:
                thm_list = None
            elif isinstance(thms, list):
                thm_list = [str(t) for t in thms]
            else:
                raise ValueError(
                    f"project '{project_name}': targets[{i}].theorems must be \"*\" or a list")
            out.append(TargetSpec(file=str(item["file"]), theorems=thm_list))
        else:
            raise ValueError(
                f"project '{project_name}': targets[{i}] needs one of `subdir` / `file` / \"*\"")
    return out


def load_config(path: str | Path) -> BenchConfig:
    """Parse + validate a benchmark YAML config. Raises ValueError on any problem."""
    import yaml

    # Expand ~ / $VARS in the config path itself too (so a quoted "~/cfg.yaml"
    # passed programmatically, not just shell-expanded, still resolves).
    p = _resolve_path(path)
    if not p.exists():
        raise ValueError(f"config file not found: {p}")
    raw = yaml.safe_load(p.read_text()) or {}

    par = raw.get("parallelism", {}) or {}
    workers = int(par.get("workers", 1))
    attempts = int(par.get("attempts", 1))
    if workers < 1:
        raise ValueError("parallelism.workers must be >= 1")
    if attempts < 1:
        raise ValueError("parallelism.attempts must be >= 1")

    projects_raw = raw.get("projects") or []
    if not projects_raw:
        raise ValueError("config: at least one project is required")
    projects: list[ProjectSpec] = []
    for pr in projects_raw:
        name = pr.get("name")
        root = pr.get("root")
        if not name or not root:
            raise ValueError("each project needs a `name` and a `root`")
        root_path = _resolve_path(root)
        projects.append(ProjectSpec(
            name=str(name),
            root=root_path,
            targets=_parse_targets(pr.get("targets", "*"), str(name)),
        ))

    return BenchConfig(
        clone_dir=_as_path(raw.get("clone_dir", ""), "clone_dir"),
        persist_dir=_as_path(raw.get("persist_dir", ""), "persist_dir"),
        report_dir=_as_path(raw.get("report_dir", ""), "report_dir"),
        workers=workers,
        attempts=attempts,
        per_attempt_minutes=float(raw.get("per_attempt_minutes", 120)),
        cheat_sheet=str(raw.get("cheat_sheet", "") or ""),
        seed=int(raw.get("seed", 0)),
        projects=projects,
    )
