"""Phase-2 execution: provision per-project clones and run one attempt in a clone.

Isolation is purely FILESYSTEM: each clone is a full copy of a project's repo with
its own StrataAgent/Sandbox, oleans, and ledger. The headless launcher runs no HTTP
server (unlike the dashboard), and lean-lsp MCP is stdio + lake servers are keyed by
path — so concurrent clones never collide and NO ports are needed.

Per attempt: run_headless.py in the clone (setup → prover_v5 → deep validation, no
monitor/clarifier), parse its JSON result, pull cost/time from the clone's
Prover_v5 log, and on success copy the proven Stub.lean into persist_dir for reuse.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

from .config import BenchConfig
from .plan import AttemptTask
from .report import AttemptResult, find_prover_log, parse_prover_cost_time


def _sanitize(s: str) -> str:
    """Make a string safe as a single filename component: keep [A-Za-z0-9._-],
    collapse everything else (dots-in-namespaces, Greek, subscripts, «», primes,
    slashes, spaces) to '_'. Never empty."""
    out = re.sub(r"[^A-Za-z0-9._-]+", "_", s).strip("._-")
    return out or "x"


def proof_filename(file_rel: str, theorem: str) -> str:
    """A filesystem-safe, COLLISION-FREE proof filename for one lemma.

    Escapes both the file path and the theorem name, and appends a short hash of
    the ORIGINAL (file_rel, theorem) so that:
      * two DIFFERENT lemmas never collide — even if they share a theorem name
        across files (Q2/Q4/Q5/Q6 all have `main_theorem`), or sanitize to the
        same string (unicode → '_');
      * the SAME lemma always maps to the SAME file (deterministic — best-of-N
        attempts of one lemma overwrite, which is intended: same proof target).
    The file-path component (parent dirs included) disambiguates same-named
    theorems in different files even before the hash."""
    stem = _sanitize(file_rel[:-5] if file_rel.endswith(".lean") else file_rel)
    thm = _sanitize(theorem)
    h = hashlib.sha1(f"{file_rel}::{theorem}".encode("utf-8")).hexdigest()[:8]
    name = f"{stem}__{thm}__{h}.lean"
    if len(name) > 200:  # stay well under the 255-byte filename limit
        name = f"{thm[:80]}__{h}.lean"
    return name

# This repo's StrataAgent (source for installing into project clones that lack one).
_STRATA_AGENT_SRC = Path(__file__).resolve().parent.parent   # .../StrataAgent
RESULT_PREFIX = "__HEADLESS_RESULT__"


# ── Clone provisioning ────────────────────────────────────────────────────────
def _has_lakefile(d: Path) -> bool:
    return (d / "lakefile.toml").exists() or (d / "lakefile.lean").exists()


def _clone_ready(dest: Path) -> bool:
    """A usable clone: a Lean project with a StrataAgent that has a venv."""
    return (_has_lakefile(dest) and (dest / "StrataAgent").is_dir()
            and (dest / "StrataAgent" / ".venv" / "bin" / "python").exists())


def ensure_clone(project_root: Path, dest: Path, warn) -> Path | None:
    """Make (or reuse) one project clone at `dest`. Idempotent: an existing ready
    clone is reused as-is. Returns the clone path, or None on failure.

    Steps for a fresh clone:
      1. cp -a the project repo → dest (preserves .lake so lake build stays warm).
      2. If dest has no StrataAgent, install this repo's StrataAgent via
         clone_strata_agent.sh (wires lakefile targets + venv + setup).
    """
    if _clone_ready(dest):
        return dest
    if not _has_lakefile(project_root):
        warn(f"project root is not a Lean project (no lakefile): {project_root}")
        return None
    dest.parent.mkdir(parents=True, exist_ok=True)
    if not dest.exists():
        print(f"[bench] cloning {project_root} → {dest} (cp -a; may be large/slow)")
        r = subprocess.run(["cp", "-a", str(project_root), str(dest)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            warn(f"clone copy failed: {r.stderr[-300:]}")
            return None
    # Ensure a StrataAgent is present + set up inside the clone.
    if not (dest / "StrataAgent" / ".venv").exists():
        print(f"[bench] installing StrataAgent into {dest} (clone_strata_agent.sh)")
        script = _STRATA_AGENT_SRC / "clone_strata_agent.sh"
        r = subprocess.run(["bash", str(script), str(_STRATA_AGENT_SRC)],
                           cwd=str(dest), capture_output=True, text=True, timeout=3600)
        if r.returncode != 0:
            warn(f"clone_strata_agent.sh failed in {dest}: {r.stderr[-400:]}")
            return None
    return dest if _clone_ready(dest) else None


def provision_clones(cfg: BenchConfig, alloc: dict[str, int],
                     project_roots: dict[str, Path], warn) -> dict[str, list[Path]]:
    """Create alloc[project] clones per project under cfg.clone_dir, named
    <project>_<i>. Returns {project: [clone_path, ...]}. Clones with no ready
    result are dropped (with a warning)."""
    out: dict[str, list[Path]] = {}
    for name, n in alloc.items():
        if n <= 0:
            continue
        root = project_roots[name]
        clones: list[Path] = []
        for i in range(1, n + 1):
            dest = cfg.clone_dir / f"{name}_{i}"
            c = ensure_clone(root, dest, warn)
            if c is not None:
                clones.append(c)
        if not clones:
            warn(f"[{name}] no usable clones provisioned — project will be skipped")
        else:
            out[name] = clones
    return out


# ── One attempt in a clone ──────────────────────────────────────────────────
def _parse_result_line(stdout: str) -> dict | None:
    for line in reversed(stdout.splitlines()):
        if line.startswith(RESULT_PREFIX):
            try:
                return json.loads(line[len(RESULT_PREFIX):])
            except json.JSONDecodeError:
                return None
    return None


def _persist_proof(cfg: BenchConfig, clone: Path, task: AttemptTask,
                   stub_rel: str) -> str:
    """Copy the proven Stub.lean into
    persist_dir/<project>/<escaped-file>__<escaped-theorem>__<hash>.lean.
    Escaped + hash-suffixed so distinct lemmas never clash (see proof_filename).
    Returns the persisted path (str), or "" on failure."""
    src = clone / stub_rel
    if not src.exists():
        return ""
    dst = cfg.persist_dir / task.lemma.project / proof_filename(
        task.lemma.file_rel, task.lemma.theorem)
    dst.parent.mkdir(parents=True, exist_ok=True)
    try:
        shutil.copy2(src, dst)
        return str(dst)
    except OSError:
        return ""


def run_attempt(task: AttemptTask, cfg: BenchConfig, clone: Path | None = None) -> AttemptResult:
    """Run ONE (lemma, attempt) in `clone` via the headless launcher. `clone` is
    required for real runs (the parallel scheduler supplies it)."""
    l = task.lemma
    base = AttemptResult(
        lemma_key=task.lemma_key, project=l.project, file_rel=l.file_rel,
        theorem=l.theorem, attempt_idx=task.attempt_idx, status="error",
        clone=str(clone) if clone else "")
    if clone is None:
        base.detail = "no clone assigned"
        return base

    py = clone / "StrataAgent" / ".venv" / "bin" / "python"
    launcher = clone / "StrataAgent" / "run_headless.py"
    cmd = [str(py), str(launcher), "--theorem-file", l.file_rel, "--theorem", l.theorem,
           "--max-run-minutes", str(cfg.per_attempt_minutes)]
    if cfg.cheat_sheet:
        cmd += ["--cheat-sheet", cfg.cheat_sheet]

    timeout_s = cfg.per_attempt_minutes * 60 + 300  # grace beyond the prover's own cap
    try:
        proc = subprocess.run(cmd, cwd=str(clone), capture_output=True, text=True,
                              timeout=timeout_s)
    except subprocess.TimeoutExpired:
        base.status = "timeout"
        base.wall_s = timeout_s
        base.detail = "attempt exceeded per_attempt_minutes"
        return base

    result = _parse_result_line(proc.stdout)
    if result is None:
        base.status = "error"
        base.detail = f"no result line (rc={proc.returncode}); stderr: {proc.stderr[-300:]}"
        return base

    base.status = result.get("status", "error")
    base.wall_s = float(result.get("wall_s", 0.0) or 0.0)
    base.give_up_reason = str(result.get("give_up_reason") or result.get("user_fix_request") or "")

    # Cost/time from the clone's newest Prover_v5 log (authoritative $ figure).
    session_dir = clone / "StrataAgent" / "strataswarm" / "temp" / "sessions"
    plog = find_prover_log(session_dir)
    if plog is not None:
        cost, _minutes = parse_prover_cost_time(plog)
        base.cost_usd = cost

    if base.status == "proven":
        base.proof_path = _persist_proof(cfg, clone, task, result.get("stub_rel", "StrataAgent/Sandbox/Stub.lean"))
    return base
