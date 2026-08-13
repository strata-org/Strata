"""Planning: turn the discovered lemmas + parallelism knobs into (a) a per-project
clone allocation and (b) a shuffled list of attempt-tasks.

Design (per user direction):
  * A clone is a full copy of ONE project's repo (with StrataAgent/Sandbox inside),
    so a clone of project P can run ANY of P's theorems. We therefore make N_P
    clones of project P, N_P proportional to P's share of the total attempt-tasks,
    with a floor of 1 clone per project that has any work, capped at the total
    worker budget K.
  * Every (lemma, attempt) is an INDEPENDENT task. We do NOT kill siblings; each
    runs to completion and we report k/N proved per lemma as a confidence signal.
  * Tasks are shuffled (seeded) so a project's attempts spread evenly across its
    clones and lemmas interleave — no clustering, trivial scheduling.
"""

from __future__ import annotations

import random
from dataclasses import dataclass

from .config import BenchConfig
from .discover import Lemma


@dataclass(frozen=True)
class AttemptTask:
    lemma: Lemma
    attempt_idx: int        # 1..attempts
    lemma_key: str          # "project::file_rel::theorem" — groups attempts of one lemma


def lemma_key(l: Lemma) -> str:
    return f"{l.project}::{l.file_rel}::{l.theorem}"


def allocate_clones(cfg: BenchConfig, lemmas: list[Lemma]) -> dict[str, int]:
    """N_P clones per project, proportional to each project's attempt-task count,
    floor 1 for any project with work, summing to <= cfg.workers.

    Largest-remainder apportionment so the totals are exact and stable."""
    # Attempt-tasks per project = (#lemmas in project) * attempts.
    per_project: dict[str, int] = {}
    for l in lemmas:
        per_project[l.project] = per_project.get(l.project, 0) + 1
    for k in per_project:
        per_project[k] *= cfg.attempts

    active = {p: n for p, n in per_project.items() if n > 0}
    if not active:
        return {}

    K = cfg.workers
    n_projects = len(active)
    # Can't give every project a clone if K < #projects — give the biggest ones one
    # each, in descending task order, until K runs out.
    if K <= n_projects:
        order = sorted(active, key=lambda p: (-active[p], p))
        return {p: (1 if i < K else 0) for i, p in enumerate(order)}

    total_tasks = sum(active.values())
    # Floor 1 each, then distribute the remaining K - n_projects by largest remainder.
    remaining = K - n_projects
    quotas = {p: 1 for p in active}
    shares = {p: remaining * (active[p] / total_tasks) for p in active}
    base = {p: int(shares[p]) for p in active}
    for p in active:
        quotas[p] += base[p]
    leftover = remaining - sum(base.values())
    # Hand leftovers to the largest fractional remainders.
    frac_order = sorted(active, key=lambda p: (-(shares[p] - base[p]), p))
    for i in range(leftover):
        quotas[frac_order[i % len(frac_order)]] += 1
    return quotas


def build_tasks(cfg: BenchConfig, lemmas: list[Lemma]) -> list[AttemptTask]:
    """Flat, shuffled list of every (lemma, attempt) task."""
    tasks: list[AttemptTask] = []
    for l in lemmas:
        k = lemma_key(l)
        for a in range(1, cfg.attempts + 1):
            tasks.append(AttemptTask(lemma=l, attempt_idx=a, lemma_key=k))
    rng = random.Random(cfg.seed)
    rng.shuffle(tasks)
    return tasks
