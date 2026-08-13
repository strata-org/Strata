"""Sequential MVP runner: discover → plan → run each attempt → report.

This is the MVP orchestration. It runs attempts ONE AT A TIME (workers effectively
1) through a pluggable `run_attempt` seam, so the whole pipeline — YAML, discovery,
clone sizing, shuffled scheduling, cost/give-up extraction, and the report format —
is exercised end-to-end and can be validated with `--dry-run` (no LLM spend).

Parallel clone-pool execution (phase 2) reuses this exact plan + report: it just
runs the same `run_attempt` across N project clones concurrently instead of serially.
"""

from __future__ import annotations

import time
from pathlib import Path

from .config import BenchConfig, load_config
from .discover import discover_all, Lemma
from .plan import allocate_clones, build_tasks, AttemptTask
from .report import AttemptResult, write_report


def _warn(msg: str) -> None:
    print(f"[bench][warn] {msg}")


def plan_run(cfg: BenchConfig):
    """Discovery + planning (no execution). Returns (lemmas, clone_alloc, tasks)."""
    lemmas = discover_all(cfg, _warn)
    alloc = allocate_clones(cfg, lemmas)
    tasks = build_tasks(cfg, lemmas)
    return lemmas, alloc, tasks


def print_plan(cfg: BenchConfig, lemmas: list[Lemma], alloc: dict[str, int],
               tasks: list[AttemptTask]) -> None:
    print("\n" + "=" * 66)
    print("BENCHMARK PLAN")
    print("=" * 66)
    by_proj: dict[str, int] = {}
    for l in lemmas:
        by_proj[l.project] = by_proj.get(l.project, 0) + 1
    for proj in sorted(by_proj):
        print(f"  {proj}: {by_proj[proj]} lemmas × {cfg.attempts} attempts "
              f"= {by_proj[proj]*cfg.attempts} tasks → {alloc.get(proj,0)} clone(s)")
    print(f"  TOTAL: {len(lemmas)} lemmas, {len(tasks)} attempt-tasks, "
          f"{sum(alloc.values())}/{cfg.workers} clones")
    print(f"  attempts/lemma (best-of-N): {cfg.attempts}   "
          f"per-attempt timeout: {cfg.per_attempt_minutes}min")
    print("=" * 66 + "\n")


def _dry_run_attempt(task: AttemptTask, cfg: BenchConfig) -> AttemptResult:
    """Fake an attempt deterministically (no LLM, no clone) so the pipeline +
    report can be validated cheaply. Marks ~2/3 of attempts 'proven'."""
    l = task.lemma
    proven = (hash((task.lemma_key, task.attempt_idx)) % 3) != 0
    return AttemptResult(
        lemma_key=task.lemma_key, project=l.project, file_rel=l.file_rel,
        theorem=l.theorem, attempt_idx=task.attempt_idx,
        status="proven" if proven else "give_up",
        wall_s=float(30 + (hash(task.lemma_key) % 90)),
        cost_usd=round(1.0 + (hash(task.lemma_key) % 500) / 100.0, 2),
        give_up_reason="" if proven else "dry-run: simulated give-up reason",
        proof_path=f"(dry-run) {l.theorem}.lean" if proven else "",
        clone=f"{l.project}_dryrun",
    )


def run(cfg: BenchConfig) -> int:
    lemmas, alloc, tasks = plan_run(cfg)
    if not lemmas:
        print("[bench] No sorry-theorems discovered. Nothing to do.")
        return 2
    print_plan(cfg, lemmas, alloc, tasks)

    if cfg.dry_run:
        print("[bench] --dry-run: simulating attempts (no clones, no LLM).")
        results = [_dry_run_attempt(t, cfg) for t in tasks]
        report_dir = write_report(cfg.report_dir, results)
        print(f"[bench] Report written to {report_dir}")
        print((report_dir / "summary.txt").read_text())
        return 0

    # Real execution: provision per-project clones, then run each project's tasks
    # across its clones concurrently (all clones run in parallel = K workers total).
    import asyncio
    from .execute import provision_clones, run_attempt

    project_roots = {p.name: p.root for p in cfg.projects}
    print("[bench] Provisioning clones (once; reused across tasks)...")
    clones_by_project = provision_clones(cfg, alloc, project_roots, _warn)
    if not clones_by_project:
        print("[bench] No usable clones — aborting.")
        return 1

    # Group the shuffled tasks by project (order preserved → still shuffled per project).
    tasks_by_project: dict[str, list[AttemptTask]] = {}
    for t in tasks:
        tasks_by_project.setdefault(t.lemma.project, []).append(t)

    results: list[AttemptResult] = []
    results_lock = asyncio.Lock()
    started = time.time()
    done = {"n": 0}

    async def clone_worker(project: str, clone, queue: "asyncio.Queue[AttemptTask]"):
        """One clone processes tasks from its project's queue until drained."""
        while True:
            try:
                task = queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            try:
                # run_attempt is blocking (subprocess) → offload to a thread so
                # sibling clone-workers truly run concurrently.
                res = await asyncio.to_thread(run_attempt, task, cfg, clone)
            except Exception as e:  # noqa: BLE001
                l = task.lemma
                res = AttemptResult(lemma_key=task.lemma_key, project=l.project,
                                    file_rel=l.file_rel, theorem=l.theorem,
                                    attempt_idx=task.attempt_idx, status="error",
                                    detail=str(e), clone=str(clone))
            async with results_lock:
                results.append(res)
                done["n"] += 1
                print(f"[bench] ({done['n']}/{len(tasks)}) {res.status:8} "
                      f"{task.lemma_key} #{task.attempt_idx} "
                      f"({res.wall_s:.0f}s, ${res.cost_usd or 0:.2f})")

    async def drive():
        coros = []
        for project, clones in clones_by_project.items():
            q: asyncio.Queue = asyncio.Queue()
            for t in tasks_by_project.get(project, []):
                q.put_nowait(t)
            for clone in clones:
                coros.append(clone_worker(project, clone, q))
        await asyncio.gather(*coros)

    try:
        asyncio.run(drive())
    except KeyboardInterrupt:
        print("[bench] interrupted — writing partial report.")

    report_dir = write_report(cfg.report_dir, results)
    print(f"[bench] Done in {int(time.time()-started)}s. Report: {report_dir}")
    print((report_dir / "summary.txt").read_text())
    return 0


def main(argv: list[str]) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="StrataSwarm headless benchmark runner")
    ap.add_argument("config", help="path to the benchmark YAML config")
    ap.add_argument("--dry-run", action="store_true",
                    help="discover + plan + simulate attempts + write report; no clones, no LLM")
    ap.add_argument("--plan-only", action="store_true",
                    help="print the discovery + clone plan and exit")
    args = ap.parse_args(argv)

    cfg = load_config(args.config)
    cfg.dry_run = args.dry_run

    if args.plan_only:
        lemmas, alloc, tasks = plan_run(cfg)
        if not lemmas:
            print("[bench] No sorry-theorems discovered.")
            return 2
        print_plan(cfg, lemmas, alloc, tasks)
        return 0
    return run(cfg)
