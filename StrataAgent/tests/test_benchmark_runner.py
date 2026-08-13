"""Offline tests for the headless benchmark runner MVP (bench/): config parsing,
clone allocation, task planning/shuffle, and report aggregation. No Lean, no LLM.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_benchmark_runner.py
"""

from __future__ import annotations

import os
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from bench.config import load_config, BenchConfig
from bench.discover import Lemma
from bench.plan import allocate_clones, build_tasks, lemma_key
from bench.report import AttemptResult, summarize, write_report, parse_prover_cost_time


def _cfg(workers=8, attempts=3, projects=None):
    return BenchConfig(
        clone_dir=Path("/tmp/clones"), persist_dir=Path("/tmp/proofs"),
        report_dir=Path("/tmp/reports"), workers=workers, attempts=attempts,
        per_attempt_minutes=120, cheat_sheet="", seed=0, projects=projects or [])


def _lemmas(project, n):
    return [Lemma(project=project, root=f"/r/{project}", file_rel=f"F{i}.lean",
                  theorem=f"thm{i}") for i in range(n)]


def test_config_parse():
    y = """
clone_dir: /tmp/c
persist_dir: /tmp/p
report_dir: /tmp/r
parallelism: {workers: 4, attempts: 2}
per_attempt_minutes: 90
projects:
  - name: alpha
    root: /tmp/alpha
    targets: "*"
  - name: beta
    root: /tmp/beta
    targets:
      - subdir: Valid
      - file: T/Bar.lean
        theorems: [a, b]
"""
    with tempfile.NamedTemporaryFile("w", suffix=".yaml", delete=False) as f:
        f.write(y); path = f.name
    try:
        cfg = load_config(path)
        assert cfg.workers == 4 and cfg.attempts == 2
        assert cfg.per_attempt_minutes == 90
        assert [p.name for p in cfg.projects] == ["alpha", "beta"]
        assert cfg.projects[0].targets[0].all_files is True
        assert cfg.projects[1].targets[0].subdir == "Valid"
        assert cfg.projects[1].targets[1].file == "T/Bar.lean"
        assert cfg.projects[1].targets[1].theorems == ["a", "b"]
    finally:
        os.unlink(path)
    print("✓ test_config_parse")


def test_config_expands_home_and_env():
    """Paths with ~ and $VARS must expand (home + env), for top-level dirs AND
    project roots."""
    os.environ["BENCH_TEST_ROOT"] = "/tmp/bench_env_root"
    y = """
clone_dir: ~/benchruns/clones
persist_dir: $BENCH_TEST_ROOT/proofs
report_dir: ~/benchruns/reports
parallelism: {workers: 1, attempts: 1}
projects:
  - name: alpha
    root: ~/projects/alpha
    targets: "*"
"""
    with tempfile.NamedTemporaryFile("w", suffix=".yaml", delete=False) as f:
        f.write(y); path = f.name
    try:
        cfg = load_config(path)
        # Compare against expanduser+resolve (resolve() may follow symlinks like
        # /home -> /local/home, so both sides must resolve identically).
        exp = lambda s: Path(os.path.expanduser(s)).resolve()
        assert cfg.clone_dir == exp("~/benchruns/clones"), cfg.clone_dir
        assert cfg.persist_dir == Path("/tmp/bench_env_root/proofs").resolve(), cfg.persist_dir
        assert cfg.projects[0].root == exp("~/projects/alpha"), cfg.projects[0].root
        # No unexpanded markers remain.
        assert "~" not in str(cfg.clone_dir) and "$" not in str(cfg.persist_dir)
    finally:
        os.unlink(path)
        os.environ.pop("BENCH_TEST_ROOT", None)
    print("✓ test_config_expands_home_and_env")


def test_config_rejects_bad():
    for bad in ["parallelism: {workers: 0}\nprojects: [{name: a, root: /x}]",
                "projects: []"]:
        with tempfile.NamedTemporaryFile("w", suffix=".yaml", delete=False) as f:
            f.write("clone_dir: /c\npersist_dir: /p\nreport_dir: /r\n" + bad); path = f.name
        try:
            raised = False
            try:
                load_config(path)
            except ValueError:
                raised = True
            assert raised, f"expected ValueError for: {bad}"
        finally:
            os.unlink(path)
    print("✓ test_config_rejects_bad")


def test_allocate_clones_proportional():
    # alpha 10 lemmas, beta 2 lemmas, attempts=3 → tasks 30 vs 6; K=8.
    cfg = _cfg(workers=8, attempts=3)
    lemmas = _lemmas("alpha", 10) + _lemmas("beta", 2)
    alloc = allocate_clones(cfg, lemmas)
    assert sum(alloc.values()) == 8, alloc
    assert alloc["alpha"] >= alloc["beta"], alloc
    assert alloc["beta"] >= 1, "every project with work gets >=1 clone"
    print("✓ test_allocate_clones_proportional", alloc)


def test_allocate_clones_fewer_workers_than_projects():
    cfg = _cfg(workers=1, attempts=1)
    lemmas = _lemmas("alpha", 5) + _lemmas("beta", 3)
    alloc = allocate_clones(cfg, lemmas)
    assert sum(alloc.values()) == 1
    assert alloc.get("alpha", 0) == 1 and alloc.get("beta", 0) == 0  # bigger project wins
    print("✓ test_allocate_clones_fewer_workers_than_projects")


def test_build_tasks_count_and_deterministic_shuffle():
    cfg = _cfg(workers=4, attempts=3, )
    lemmas = _lemmas("alpha", 4)
    t1 = build_tasks(cfg, lemmas)
    t2 = build_tasks(cfg, lemmas)
    assert len(t1) == 4 * 3, "one task per (lemma, attempt)"
    assert [ (t.lemma_key, t.attempt_idx) for t in t1 ] == \
           [ (t.lemma_key, t.attempt_idx) for t in t2 ], "seeded shuffle must be deterministic"
    # every lemma has exactly `attempts` tasks
    from collections import Counter
    c = Counter(t.lemma_key for t in t1)
    assert all(v == 3 for v in c.values())
    print("✓ test_build_tasks_count_and_deterministic_shuffle")


def test_summarize_confidence_k_of_n():
    l = _lemmas("alpha", 1)[0]
    key = lemma_key(l)
    def mk(idx, status, reason="", cost=1.0, wall=10.0, proof=""):
        return AttemptResult(lemma_key=key, project=l.project, file_rel=l.file_rel,
                             theorem=l.theorem, attempt_idx=idx, status=status,
                             wall_s=wall, cost_usd=cost, give_up_reason=reason, proof_path=proof)
    results = [mk(1, "proven", cost=2, wall=50, proof="/p/thm0.lean"),
               mk(2, "give_up", reason="false as stated", cost=3, wall=99),
               mk(3, "proven", cost=1, wall=30, proof="/p/thm0.lean")]
    s = summarize(results)[0]
    assert s.confidence == "2/3", s.confidence
    assert s.proved == 2 and s.attempts == 3
    assert s.best_wall_s == 30.0                  # fastest proven
    assert s.total_cost_usd == 6.0
    assert s.proof_path == "/p/thm0.lean"
    assert "false as stated" in s.give_up_reasons
    print("✓ test_summarize_confidence_k_of_n")


def test_write_report_files():
    l = _lemmas("alpha", 1)[0]; key = lemma_key(l)
    results = [AttemptResult(lemma_key=key, project=l.project, file_rel=l.file_rel,
                             theorem=l.theorem, attempt_idx=1, status="proven",
                             wall_s=12, cost_usd=1.5, proof_path="/p/x.lean")]
    d = Path(tempfile.mkdtemp())
    try:
        out = write_report(d, results)
        assert (out / "attempts.jsonl").exists()
        assert (out / "summary.jsonl").exists()
        assert "1/1" in (out / "summary.txt").read_text()
    finally:
        import shutil; shutil.rmtree(d, ignore_errors=True)
    print("✓ test_write_report_files")


def test_parse_prover_cost_time():
    import json
    d = Path(tempfile.mkdtemp())
    try:
        p = d / "Prover_v5_2.jsonl"
        p.write_text("\n".join([
            json.dumps({"ts": 1, "type": "message", "data": "[PO5] working..."}),
            json.dumps({"ts": 2, "type": "message",
                        "data": "[PO5] Finished: stage=done, proved=1, cycles=0, time=157.1min, cost=$129.48"}),
        ]))
        cost, minutes = parse_prover_cost_time(p)
        assert cost == 129.48, cost
        assert minutes == 157.1, minutes
    finally:
        import shutil; shutil.rmtree(d, ignore_errors=True)
    print("✓ test_parse_prover_cost_time")


def test_proof_filename_escapes_and_avoids_clashes():
    """Proof filenames must escape unsafe chars AND never collide across distinct
    lemmas — including the real IMO case where Q2/Q4/Q5/Q6 all have `main_theorem`."""
    from bench.execute import proof_filename, _sanitize

    # 1. Same theorem name in different files → DIFFERENT files (the real clash).
    names = {proof_filename(f"IMO2026/Q{q}/problem.lean", "main_theorem") for q in (2, 4, 5, 6)}
    assert len(names) == 4, f"main_theorem across Q2/Q4/Q5/Q6 collided: {names}"

    # 2. Deterministic: same lemma → same filename (best-of-N attempts overwrite).
    a = proof_filename("IMO2026/Q1/problem.lean", "Mval_gt_one")
    b = proof_filename("IMO2026/Q1/problem.lean", "Mval_gt_one")
    assert a == b

    # 3. Unsafe chars escaped (namespaces, Greek/subscripts, guillemets, primes, /).
    for thm in ["CallElim.foo", "pieceLengths_lengthₙ", "«weird»", "foo'", "a/b c"]:
        fn = proof_filename("X/Y.lean", thm)
        assert fn.endswith(".lean")
        stem = fn[:-5]
        assert re.fullmatch(r"[A-Za-z0-9._-]+", stem), f"unsafe filename: {fn}"

    # 4. Distinct unicode names that sanitize to the same string still differ (hash).
    n1 = proof_filename("F.lean", "αβ")
    n2 = proof_filename("F.lean", "γδ")   # both → "_" under sanitize, hash disambiguates
    assert n1 != n2
    assert _sanitize("a/b:c") == "a_b_c"
    print("✓ test_proof_filename_escapes_and_avoids_clashes")


def _main():
    for fn in (test_config_parse, test_config_expands_home_and_env,
               test_proof_filename_escapes_and_avoids_clashes,
               test_config_rejects_bad,
               test_allocate_clones_proportional,
               test_allocate_clones_fewer_workers_than_projects,
               test_build_tasks_count_and_deterministic_shuffle,
               test_summarize_confidence_k_of_n, test_write_report_files,
               test_parse_prover_cost_time):
        fn()
    print("ALL BENCHMARK-RUNNER TESTS PASSED")


if __name__ == "__main__":
    _main()
