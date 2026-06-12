#!/usr/bin/env python3
"""Benchmark the impact of native typed lowering.

The same type-annotated programs (`benchmarks.py`) are verified on two strata
builds:

  before — a build *without* this change (e.g. `main`), where an annotated
           `int` is still boxed in the `Any` datatype (the annotation survives
           only as an `isfrom_int` precondition).
  after  — this branch, where annotated values lower to native SMT sorts.

The Python source is identical for both runs, so the proposition proved is the
same; only the Laurel encoding differs. The reported gap is therefore the cost
of the representation, nothing else.

For each scenario the runner reports whether the goal was *proved* (all
assertions discharged, no `inconclusive`), the median wall time, and the
speedup of `after` over `before`.

Usage: ./run_benchmarks.py [--reps N] [--solver-timeout MS] [--wall S]

Env:
  STRATA_AFTER   strata CLI built from this branch (default: the in-tree build).
  STRATA_BEFORE  strata CLI built from the baseline. Build it once, e.g.:
                   git worktree add /tmp/strata-main main
                   (cd /tmp/strata-main/StrataCLI && lake build strata)
                 then export STRATA_BEFORE=/tmp/strata-main/StrataCLI/.lake/build/bin/strata
                 If unset, only the `after` build is measured.
  STRATA_PYTHON  a python3 with strata.gen (default: python3).
"""
from __future__ import annotations

import argparse
import os
import re
import statistics
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STRATA_AFTER = Path(os.environ.get("STRATA_AFTER",
                    os.environ.get("STRATA", ROOT / "StrataCLI/.lake/build/bin/strata")))
STRATA_BEFORE = os.environ.get("STRATA_BEFORE")  # optional
PYTHON = os.environ.get("STRATA_PYTHON", "python3")
DIALECT = ROOT / "Tools/Python/dialects/Python.dialect.st.ion"
RESULT_RE = re.compile(r"(\d+) passed, (\d+) failed, (\d+) inconclusive")


@dataclass
class Outcome:
    proved: bool      # all assertions discharged (no failures/inconclusive)
    timed_out: bool
    ms: float


def split_functions(text: str) -> tuple[str, list[tuple[str, str]]]:
    header: list[str] = []
    funcs: list[tuple[str, list[str]]] = []
    for line in text.splitlines():
        if line.startswith("def "):
            funcs.append((line[4 : line.index("(")], [line]))
        elif funcs:
            funcs[-1][1].append(line)
        else:
            header.append(line)
    return "\n".join(header), [(n, "\n".join(b)) for n, b in funcs]


def compile_to_ion(py: Path, ion: Path) -> None:
    subprocess.run(
        [PYTHON, "-m", "strata.gen", "py_to_strata", "--dialect", str(DIALECT), str(py), str(ion)],
        cwd=ROOT / "Tools/Python", check=True, capture_output=True,
    )


def verify(strata: Path, ion: Path, reps: int, solver_timeout: int, wall: float) -> Outcome:
    cmd = [str(strata), "pyAnalyzeLaurel", "--solver-timeout", str(solver_timeout), str(ion)]
    proved, samples = False, []
    for rep in range(reps + 1):  # one extra warmup run, discarded, to absorb cold start
        start = time.perf_counter()
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=wall)
        except subprocess.TimeoutExpired:
            return Outcome(proved=False, timed_out=True, ms=wall * 1000)
        if rep > 0:
            samples.append((time.perf_counter() - start) * 1000)
        if (m := RESULT_RE.search(out.stdout)):
            p, f, i = map(int, m.groups())
            proved = p > 0 and f == 0 and i == 0
    return Outcome(proved=proved, timed_out=False, ms=statistics.median(samples))


def cell(o: Outcome) -> str:
    mark = "✓" if o.proved else "✗"
    t = "timeout" if o.timed_out else f"{o.ms:.0f}ms"
    return f"{mark} {t:>9}"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--solver-timeout", type=int, default=10000, help="per-query solver cap (ms)")
    ap.add_argument("--wall", type=float, default=20.0, help="per-run wall cap (s)")
    args = ap.parse_args()

    if not STRATA_AFTER.exists():
        raise SystemExit(f"strata CLI not found at {STRATA_AFTER} — run: (cd StrataCLI && lake build strata)")
    before = Path(STRATA_BEFORE) if STRATA_BEFORE else None
    if before and not before.exists():
        raise SystemExit(f"STRATA_BEFORE set but not found at {before}")
    if not before:
        print("note: STRATA_BEFORE unset — measuring only the 'after' build "
              "(see --help to build a baseline).\n")

    print(f"{'scenario':<14}{'before':>13}{'after':>13}{'speedup':>10}")
    print("-" * 50)
    aft_proved = bef_proved = total = aft_ms = 0
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for src_file in sorted(HERE.glob("*.py")):
            if src_file.name == Path(__file__).name:
                continue
            header, funcs = split_functions(src_file.read_text())
            for name, src in funcs:
                py = work / f"{name}.py"
                ion = py.with_suffix(".ion")
                py.write_text(f"{header}\n\n{src}\n")
                compile_to_ion(py, ion)
                aft = verify(STRATA_AFTER, ion, args.reps, args.solver_timeout, args.wall)
                bef = verify(before, ion, args.reps, args.solver_timeout, args.wall) if before else None
                bef_cell = cell(bef) if bef else f"{'-':>11}"
                if bef and bef.ms and aft.ms:
                    ratio = bef.ms / aft.ms
                    speedup = ("∞" if bef.timed_out
                               else f"{ratio:.0f}x" if ratio >= 10
                               else f"{ratio:.1f}x")
                else:
                    speedup = "-"
                print(f"{name:<14}{bef_cell:>13}{cell(aft):>13}{speedup:>10}")
                total += 1
                aft_proved += aft.proved
                bef_proved += bef.proved if bef else 0
                aft_ms += aft.ms
    print("-" * 50)
    summary = f"after: {aft_proved}/{total} proved, median {aft_ms / total:.0f}ms"
    if before:
        summary += f"      before: {bef_proved}/{total} proved"
    print(summary)


if __name__ == "__main__":
    main()
