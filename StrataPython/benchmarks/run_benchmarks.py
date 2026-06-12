#!/usr/bin/env python3
"""Benchmark the Python verification pipeline: native types vs `Any`-boxing.

Each `*.tmpl.py` holds one function per scenario, with type placeholders
(`__INT__`, `__REAL__`, `__BOOL__`). Every function is verified twice — at
native types and at the dynamic type `Any` — over its symbolic parameters,
which is where boxing hurts: `Any` reasons through the datatype and can fail
or time out where native types are proved quickly.

For each scenario the runner reports whether the goal was *proved* (all
assertions discharged, no `inconclusive`), the median wall time, and the
speedup of native over `Any`.

Usage: ./run_benchmarks.py [--reps N] [--solver-timeout MS] [--wall S]

Env: STRATA (the strata CLI), STRATA_PYTHON (a python3 with strata.gen).
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
STRATA = Path(os.environ.get("STRATA", ROOT / "StrataCLI/.lake/build/bin/strata"))
PYTHON = os.environ.get("STRATA_PYTHON", "python3")
DIALECT = ROOT / "Tools/Python/dialects/Python.dialect.st.ion"

MODES = {
    "native": {"__INT__": "int", "__REAL__": "float", "__STR__": "str", "__BOOL__": "bool"},
    "Any": {"__INT__": "Any", "__REAL__": "Any", "__STR__": "Any", "__BOOL__": "Any"},
}
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


def instantiate(text: str, subs: dict[str, str]) -> str:
    for placeholder, ty in subs.items():
        text = text.replace(placeholder, ty)
    return text


def compile_to_ion(py: Path, ion: Path) -> None:
    subprocess.run(
        [PYTHON, "-m", "strata.gen", "py_to_strata", "--dialect", str(DIALECT), str(py), str(ion)],
        cwd=ROOT / "Tools/Python", check=True, capture_output=True,
    )


def verify(ion: Path, reps: int, solver_timeout: int, wall: float) -> Outcome:
    cmd = [str(STRATA), "pyAnalyzeLaurel", "--solver-timeout", str(solver_timeout), str(ion)]
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
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--solver-timeout", type=int, default=10000, help="per-query solver cap (ms)")
    ap.add_argument("--wall", type=float, default=20.0, help="per-run wall cap (s)")
    args = ap.parse_args()

    if not STRATA.exists():
        raise SystemExit(f"strata CLI not found at {STRATA} — run: (cd StrataCLI && lake build strata)")

    print(f"{'scenario':<14}{'native':>13}{'Any':>13}{'speedup':>10}")
    print("-" * 50)
    nat_proved = any_proved = total = nat_ms = 0
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for tmpl in sorted(HERE.glob("*.tmpl.py")):
            header, funcs = split_functions(tmpl.read_text())
            for name, src in funcs:
                res = {}
                for mode, subs in MODES.items():
                    py = work / f"{name}_{mode}.py"
                    ion = py.with_suffix(".ion")
                    py.write_text(instantiate(f"{header}\n\n{src}\n", subs))
                    compile_to_ion(py, ion)
                    res[mode] = verify(ion, args.reps, args.solver_timeout, args.wall)
                nat, dyn = res["native"], res["Any"]
                ratio = dyn.ms / nat.ms if nat.ms else 0.0
                speedup = ("∞" if dyn.timed_out
                           else "-" if not ratio
                           else f"{ratio:.0f}x" if ratio >= 10
                           else f"{ratio:.1f}x")
                print(f"{name:<14}{cell(nat):>13}{cell(dyn):>13}{speedup:>10}")
                total += 1
                nat_proved += nat.proved
                any_proved += dyn.proved
                nat_ms += nat.ms
    print("-" * 50)
    print(f"native: {nat_proved}/{total} proved, median {nat_ms / total:.0f}ms      "
          f"Any: {any_proved}/{total} proved")


if __name__ == "__main__":
    main()
