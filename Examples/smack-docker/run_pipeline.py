#!/usr/bin/env python3
"""Run the SMACK → BoogieToStrata → Strata verify pipeline on .bpl files.

Usage:
    python3 run_pipeline.py [--backends deductive,bugFinding,cbmc] [programs/*.bpl ...]

If no arguments given, runs on all .bpl files in the programs/ directory.

Requires:
    - dotnet SDK (default: ~/.dotnet/dotnet)
    - BoogieToStrata built (Tools/BoogieToStrata/Source/BoogieToStrata.csproj)
    - strata binary (.lake/build/bin/strata)
    - strip_smack_prelude.py and fix_core_st.py in the same directory as this script

Optional:
    - StrataCoreToGoto (.lake/build/bin/StrataCoreToGoto) for CBMC backend
    - cbmc and symtab2gb for full CBMC verification
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
STRATA_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "strata"
BOOGIE_TO_STRATA_PROJ = REPO_ROOT / "Tools" / "BoogieToStrata" / "Source" / "BoogieToStrata.csproj"
STRATA_CORE_TO_GOTO = REPO_ROOT / ".lake" / "build" / "bin" / "StrataCoreToGoto"
CBMC_BIN = shutil.which("cbmc")
SYMTAB2GB_BIN = shutil.which("symtab2gb")
STRIP_SCRIPT = SCRIPT_DIR / "strip_smack_prelude.py"
FIX_SCRIPT = SCRIPT_DIR / "fix_core_st.py"

# Find dotnet
DOTNET = None
for candidate in [
    os.path.expanduser("~/.dotnet/dotnet"),
    "dotnet",
]:
    if Path(candidate).exists() or subprocess.run(
        ["which", candidate], capture_output=True
    ).returncode == 0:
        DOTNET = candidate
        break


class PipelineResult:
    def __init__(self, name: str):
        self.name = name
        self.translation_steps: list[tuple[str, str, str]] = []  # (step_name, status, detail)
        self.backend_results: dict[str, tuple[str, str]] = {}  # backend -> (status, detail)

    def add_step(self, step: str, status: str, detail: str = ""):
        self.translation_steps.append((step, status, detail))

    def add_backend(self, backend: str, status: str, detail: str = ""):
        self.backend_results[backend] = (status, detail)

    @property
    def final_status(self) -> str:
        for _, status, _ in reversed(self.translation_steps):
            if status not in ("OK",):
                return status
        for _, (status, _) in self.backend_results.items():
            if status in ("PASS",):
                return "PASS"
        for _, (status, _) in self.backend_results.items():
            if status in ("FAIL",):
                return "FAIL"
        return "OK"


def run_cmd(cmd: list[str], cwd: str = None, timeout: int = 60) -> tuple[int, str, str]:
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, cwd=cwd, timeout=timeout
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT"
    except FileNotFoundError as e:
        return -1, "", str(e)


def run_translation(bpl_path: Path, tmpdir: Path, result: PipelineResult) -> Path | None:
    """Run strip -> BoogieToStrata -> fix. Returns path to fixed .core.st or None on failure."""
    name = bpl_path.stem
    stripped = tmpdir / f"{name}_stripped.bpl"
    core_st = tmpdir / f"{name}.core.st"
    fixed_st = tmpdir / f"{name}_fixed.core.st"

    # Step 1: Strip SMACK prelude
    rc, stdout, stderr = run_cmd(
        [sys.executable, str(STRIP_SCRIPT), str(bpl_path), str(stripped)]
    )
    if rc != 0:
        result.add_step("Strip prelude", "FAIL", stderr.strip())
        return None
    m = re.search(r"Stripped (\d+) prelude", stderr)
    detail = m.group(0) if m else "OK"
    result.add_step("Strip prelude", "OK", detail)

    # Step 2: BoogieToStrata
    if DOTNET is None:
        result.add_step("BoogieToStrata", "FAIL", "dotnet not found")
        return None

    rc, stdout, stderr = run_cmd(
        [DOTNET, "run", "--project", str(BOOGIE_TO_STRATA_PROJ), "--", str(stripped)],
        cwd=str(BOOGIE_TO_STRATA_PROJ.parent.parent),
        timeout=120,
    )
    if rc != 0:
        err = stderr.strip()
        if "Failed translation:" in err:
            msg = err.split("Failed translation:")[-1].strip()
            msg = re.sub(r'.*/([^/]+\.bpl)', r'\1', msg)
            err = msg
        elif "Failed to typecheck" in err:
            err = err.split("\n")[-1].strip()
        elif "Failed to parse" in err:
            err = "Parse error"
        result.add_step("BoogieToStrata", "FAIL", err)
        return None

    core_st.write_text(stdout)
    lines = stdout.count("\n")
    result.add_step("BoogieToStrata", "OK", f"{lines} lines")

    # Step 3: Fix .core.st
    rc, stdout, stderr = run_cmd(
        [sys.executable, str(FIX_SCRIPT), str(core_st), str(fixed_st)]
    )
    if rc != 0:
        result.add_step("fix_core_st", "FAIL", stderr.strip())
        return None
    result.add_step("fix_core_st", "OK", "")

    return fixed_st


def list_procedures(core_st: Path) -> list[str]:
    """Return procedure names in declaration order."""
    procs = []
    for line in core_st.read_text().splitlines():
        m = re.match(r"procedure +([A-Za-z_$][A-Za-z0-9_$.]*)\(", line)
        if m:
            procs.append(m.group(1))
    return procs


def parse_strata_output(output: str, mode: str, label: str) -> tuple[str, str]:
    """Classify a single `strata verify` invocation. Returns (status, detail)."""
    if "All 0 goals passed" in output:
        return ("WARN", "0 VCs")
    if re.search(r"All \d+ goals passed", output):
        m = re.search(r"All (\d+) goals passed", output)
        return ("PASS", f"{m.group(1)} VCs")
    if "cannot apply statement-level transform to CFG body" in output:
        return ("SKIP", "CFG body (transforms unsupported)")
    if "Cannot find this fvar" in output and "__nondet" in output:
        return ("SKIP", "Nondet goto type-check (#1162)")
    if "a declaration of this name already exists" in output:
        return ("FAIL", "Namespace collision")
    if "unexpected type" in output:
        m = re.search(r'name := "(\w+)"', output)
        op = m.group(1) if m else "unknown"
        return ("FAIL", f"Type synonym panic '{op}'")
    if "goals passed" in output and "failed" in output:
        m = re.search(r"(\d+) goals passed, (\d+) failed", output)
        if m:
            return ("PARTIAL", f"{m.group(1)} pass, {m.group(2)} fail")
        return ("FAIL", "Unknown verify output")
    if "TIMEOUT" in output:
        return ("TIMEOUT", "")
    for line in output.split("\n"):
        if "error:" in line.lower() or "Error" in line or "PANIC" in line:
            return ("FAIL", line.strip()[:80])
    return ("FAIL", "Unknown output")


def run_strata_split_procs(core_st: Path, mode: str, result: PipelineResult):
    """Run `strata verify` once per procedure and aggregate.

    Sidesteps the cross-procedure Env.error contamination bug: when one
    procedure's PE evaluation errors, its env is threaded into all later
    procedures and silently suppresses their VCs (visible in the README
    snapshot as `aws_array_eq` -> 0 VCs / WARN). Splitting per-procedure
    gives each procedure a fresh env.
    """
    if not STRATA_BIN.exists():
        result.add_backend(mode, "FAIL", f"Binary not found: {STRATA_BIN}")
        return

    procs = list_procedures(core_st)
    if not procs:
        result.add_backend(mode, "FAIL", "No procedures found")
        return

    total_pass = 0
    total_fail = 0
    contributing = 0
    failed_procs: list[str] = []
    skipped_procs: list[tuple[str, str]] = []
    for proc in procs:
        rc, stdout, stderr = run_cmd(
            [str(STRATA_BIN), "verify", "--check-mode", mode,
             "--procedures", proc, str(core_st)],
            timeout=120,
        )
        output = stdout + stderr
        status, detail = parse_strata_output(output, mode, proc)
        if status == "PASS":
            m = re.search(r"All (\d+) goals passed", output)
            total_pass += int(m.group(1)) if m else 0
            contributing += 1
        elif status == "PARTIAL":
            m = re.search(r"(\d+) goals passed, (\d+) failed", output)
            if m:
                total_pass += int(m.group(1))
                total_fail += int(m.group(2))
            failed_procs.append(proc)
            contributing += 1
        elif status == "FAIL":
            failed_procs.append(proc)
        elif status in ("SKIP", "TIMEOUT", "WARN"):
            if status != "WARN":  # WARN = 0 VCs is normal for decl-only procs
                skipped_procs.append((proc, status))

    if total_fail > 0:
        result.add_backend(
            mode, "PARTIAL",
            f"{total_pass} pass, {total_fail} fail across {contributing} procs ({','.join(failed_procs[:3])})"
        )
    elif total_pass > 0:
        suffix = ""
        if skipped_procs:
            suffix = f" ({len(skipped_procs)} proc skipped)"
        result.add_backend(mode, "PASS", f"{total_pass} VCs across {contributing} procs{suffix}")
    elif failed_procs:
        result.add_backend(mode, "FAIL", f"{len(failed_procs)} procs failed: {','.join(failed_procs[:3])}")
    else:
        result.add_backend(mode, "WARN", f"0 VCs across {len(procs)} procs")


def run_strata_backend(core_st: Path, mode: str, result: PipelineResult):
    if not STRATA_BIN.exists():
        result.add_backend(mode, "FAIL", f"Binary not found: {STRATA_BIN}")
        return

    rc, stdout, stderr = run_cmd(
        [str(STRATA_BIN), "verify", "--check-mode", mode, str(core_st)], timeout=120
    )
    output = stdout + stderr
    if "All 0 goals passed" in output:
        result.add_backend(mode, "WARN", "0 VCs")
    elif re.search(r"All \d+ goals passed", output):
        m = re.search(r"All (\d+) goals passed", output)
        result.add_backend(mode, "PASS", f"{m.group(1)} VCs")
    elif "cannot apply statement-level transform to CFG body" in output:
        result.add_backend(mode, "SKIP", "CFG body (transforms unsupported)")
    elif "Cannot find this fvar" in output and "__nondet" in output:
        result.add_backend(mode, "SKIP", "Nondet goto type-check (#1162)")
    elif "a declaration of this name already exists" in output:
        result.add_backend(mode, "FAIL", "Namespace collision")
    elif "unexpected type" in output:
        m = re.search(r'name := "(\w+)"', output)
        op = m.group(1) if m else "unknown"
        result.add_backend(mode, "FAIL", f"Type synonym panic '{op}'")
    elif "goals passed" in output and "failed" in output:
        m = re.search(r"(\d+) goals passed, (\d+) failed", output)
        if m:
            result.add_backend(mode, "PARTIAL", f"{m.group(1)} pass, {m.group(2)} fail")
        else:
            result.add_backend(mode, "FAIL", "Unknown verify output")
    elif rc == -1 and "TIMEOUT" in stderr:
        result.add_backend(mode, "TIMEOUT", "")
    elif rc != 0:
        for line in output.split("\n"):
            if "error:" in line.lower() or "Error" in line or "PANIC" in line:
                result.add_backend(mode, "FAIL", line.strip()[:80])
                return
        result.add_backend(mode, "FAIL", f"Exit code {rc}")
    else:
        result.add_backend(mode, "FAIL", "Unknown output")


def run_cbmc_backend(core_st: Path, tmpdir: Path, result: PipelineResult):
    if not STRATA_CORE_TO_GOTO.exists():
        result.add_backend("cbmc", "FAIL", "StrataCoreToGoto not found")
        return

    # Step 1: Core -> GOTO JSON
    rc, stdout, stderr = run_cmd([
        str(STRATA_CORE_TO_GOTO),
        "--output-dir", str(tmpdir),
        str(core_st)
    ], timeout=120)
    if rc != 0:
        err = stderr.strip()
        for line in err.split("\n"):
            if "error" in line.lower() or "Error" in line:
                result.add_backend("cbmc", "FAIL", f"CoreToGoto: {line.strip()[:60]}")
                return
        result.add_backend("cbmc", "FAIL", f"CoreToGoto exit {rc}")
        return

    # Step 2: Check output files exist
    symtab_files = list(tmpdir.glob("*.symtab.json"))
    goto_files = list(tmpdir.glob("*.goto.json"))
    if not symtab_files or not goto_files:
        result.add_backend("cbmc", "FAIL", "GOTO JSON not generated")
        return

    symtab = symtab_files[0]
    goto_json = goto_files[0]

    if CBMC_BIN is None or SYMTAB2GB_BIN is None:
        result.add_backend("cbmc", "OK", f"GOTO JSON generated ({symtab.name})")
        return

    # Step 3: Convert to GOTO binary
    stem = core_st.stem
    goto_bin = tmpdir / f"{stem}.gb"
    rc, stdout, stderr = run_cmd([
        SYMTAB2GB_BIN, str(symtab), "--goto-functions", str(goto_json),
        "--out", str(goto_bin)
    ], timeout=60)
    if rc != 0:
        result.add_backend("cbmc", "FAIL", f"symtab2gb: {stderr.strip()[:60]}")
        return

    # Step 4: Run CBMC. `--function main` is required because Strata-emitted
    # `main` has parameters that don't match cbmc's standard C entrypoint
    # signatures; without it cbmc rejects the binary as "no entry point" and
    # exits with rc=6 rather than the rc=0/10 PASS/FAIL contract used below.
    rc, stdout, stderr = run_cmd([
        CBMC_BIN, "--function", "main", str(goto_bin)
    ], timeout=120)
    if rc == 0:
        result.add_backend("cbmc", "PASS", "All properties hold")
    elif rc == 10:
        result.add_backend("cbmc", "FAIL", "Property violations found")
    elif rc == -1:
        result.add_backend("cbmc", "TIMEOUT", "")
    else:
        result.add_backend("cbmc", "FAIL", f"CBMC exit code {rc}")


def run_pipeline(bpl_path: Path, backends: list[str], split_procs: bool = False) -> PipelineResult:
    name = bpl_path.stem
    result = PipelineResult(name)

    with tempfile.TemporaryDirectory(prefix=f"strata_{name}_") as tmpdir:
        tmpdir = Path(tmpdir)
        # Translation steps (strip -> BoogieToStrata -> fix)
        fixed_st = run_translation(bpl_path, tmpdir, result)
        if fixed_st is None:
            return result

        # Run each backend
        for backend in backends:
            if backend == "deductive":
                if split_procs:
                    run_strata_split_procs(fixed_st, "deductive", result)
                else:
                    run_strata_backend(fixed_st, "deductive", result)
            elif backend == "bugFinding":
                if split_procs:
                    run_strata_split_procs(fixed_st, "bugFinding", result)
                else:
                    run_strata_backend(fixed_st, "bugFinding", result)
            elif backend == "cbmc":
                run_cbmc_backend(fixed_st, tmpdir, result)

    return result


def print_results(results: list[PipelineResult], backends: list[str]):
    name_w = max(len(r.name) for r in results)
    trans_steps = ["Strip", "B2S", "Fix"]

    # Header
    print()
    header = f"{'Program':<{name_w}}  "
    for s in trans_steps:
        header += f"| {s:>6} "
    for b in backends:
        header += f"| {b:>12} "
    header += "| Detail"
    print(header)
    print("-" * len(header))

    for r in results:
        line = f"{r.name:<{name_w}}  "
        step_map = {s: (st, d) for s, st, d in r.translation_steps}
        detail = ""

        for sn_full, sn_short in [("Strip prelude", "Strip"), ("BoogieToStrata", "B2S"), ("fix_core_st", "Fix")]:
            if sn_full in step_map:
                status, d = step_map[sn_full]
                cell = status if status in ("OK",) else status
                if status == "FAIL" and not detail:
                    detail = d
            else:
                cell = "—"
            line += f"| {cell:>6} "

        for b in backends:
            if b in r.backend_results:
                status, d = r.backend_results[b]
                cell = status
                if status in ("PASS", "OK") and d:
                    cell = f"{status}"
                if status in ("FAIL", "PARTIAL", "SKIP") and not detail:
                    detail = d
            else:
                cell = "—"
            line += f"| {cell:>12} "

        line += f"| {detail}"
        print(line)

    print()

    # Summary per backend
    for b in backends:
        passed = sum(1 for r in results if r.backend_results.get(b, ("", ""))[0] in ("PASS", "OK"))
        failed = sum(1 for r in results if r.backend_results.get(b, ("", ""))[0] in ("FAIL", "PARTIAL"))
        skipped = sum(1 for r in results if r.backend_results.get(b, ("", ""))[0] in ("SKIP", "WARN", "TIMEOUT"))
        not_reached = sum(1 for r in results if b not in r.backend_results)
        print(f"  {b:>12}: {passed} pass, {failed} fail, {skipped} skip, {not_reached} not reached")
    print()


def main():
    parser = argparse.ArgumentParser(description="Run SMACK -> BoogieToStrata -> verify pipeline")
    parser.add_argument("files", nargs="*", help="Input .bpl files (default: programs/*.bpl)")
    parser.add_argument("--backends", default="deductive,bugFinding,cbmc",
                        help="Comma-separated backends: deductive,bugFinding,cbmc (default: all)")
    parser.add_argument("--split-procs", action="store_true",
                        help="For deductive/bugFinding, run `strata verify --procedures <p>` once per procedure "
                             "and aggregate. Sidesteps cross-procedure Env.error contamination.")
    args = parser.parse_args()

    backends = [b.strip() for b in args.backends.split(",")]
    valid = {"deductive", "bugFinding", "cbmc"}
    for b in backends:
        if b not in valid:
            print(f"Unknown backend: {b}. Valid: {', '.join(valid)}", file=sys.stderr)
            sys.exit(1)

    if args.files:
        bpl_files = [Path(f) for f in args.files]
    else:
        programs_dir = SCRIPT_DIR / "programs"
        bpl_files = sorted(programs_dir.glob("*.bpl"))

    if not bpl_files:
        print("No .bpl files found.", file=sys.stderr)
        sys.exit(1)

    # Check prerequisites
    if DOTNET is None:
        print("Warning: dotnet not found.", file=sys.stderr)
    if not STRATA_BIN.exists():
        print(f"Warning: strata not found at {STRATA_BIN}", file=sys.stderr)
    if "cbmc" in backends:
        if not STRATA_CORE_TO_GOTO.exists():
            print(f"Warning: StrataCoreToGoto not found at {STRATA_CORE_TO_GOTO}", file=sys.stderr)
        if CBMC_BIN is None:
            print("Note: cbmc not found; CBMC backend will generate GOTO JSON only.", file=sys.stderr)

    mode_note = " [split-procs]" if args.split_procs else ""
    print(f"Running pipeline on {len(bpl_files)} programs, backends: {', '.join(backends)}{mode_note}")
    print()

    results = []
    for bpl in bpl_files:
        print(f"  {bpl.name}...", end="", flush=True)
        r = run_pipeline(bpl, backends, split_procs=args.split_procs)
        results.append(r)
        statuses = []
        for b in backends:
            if b in r.backend_results:
                statuses.append(f"{b}={r.backend_results[b][0]}")
        trans_ok = all(s == "OK" for _, s, _ in r.translation_steps)
        if not trans_ok:
            last_fail = [(s, d) for s, st, d in r.translation_steps if st != "OK"]
            print(f" FAIL ({last_fail[-1][0]})" if last_fail else " FAIL")
        else:
            print(f" {', '.join(statuses)}")

    print_results(results, backends)


if __name__ == "__main__":
    main()
