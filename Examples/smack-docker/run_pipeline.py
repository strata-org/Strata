#!/usr/bin/env python3
"""Run the SMACK → BoogieToStrata → Strata verify pipeline on .bpl files.

Usage:
    python3 run_pipeline.py [programs/*.bpl ...]

If no arguments given, runs on all .bpl files in the programs/ directory.

Requires:
    - dotnet SDK (default: ~/.dotnet/dotnet)
    - BoogieToStrata built (Tools/BoogieToStrata/Source/BoogieToStrata.csproj)
    - strata binary (.lake/build/bin/strata)
    - strip_smack_prelude.py and fix_core_st.py in the same directory as this script
"""

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
STRATA_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "strata"
BOOGIE_TO_STRATA_PROJ = REPO_ROOT / "Tools" / "BoogieToStrata" / "Source" / "BoogieToStrata.csproj"
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
        self.steps: list[tuple[str, str, str]] = []  # (step_name, status, detail)

    def add(self, step: str, status: str, detail: str = ""):
        self.steps.append((step, status, detail))

    @property
    def final_status(self) -> str:
        for _, status, _ in reversed(self.steps):
            if status != "OK":
                return status
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


def run_pipeline(bpl_path: Path) -> PipelineResult:
    name = bpl_path.stem
    result = PipelineResult(name)

    with tempfile.TemporaryDirectory(prefix=f"strata_{name}_") as tmpdir:
        stripped = Path(tmpdir) / f"{name}_stripped.bpl"
        core_st = Path(tmpdir) / f"{name}.core.st"
        fixed_st = Path(tmpdir) / f"{name}_fixed.core.st"

        # Step 1: Strip SMACK prelude
        rc, stdout, stderr = run_cmd(
            [sys.executable, str(STRIP_SCRIPT), str(bpl_path), str(stripped)]
        )
        if rc != 0:
            result.add("Strip prelude", "FAIL", stderr.strip())
            return result
        # Extract count from stderr
        m = re.search(r"Stripped (\d+) prelude", stderr)
        detail = m.group(0) if m else "OK"
        result.add("Strip prelude", "OK", detail)

        # Step 2: BoogieToStrata translation
        if DOTNET is None:
            result.add("BoogieToStrata", "FAIL", "dotnet not found")
            return result

        rc, stdout, stderr = run_cmd(
            [DOTNET, "run", "--project", str(BOOGIE_TO_STRATA_PROJ), "--", str(stripped)],
            cwd=str(BOOGIE_TO_STRATA_PROJ.parent.parent),
            timeout=120,
        )
        if rc != 0:
            # Extract the meaningful error
            err = stderr.strip()
            if "Failed translation:" in err:
                msg = err.split("Failed translation:")[-1].strip()
                # Remove temp path prefix, keep just filename and error
                msg = re.sub(r'.*/([^/]+\.bpl)', r'\1', msg)
                err = msg
            elif "Failed to typecheck" in err:
                err = err.split("\n")[-1].strip()
            elif "Failed to parse" in err:
                err = "Parse error"
            result.add("BoogieToStrata", "FAIL", err)
            return result

        core_st.write_text(stdout)
        lines = stdout.count("\n")
        result.add("BoogieToStrata", "OK", f"{lines} lines")

        # Step 3: Fix .core.st (forward refs + param shadowing)
        rc, stdout, stderr = run_cmd(
            [sys.executable, str(FIX_SCRIPT), str(core_st), str(fixed_st)]
        )
        if rc != 0:
            result.add("fix_core_st", "FAIL", stderr.strip())
            return result
        result.add("fix_core_st", "OK", "")

        # Step 4: Strata verify
        if not STRATA_BIN.exists():
            result.add("strata verify", "FAIL", f"Binary not found: {STRATA_BIN}")
            return result

        rc, stdout, stderr = run_cmd(
            [str(STRATA_BIN), "verify", str(fixed_st)], timeout=120
        )

        # Parse output
        output = stdout + stderr
        if "All 0 goals passed" in output:
            result.add("strata verify", "WARN", "0 VCs (assert not recognized)")
        elif re.search(r"All \d+ goals passed", output):
            m = re.search(r"All (\d+) goals passed", output)
            result.add("strata verify", "PASS", f"{m.group(1)} VCs passed")
        elif "a declaration of this name already exists" in output:
            result.add("strata verify", "FAIL", "Namespace collision (const vs procedure)")
        elif "unexpected type" in output:
            m = re.search(r'name := "(\w+)"', output)
            op = m.group(1) if m else "unknown"
            result.add("strata verify", "FAIL", f"Type synonym panic on '{op}' operator")
        elif "goals passed" in output and "failed" in output:
            m = re.search(r"(\d+) goals passed, (\d+) failed", output)
            if m:
                result.add("strata verify", "PARTIAL", f"{m.group(1)} pass, {m.group(2)} fail")
            else:
                result.add("strata verify", "FAIL", output.split("\n")[-2] if output.strip() else "Unknown")
        elif rc != 0:
            # Extract first meaningful error line
            for line in output.split("\n"):
                if "error:" in line.lower() or "Error" in line or "PANIC" in line:
                    result.add("strata verify", "FAIL", line.strip()[:80])
                    return result
            result.add("strata verify", "FAIL", f"Exit code {rc}")
        else:
            result.add("strata verify", "FAIL", "Unknown output")

    return result


def print_results(results: list[PipelineResult]):
    # Compute column widths
    name_w = max(len(r.name) for r in results)
    step_names = ["Strip prelude", "BoogieToStrata", "fix_core_st", "strata verify"]

    # Header
    print()
    print(f"{'Program':<{name_w}}  ", end="")
    for s in step_names:
        print(f"{'│ ' + s + ' ':>18}", end="")
    print("│ Failure reason")
    print("─" * name_w + "──" + ("─" * 18 + "┼") * len(step_names) + "─" * 40)

    for r in results:
        print(f"{r.name:<{name_w}}  ", end="")
        step_map = {s: (status, detail) for s, status, detail in r.steps}
        failure_reason = ""

        for sn in step_names:
            if sn in step_map:
                status, detail = step_map[sn]
                if status == "OK":
                    cell = "OK"
                elif status == "PASS":
                    cell = f"PASS ({detail})"
                elif status == "WARN":
                    cell = "WARN"
                elif status == "PARTIAL":
                    cell = "PARTIAL"
                else:
                    cell = "FAIL"
                    if not failure_reason:
                        failure_reason = detail
            else:
                cell = "—"
            print(f"│ {cell:>15} ", end="")

        print(f"│ {failure_reason}")

    print()

    # Summary
    passed = sum(1 for r in results if r.final_status in ("OK", "PASS"))
    warned = sum(1 for r in results if r.final_status == "WARN")
    failed = sum(1 for r in results if r.final_status in ("FAIL", "PARTIAL"))
    print(f"Summary: {passed} passed, {warned} warnings (0 VCs), {failed} failed out of {len(results)} programs")
    print()

    # Failure breakdown
    if failed or warned:
        reasons: dict[str, int] = {}
        for r in results:
            for _, status, detail in r.steps:
                if status in ("FAIL", "WARN"):
                    # Normalize to category
                    if "Namespace collision" in detail:
                        key = "Namespace collision (const vs procedure)"
                    elif "goto with two targets" in detail:
                        key = "Multi-target goto (unstructured CFG)"
                    elif "Irreducible" in detail:
                        key = "Irreducible control flow"
                    elif "Type synonym panic" in detail:
                        key = "Type synonym panic (comparison on ref type)"
                    elif "0 VCs" in detail:
                        key = "0 VCs generated (SMACK assert encoding)"
                    else:
                        key = detail[:70] if detail else "Unknown"
                    reasons[key] = reasons.get(key, 0) + 1
                    break
        print("Failure breakdown:")
        for reason, count in sorted(reasons.items(), key=lambda x: -x[1]):
            print(f"  {count}x  {reason}")
        print()


def main():
    if len(sys.argv) > 1:
        bpl_files = [Path(f) for f in sys.argv[1:]]
    else:
        programs_dir = SCRIPT_DIR / "programs"
        bpl_files = sorted(programs_dir.glob("*.bpl"))

    if not bpl_files:
        print("No .bpl files found.", file=sys.stderr)
        sys.exit(1)

    # Check prerequisites
    if DOTNET is None:
        print("Warning: dotnet not found. BoogieToStrata step will fail.", file=sys.stderr)
    if not STRATA_BIN.exists():
        print(f"Warning: strata binary not found at {STRATA_BIN}", file=sys.stderr)
    if not BOOGIE_TO_STRATA_PROJ.exists():
        print(f"Warning: BoogieToStrata project not found at {BOOGIE_TO_STRATA_PROJ}", file=sys.stderr)

    print(f"Running pipeline on {len(bpl_files)} .bpl files...")
    print()

    results = []
    for bpl in bpl_files:
        print(f"  Processing {bpl.name}...", end="", flush=True)
        r = run_pipeline(bpl)
        results.append(r)
        print(f" {r.final_status}")

    print_results(results)


if __name__ == "__main__":
    main()
