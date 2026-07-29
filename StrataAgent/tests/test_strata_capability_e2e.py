"""End-to-end capability tests: drive the StrataSwarm dashboard HEADLESS over the
sorry-stubbed theorems in ``tests/Lean/StrataCapabilityTests``, ONE THEOREM AT A
TIME, and assert the swarm actually proves each (no sorry, no bad axioms).

Theorems run in INCREASING order of complexity (see ``CAPABILITY_FILES_ORDERED``):
trivial single-goal arithmetic VCs first, then a single structural induction,
then helper-gated multi-target files (which exercise the multi-theorem /
transitive-sorry oracle), and finally the hard Strata transform theorems. So the
cheap, likely-to-pass proofs run first and a failure high in the list surfaces
before hours are spent on the domain theorems.

The two `module`-system files are placed at their true complexity rank, NOT
lumped together: ``VCModuleArith`` (a single ``omega`` proof) is the very first
target, so the cheapest run already exercises the module axiom-oracle path (the
recent fix — success confirmable only by the out-of-module ``#print axioms``
probe on ``public`` decls); ``VCModuleMultiSorry`` (helper-gated induction inside
a module) sits with the other multi-target files, since it is strictly harder
than the single-goal proofs above it.

Several files are NTP4VC-inspired VCs (github.com/xqyww123/NTP4VC) ported to core
Lean 4 (no Mathlib) — verification conditions stated in the benchmark's style.

How it works, per theorem:
  1. Clear the Sandbox (fresh proof workspace).
  2. Launch ``./start_dashboard.sh --prompt "prove <thm> in <file>"`` in the
     background. That script handles everything: start dashboard, load + start
     the LeanSwarm config, and deliver the prompt to the TaskManager.
  3. Poll the proof artifact (``Sandbox/Stub.lean``) using the SAME build-then-
     #print-axioms oracle TaskManager's watchdog uses, until the target theorem
     is verified sorry-free — or the per-theorem timeout elapses.
  4. Kill the dashboard (``./kill_dashboard.sh``) and clear the Sandbox.
  5. Move on to the next theorem.

This is a REAL LLM run: each proof can take 90 minutes or more, so the whole
suite is VERY long-running. Run it explicitly:

    # every theorem in every capability file
    StrataAgent/.venv/bin/python StrataAgent/tests/test_strata_capability_e2e.py

    # a subset (match by file stem or "file::theorem")
    StrataAgent/.venv/bin/python StrataAgent/tests/test_strata_capability_e2e.py StrataAgentTest1
    StrataAgent/.venv/bin/python StrataAgent/tests/test_strata_capability_e2e.py \
        StrataAgentTestMultiSorry::fast_exponentiation_same_as_slow

Environment knobs:
    STRATA_E2E_PORT         dashboard port (default 8421 — start_dashboard.sh's default)
    STRATA_E2E_TIMEOUT      per-theorem proof timeout in seconds (default 7200 = 2h)
    STRATA_E2E_CHEAT_SHEET  path to a cheat sheet to enable, repo-relative
                            (default: StrataAgent/strataswarm/agent_specs/StrataProofCheatSheet.md;
                            set to "" to run without one)
    STRATA_E2E_POLL         artifact poll interval in seconds (default 30)
"""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import time
from pathlib import Path

# ── Paths ──────────────────────────────────────────────────────────────────────
# tests/ -> StrataAgent/ -> repo root
STRATA_AGENT = Path(__file__).resolve().parent.parent
REPO_ROOT = STRATA_AGENT.parent
START_DASHBOARD = STRATA_AGENT / "start_dashboard.sh"
KILL_DASHBOARD = STRATA_AGENT / "kill_dashboard.sh"
CAP_TESTS_DIR = STRATA_AGENT / "tests" / "Lean" / "StrataCapabilityTests"
SANDBOX_DIR = STRATA_AGENT / "Sandbox"
# The single file the prover writes into (TaskManager copies the target here at SETUP).
STUB_REL = "StrataAgent/Sandbox/Stub.lean"

# Make `strataswarm` importable so we can use the same Lean oracle the swarm uses.
sys.path.insert(0, str(STRATA_AGENT))

# ── Config ───────────────────────────────────────────────────────────────────
PORT = int(os.environ.get("STRATA_E2E_PORT", "8421"))
PROOF_TIMEOUT = float(os.environ.get("STRATA_E2E_TIMEOUT", str(2 * 3600)))
POLL_INTERVAL = float(os.environ.get("STRATA_E2E_POLL", "30"))
# Default to the Strata proof cheat sheet (repo-relative, as start_dashboard.sh
# expects). Override with STRATA_E2E_CHEAT_SHEET="" to run without one.
CHEAT_SHEET = os.environ.get(
    "STRATA_E2E_CHEAT_SHEET",
    "StrataAgent/strataswarm/agent_specs/StrataProofCheatSheet.md",
)

# Capability files under tests/Lean/StrataCapabilityTests, ORDERED BY INCREASING
# COMPLEXITY. The harness runs them (and the theorems within each) top-to-bottom,
# so the cheapest/most-likely-to-pass proofs run first and expensive domain
# theorems (which can take 90 min+) run last. Each tuple is (filename, tier-note).
CAPABILITY_FILES_ORDERED: list[tuple[str, str]] = [
    # Tier 1 — trivial single-goal proofs (omega/decide/simp). The cheapest work.
    # VCModuleArith is FIRST because it is both the simplest proof AND a `module`-
    # system smoke test: its target keeps the `module` header when copied into
    # Sandbox/Stub.lean, so success can ONLY be confirmed by the out-of-module
    # `#print axioms` probe (in-module `#print axioms` is a hard Lean error) and
    # the decl is `public`. So the very first proof already exercises the module
    # oracle path — if that regressed, the run fails immediately and cheaply.
    ("VCModuleArith.lean", "module: proven-in-a-module (add_comm VC), omega"),
    ("VCEasyArith.lean", "easy arithmetic VCs (omega/decide)"),
    # Tier 1.5 — single-goal but needs Nat division/modulus lemmas (omega alone
    # won't close carry/borrow bounds), so a notch above pure-omega arith.
    ("VCMultiprecision.lean", "multiprecision limb carry/borrow VCs (Nat div/mod)"),
    # Tier 2 — single structural induction (omega alone won't close them).
    ("VCListInduction.lean", "list induction VCs"),
    # Tier 2.5 — tree structural induction (two IHs per node), a step up from list.
    ("VCTreeInduction.lean", "binary-tree size/height/mirror VCs"),
    # Tier 3 — multi-target files: a helper lemma gates the main VC, exercising the
    # multi-theorem / transitive-sorry oracle. VCModuleMultiSorry is the `module`
    # variant of this tier (helper-gated multi-target INSIDE a module, so the
    # transitive-sorry axiom gate runs through the out-of-module probe) and sits
    # here — not at the top — because it needs an accumulator-generalization
    # induction, strictly harder than the Tier-1/2 single-goal proofs.
    ("VCModuleMultiSorry.lean", "module: multi-target factorial (helper-gated induction)"),
    ("VCFactGcdMultiSorry.lean", "fact loop-vs-spec + gcd (multi-target, helper)"),
    ("StrataAgentTestMultiSorry.lean", "fast/slow exponentiation (nonlinear induction)"),
    # Tier 4 — Strata transform theorems (domain-specific, hard).
    ("StrataAgentTest1.lean", "wrapCmdInBlock overapproximates"),
    ("StrataAgentTest2.lean", "wrapStmtInBlock overapproximates"),
    # Tier 5 — hardest known target (forward-simulation; never proved in prior runs).
    ("StrataAgentTestStub.lean", "detToKleene overapproximates"),
]

# Flat list of filenames in complexity order (used for discovery / selection).
CAPABILITY_FILES = [f for f, _ in CAPABILITY_FILES_ORDERED]


# ── Lean oracle (the authoritative success check) ────────────────────────────
def discover_sorry_theorems(source_file: Path) -> list[str]:
    """Names of the sorry-stubbed theorems in a capability source file."""
    from strataswarm.modules.po_lean import get_lean_tools

    rel = os.path.relpath(source_file, REPO_ROOT)
    result = get_lean_tools().list_theorems(rel)
    if result.error:
        raise RuntimeError(f"list_theorems({rel}) failed: {result.error}")
    return [t.name for t in result.theorems if t.status == "sorry"]


def theorem_proven(name: str) -> tuple[bool, str]:
    """Run the build-then-#print-axioms oracle on Sandbox/Stub.lean for one theorem.

    Returns (proven, detail). proven is True only if the module builds AND the
    named theorem is verified sorry-free (transitively).
    """
    from strataswarm.modules.po_lean import get_lean_tools

    if not (REPO_ROOT / STUB_REL).exists():
        return False, "Stub.lean not yet created"
    result = get_lean_tools().axioms_by_theorem(STUB_REL, [name])
    if not result.build_ok:
        return False, f"build failed: {result.build_error or result.error}"
    proven = result.is_proven(name)
    return proven, f"{name}={'proven' if proven else 'sorry'}"


# ── Sandbox / dashboard lifecycle ────────────────────────────────────────────
def clear_sandbox() -> None:
    """Remove all proof artifacts from Sandbox/ but keep .gitkeep."""
    if not SANDBOX_DIR.exists():
        SANDBOX_DIR.mkdir(parents=True)
        return
    for entry in SANDBOX_DIR.iterdir():
        if entry.name == ".gitkeep":
            continue
        if entry.is_dir():
            import shutil

            shutil.rmtree(entry, ignore_errors=True)
        else:
            entry.unlink(missing_ok=True)


def kill_dashboard() -> None:
    subprocess.run(
        ["bash", str(KILL_DASHBOARD), str(PORT)],
        capture_output=True,
        text=True,
    )


def launch_dashboard(prompt: str) -> subprocess.Popen:
    """Launch start_dashboard.sh --prompt in its own process group (it runs in
    the foreground / blocks, so we background it and poll separately)."""
    args = ["bash", str(START_DASHBOARD), "--port", str(PORT), "--prompt", prompt]
    if CHEAT_SHEET:
        args += ["--cheat-sheet", CHEAT_SHEET]
    print(f"[E2E] Launching: {' '.join(args[:5])} --prompt <...>")
    return subprocess.Popen(
        args,
        cwd=str(STRATA_AGENT),
        start_new_session=True,  # own process group → clean tree kill
    )


def stop_dashboard(proc: subprocess.Popen) -> None:
    """Kill the dashboard tree (via kill_dashboard.sh) and the wrapper script."""
    kill_dashboard()
    if proc.poll() is None:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        except (ProcessLookupError, PermissionError):
            pass
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass


# ── One proof run ────────────────────────────────────────────────────────────
def _build_prompt(source_rel: str, theorem: str) -> str:
    return (
        f"Please prove the theorem `{theorem}` in the file {source_rel}. "
        f"It is currently stubbed with `sorry`. Prove it completely so the file "
        f"builds with no `sorry` remaining in that theorem."
    )


def run_one_theorem(source: Path, theorem: str, timeout: float = PROOF_TIMEOUT) -> bool:
    """Clear Sandbox, drive the dashboard on a single theorem, poll to completion,
    then tear down. Returns True on a verified sorry-free proof."""
    source_rel = os.path.relpath(source, REPO_ROOT)
    print("\n" + "=" * 72)
    print(f"[E2E] Proving  {source.name} :: {theorem}")
    print("=" * 72)

    clear_sandbox()
    kill_dashboard()  # ensure no stale dashboard on the port
    started = time.time()
    proc = launch_dashboard(_build_prompt(source_rel, theorem))
    try:
        deadline = time.time() + timeout
        last_detail = ""
        while time.time() < deadline:
            proven, detail = theorem_proven(theorem)
            if detail != last_detail:
                print(f"[E2E] [{int(time.time() - started):>6}s] {detail}")
                last_detail = detail
            if proven:
                print(f"[E2E] ✓ PROVEN in {int(time.time() - started)}s — {theorem}")
                return True
            # If the wrapper died, do a final check and stop waiting.
            if proc.poll() is not None:
                print(f"[E2E] dashboard wrapper exited (code {proc.returncode}); final check ...")
                proven, detail = theorem_proven(theorem)
                print(f"[E2E] final: {detail}")
                return proven
            time.sleep(POLL_INTERVAL)

        print(f"[E2E] ✗ TIMEOUT after {int(timeout)}s — {theorem} (last: {last_detail})")
        return False
    finally:
        stop_dashboard(proc)
        clear_sandbox()


# ── Selection ────────────────────────────────────────────────────────────────
def _collect_targets(selectors: list[str]) -> list[tuple[Path, str]]:
    """Expand selectors into (source_file, theorem_name) pairs, ALWAYS ordered by
    increasing complexity (the ``CAPABILITY_FILES_ORDERED`` rank).

    A selector is either a file stem/name ("StrataAgentTest1") — expands to every
    sorry-theorem in that file — or "stem::theorem" for a single theorem.
    No selectors → every theorem in every capability file.

    The final list is sorted by each file's complexity rank so a selected SUBSET
    still runs cheapest-first regardless of the order the selectors were passed on
    the command line (e.g. ``... StrataAgentTest2 VCEasyArith`` runs VCEasyArith
    first). The sort is stable, so theorems within a file keep their source order.
    """
    # File complexity rank = position in CAPABILITY_FILES (already ordered).
    rank = {f: i for i, f in enumerate(CAPABILITY_FILES)}

    targets: list[tuple[Path, str]] = []
    if not selectors:
        selectors = [f[:-5] for f in CAPABILITY_FILES]

    for sel in selectors:
        stem, _, thm = sel.partition("::")
        stem = stem.removesuffix(".lean")
        matches = [f for f in CAPABILITY_FILES if f[:-5] == stem]
        if not matches:
            print(f"[E2E] WARNING: no capability file matches '{stem}' — skipping.")
            continue
        source = CAP_TESTS_DIR / matches[0]
        if thm:
            targets.append((source, thm))
        else:
            for name in discover_sorry_theorems(source):
                targets.append((source, name))

    # Stable sort by file complexity rank: reorders across files (cheapest-first)
    # while preserving each file's within-file theorem order.
    targets.sort(key=lambda t: rank.get(t[0].name, len(rank)))
    return targets


# ── Entry point ──────────────────────────────────────────────────────────────
def main(argv: list[str]) -> int:
    targets = _collect_targets(argv)
    if not targets:
        print("[E2E] No targets to run.")
        print(f"Available files: {', '.join(f[:-5] for f in CAPABILITY_FILES)}")
        return 2

    print(f"[E2E] {len(targets)} theorem(s) queued, one at a time:")
    for source, thm in targets:
        print(f"        {source.name} :: {thm}")

    results: list[tuple[str, str, bool]] = []
    for source, thm in targets:
        try:
            ok = run_one_theorem(source, thm)
        except KeyboardInterrupt:
            print("\n[E2E] Interrupted — tearing down and stopping.")
            kill_dashboard()
            raise
        except Exception as e:  # noqa: BLE001 — report per-theorem, keep going
            print(f"[E2E] ERROR on {source.name}::{thm}: {e}")
            ok = False
        results.append((source.name, thm, ok))

    print("\n" + "=" * 72)
    print("[E2E] Summary")
    print("=" * 72)
    for fname, thm, ok in results:
        print(f"  {'PASS' if ok else 'FAIL'}  {fname} :: {thm}")
    passed = sum(1 for _, _, ok in results if ok)
    print(f"\n{passed}/{len(results)} theorems proven.")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
