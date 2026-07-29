"""End-to-end tests for the transitive-sorry axiom oracle on `module` files.

These are the regression tests for the bug that motivated the whole oracle
rewrite (see the run analyses): in Lean's `module` system, `#print axioms` is
ILLEGAL *inside* a module, so the old in-place oracle (and external `lean_verify`)
could never confirm — or refute — anything in this repo's Sandbox files. Worse, a
"looks-clean" file could hide a `sorry` reached through an imported helper (the
"shell-game" false-success). The rewritten oracle builds the module to a fresh
olean and probes `#print axioms` from a throwaway NON-module scratch file, making
the axiom set transitive.

Each test drives the REAL oracle (`SwarmLeanTools.axioms_by_theorem`, which
`verify_no_sorry` wraps) against a `module` fixture whose expected verdict is
known, so we exercise the exact behaviors we now guard against:

  1. proven-in-a-module          → is_proven=True   (old oracle: could never confirm)
  2. direct sorry-in-a-module    → is_proven=False, sorryAx present
  3. TRANSITIVE sorry via import → is_proven=False  (no literal `sorry` in the file —
                                    the case text/grep checks miss; the shell-game)
  4. build failure               → build_ok=False, confirms NOTHING
  5. multi-name aggregation      → mirrors verify_no_sorry's all_proven

Plus the `check_compiles` substring-swallow regression (Bug: a real error whose
message text contains the substring "sorry" was classified as a benign
sorry-warning → false success).

The fixtures are written ON THE FLY into a temp dir under the `StrataAgent.+`
lean_lib glob (so `lake build <module>` resolves them by name), then removed on
teardown — mirroring `test_cycle_detection.py`. Nothing is committed: the broken
fixtures (real type errors) never linger in the source tree to trip a build.

Requires a working `lake` + the built SwarmAgentTools (real Lean builds; each
fixture is tiny, so the whole file runs in well under a minute). Run:

    StrataAgent/.venv/bin/python StrataAgent/tests/test_module_sorry_oracle.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_lean import get_lean_tools

# tests/ -> StrataAgent/ -> repo root (where lakefile.toml lives)
STRATA_AGENT = Path(__file__).resolve().parent.parent
REPO_ROOT = STRATA_AGENT.parent

# Fixtures are generated on the fly into a temp dir under the StrataAgent.+
# lean_lib glob so `lake build` can resolve them by module name. The dir is
# created in setup() and removed in teardown() — nothing is checked in.
WORK_DIR = STRATA_AGENT / "tests" / "Lean" / "oracle_fixtures_tmp"
FIX_DIR_REL = "StrataAgent/tests/Lean/oracle_fixtures_tmp"
FIX_MOD_PREFIX = "StrataAgent.tests.Lean.oracle_fixtures_tmp"

# The fixture set: filename stem → source. `module` files need `public` decls to
# expose them to the out-of-module import probe (`public section` would need a
# Lean import to enable the modifier, so we mark each decl `public` directly).
FIXTURES: dict[str, str] = {
    "Proven": (
        "module\n\n"
        "/-- A genuinely-proven theorem in a `module` file. The OLD oracle broke here:\n"
        "    in-place `#print axioms` is illegal in a module, so it could never confirm\n"
        "    even a real proof. `public` exposes the decl for the transitive import probe. -/\n"
        "public theorem oracle_fixture_proven (a b : Nat) : a + b = b + a := by\n"
        "  omega\n"
    ),
    "DirectSorry": (
        "module\n\n"
        "/-- Direct `sorry` inside a `module`. The oracle must report has_sorry / not-proven\n"
        "    (the `#print axioms` verdict contains `sorryAx`). -/\n"
        "public theorem oracle_fixture_direct_sorry (a b : Nat) : a + b = b + a := by\n"
        "  sorry\n"
    ),
    "SorryHelper": (
        "module\n\n"
        "/-- Helper carrying a hidden `sorry`. Imported transitively by TransitiveSorry. -/\n"
        "public theorem oracle_fixture_helper (n : Nat) : n + 0 = n := by\n"
        "  sorry\n"
    ),
    "TransitiveSorry": (
        "module\n\n"
        f"import {FIX_MOD_PREFIX}.SorryHelper\n\n"
        "/-- No literal `sorry` in THIS file's proof — it closes via the imported helper.\n"
        "    A text/grep check would call this \"clean\"; the transitive #print-axioms oracle\n"
        "    must still see `sorryAx` through the import and report not-proven. -/\n"
        "public theorem oracle_fixture_transitive_sorry (n : Nat) : n + 0 = n := by\n"
        "  exact oracle_fixture_helper n\n"
    ),
    "BuildError": (
        "module\n\n"
        "/-- A genuine type error (not a sorry). The oracle must return build_ok=False and\n"
        "    confirm nothing — \"couldn't check\" must never be conflated with \"proven\". -/\n"
        "public theorem oracle_fixture_build_error (a b : Nat) : a + b = b + a := by\n"
        "  exact \"this is not a proof\"\n"
    ),
    "ErrorMentionsSorry": (
        "module\n\n"
        "/-- A genuine compile error (unknown identifier) whose error message text happens\n"
        "    to contain the substring \"sorry\". The buggy classifier swallowed any error\n"
        "    line containing \"sorry\" as a benign sorry-warning → reported false success.\n"
        "    The fix keys on the exact `declaration uses 'sorry'` diagnostic instead. -/\n"
        "public theorem oracle_fixture_error_mentions_sorry (n : Nat) : n = n := by\n"
        "  exact my_sorry_lemma n\n"
    ),
}


def _rel(name: str) -> str:
    """Repo-relative path to a fixture file, as the oracle expects."""
    return f"{FIX_DIR_REL}/{name}.lean"


def setup() -> None:
    """Create the temp fixture dir and write every fixture to disk."""
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)
    for name, src in FIXTURES.items():
        (WORK_DIR / f"{name}.lean").write_text(src, encoding="utf-8")


def teardown() -> None:
    """Remove the temp fixture dir (and any olean build products under it)."""
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR, ignore_errors=True)


# ── 1. A real proof in a module is CONFIRMED (the core regression) ────────────
def test_proven_in_module():
    """The old in-place `#print axioms` errored inside a `module`, so a genuine
    proof could never be confirmed. The rewritten oracle must return proven."""
    t = get_lean_tools()
    r = t.axioms_by_theorem(_rel("Proven"), ["oracle_fixture_proven"])
    assert r.build_ok, f"expected build_ok, got build_error={r.build_error}"
    assert r.is_proven("oracle_fixture_proven"), "genuine proof in a module not confirmed"
    assert r.sorry_by_name.get("oracle_fixture_proven") is False
    assert "sorryAx" not in r.axioms_by_name.get("oracle_fixture_proven", [])
    print("✓ test_proven_in_module")


# ── 2. A direct sorry in a module is REFUTED ──────────────────────────────────
def test_direct_sorry_in_module():
    t = get_lean_tools()
    r = t.axioms_by_theorem(_rel("DirectSorry"), ["oracle_fixture_direct_sorry"])
    assert r.build_ok, f"fixture should build (sorry is a warning): {r.build_error}"
    assert not r.is_proven("oracle_fixture_direct_sorry"), "direct sorry wrongly confirmed"
    assert r.sorry_by_name.get("oracle_fixture_direct_sorry") is True
    assert "sorryAx" in r.axioms_by_name.get("oracle_fixture_direct_sorry", [])
    print("✓ test_direct_sorry_in_module")


# ── 3. A sorry reached THROUGH AN IMPORT is refuted (the shell-game) ──────────
def test_transitive_sorry_through_import():
    """TransitiveSorry.lean has NO literal `sorry` in its own proof — it closes via
    an imported helper that does. A text/grep check calls this clean; the
    transitive #print-axioms oracle must still see sorryAx and refute it. This is
    the exact false-success ("shell game") the oracle was built to stop."""
    t = get_lean_tools()
    name = "oracle_fixture_transitive_sorry"
    r = t.axioms_by_theorem(_rel("TransitiveSorry"), [name])
    assert r.build_ok, f"fixture should build: {r.build_error}"
    assert not r.is_proven(name), "TRANSITIVE sorry (via import) wrongly confirmed as proven"
    assert r.sorry_by_name.get(name) is True, "transitive sorryAx not detected through import"
    assert "sorryAx" in r.axioms_by_name.get(name, [])

    # Sanity: the file itself contains no literal `sorry` token — proving that the
    # verdict came from the transitive axiom set, not a text match.
    src = (REPO_ROOT / _rel("TransitiveSorry")).read_text()
    proof_body = src.split(":= by", 1)[-1]
    assert "sorry" not in proof_body, "fixture invalidated: it now has a literal sorry"
    print("✓ test_transitive_sorry_through_import")


# ── 4. A build failure confirms NOTHING (couldn't-check != proven) ────────────
def test_build_failure_confirms_nothing():
    t = get_lean_tools()
    name = "oracle_fixture_build_error"
    r = t.axioms_by_theorem(_rel("BuildError"), [name])
    assert not r.build_ok, "a real compile error must set build_ok=False"
    assert r.build_error, "build_error detail should be populated"
    assert not r.is_proven(name), "a non-building theorem must never be 'proven'"
    print("✓ test_build_failure_confirms_nothing")


# ── 5. Multi-name aggregation mirrors verify_no_sorry.all_proven ──────────────
def test_multi_name_all_proven_aggregation():
    """verify_no_sorry reports all_proven = build_ok AND every name proven. Confirm
    that a mix of proven + sorry names aggregates to not-all-proven, and that a
    single-proven name aggregates to all-proven."""
    t = get_lean_tools()

    # Proven alone → all proven.
    r1 = t.axioms_by_theorem(_rel("Proven"), ["oracle_fixture_proven"])
    all_proven_1 = r1.build_ok and all(r1.is_proven(n) for n in ["oracle_fixture_proven"])
    assert all_proven_1 is True

    # Helper (sorry) alone → not all proven.
    r2 = t.axioms_by_theorem(_rel("SorryHelper"), ["oracle_fixture_helper"])
    all_proven_2 = r2.build_ok and all(r2.is_proven(n) for n in ["oracle_fixture_helper"])
    assert all_proven_2 is False
    print("✓ test_multi_name_all_proven_aggregation")


# ── 6. Unknown theorem name → found=False, not proven ─────────────────────────
def test_unknown_name_not_proven():
    t = get_lean_tools()
    name = "oracle_fixture_does_not_exist"
    r = t.axioms_by_theorem(_rel("Proven"), [name])
    # Build succeeds (Proven.lean is fine) but the name has no verdict.
    assert r.ok_by_name.get(name, False) is False, "unknown name should have no verdict"
    assert not r.is_proven(name), "unknown name must never be 'proven'"
    print("✓ test_unknown_name_not_proven")


# ── 7. check_compiles: a real error mentioning 'sorry' is NOT swallowed ───────
def test_check_compiles_does_not_swallow_error_mentioning_sorry():
    """Regression for the substring bug: the classifier used to treat any error
    line containing the substring "sorry" as a benign sorry-warning. This fixture
    is a genuine `Unknown identifier` error whose message contains "sorry" — it
    must be reported as a real error, not a false success."""
    t = get_lean_tools()
    r = t.check_compiles(_rel("ErrorMentionsSorry"))
    assert r.success is False, "real error mentioning 'sorry' was swallowed as success"
    assert r.has_error is True
    print("✓ test_check_compiles_does_not_swallow_error_mentioning_sorry")


# ── 8. check_compiles: a clean proof compiles cleanly ─────────────────────────
def test_check_compiles_clean_proof():
    t = get_lean_tools()
    r = t.check_compiles(_rel("Proven"))
    assert r.success is True, f"clean proof should compile: {r.error}"
    assert r.has_error is False
    print("✓ test_check_compiles_clean_proof")


# ── 9. Declaration parsers see `public` module decls (target-discovery) ───────
def test_list_theorems_finds_public_module_decls():
    """The Lean-side declaration parsers (list_theorems / count_sorries /
    split_theorems in LeanTools/Main.lean) key on the bare `theorem `/`def `
    keyword. In a `module` file every decl is `public theorem …`, so before the
    `stripPublic` fix these parsers returned NOTHING for module files — which
    silently breaks E2E target discovery (`discover_sorry_theorems` enumerates
    exactly these). This guards that a `public theorem` in a module is found and
    reported as a sorry."""
    t = get_lean_tools()

    # Proven.lean: one public theorem, no sorry → discovered, status 'proved'.
    lt = t.list_theorems(_rel("Proven"))
    assert lt.error is None, f"list_theorems errored: {lt.error}"
    names = {x.name: x.status for x in lt.theorems}
    assert "oracle_fixture_proven" in names, (
        f"public module theorem not discovered — got {names}")
    assert names["oracle_fixture_proven"] == "proved"

    # DirectSorry.lean: one public theorem WITH sorry → discovered, status 'sorry'.
    lt2 = t.list_theorems(_rel("DirectSorry"))
    names2 = {x.name: x.status for x in lt2.theorems}
    assert names2.get("oracle_fixture_direct_sorry") == "sorry", (
        f"public module sorry-theorem not discovered as sorry — got {names2}")
    print("✓ test_list_theorems_finds_public_module_decls")


# ── 10. The ANCHOR: in-module `#print axioms` really is illegal ───────────────
def test_in_module_print_axioms_is_illegal():
    """Reproduce the OLD broken oracle: append `#print axioms` INSIDE the module
    file and build it. Lean rejects it ("cannot use `#print axioms` in a
    `module`"). This is the entire reason the oracle probes from a separate
    non-module scratch file. If this ever starts passing, Lean changed the rule
    and the out-of-module dance may no longer be necessary — but until then, any
    revert to in-place probing is provably broken. We build a throwaway sibling
    module inside the temp fixture dir."""
    probe_name = "InModulePrintAxioms"
    probe_path = WORK_DIR / f"{probe_name}.lean"
    probe_path.write_text(
        "module\n\n"
        "public theorem in_module_probe (a b : Nat) : a + b = b + a := by omega\n\n"
        "#print axioms in_module_probe\n",
        encoding="utf-8",
    )
    try:
        proc = subprocess.run(
            ["lake", "build", f"{FIX_MOD_PREFIX}.{probe_name}"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=300,
        )
        out = proc.stdout + "\n" + proc.stderr
        assert proc.returncode != 0, "in-module `#print axioms` unexpectedly built OK"
        assert "#print axioms" in out and "module" in out, (
            f"expected the in-module `#print axioms` rejection, got:\n{out[:500]}")
    finally:
        probe_path.unlink(missing_ok=True)
    print("✓ test_in_module_print_axioms_is_illegal")


if __name__ == "__main__":
    print("=" * 60)
    print("test_module_sorry_oracle (real Lean builds)")
    print("=" * 60)
    setup()
    try:
        test_proven_in_module()
        test_direct_sorry_in_module()
        test_transitive_sorry_through_import()
        test_build_failure_confirms_nothing()
        test_multi_name_all_proven_aggregation()
        test_unknown_name_not_proven()
        test_check_compiles_does_not_swallow_error_mentioning_sorry()
        test_check_compiles_clean_proof()
        test_list_theorems_finds_public_module_decls()
        test_in_module_print_axioms_is_illegal()
    finally:
        teardown()
    print("\n✅ All module-sorry-oracle tests passed!")
