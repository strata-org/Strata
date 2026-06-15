"""Test: write_helper_lemma tool — transactional sorry replacement.

Tests that:
1. Successful case: helper created, sorry replaced, both compile
2. Helper doesn't compile → reverts everything
3. Replacement tactic doesn't type-check → reverts everything
4. Sorry not found at specified line → rejected
5. Axiom in helper → rejected
6. Line numbers stay valid (import added AFTER replacement)

Test files are created in StrataAgent/tests/Lean/ and cleaned up after each test.
"""

import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import argparse
import shutil
from pathlib import Path

from strataswarm.modules.po_lean import SwarmLeanTools


PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent  # Strata/
# Workspace must be inside StrataAgent/ for Lean to resolve imports
WORK_DIR = PROJECT_ROOT / "StrataAgent" / "Sandbox" / "TestWs"
# Inspection/log artifacts go here
LOG_DIR = Path(__file__).resolve().parent / "Lean"

# Flags (set via command line)
PRESERVE_FILES = False


def setup_workspace() -> tuple[str, str]:
    """Create a minimal workspace in StrataAgent/Sandbox/TestWs/ for testing.
    This path is within the lakefile's StrataAgent.+ glob so Lean can resolve it.
    Returns (workspace_rel, stub_rel) relative to PROJECT_ROOT."""
    # Clean any leftover
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)

    workspace = str(WORK_DIR.relative_to(PROJECT_ROOT))

    # Stub.lean — self-contained theorem with two sorries (no imports needed)
    (WORK_DIR / "Stub.lean").write_text(
        "-- Test file for write_helper_lemma\n"
        "\n"
        "theorem main_thm (x : Nat) (h : x > 0) : x ≠ 0 ∧ x ≥ 1 := by\n"
        "  constructor\n"
        "  · sorry\n"
        "  · sorry\n"
    )

    stub_rel = f"{workspace}/Stub.lean"
    return workspace, stub_rel


def cleanup(test_name: str = ""):
    """Remove test workspace. If --preserve, copy to tests/Lean/<test_name>/ for inspection."""
    if PRESERVE_FILES and WORK_DIR.exists():
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        inspect_dir = LOG_DIR / (test_name or "last_run")
        if inspect_dir.exists():
            shutil.rmtree(inspect_dir)
        shutil.copytree(WORK_DIR, inspect_dir)
        log(f"  [preserve] Files at: {inspect_dir}")
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)


def log(msg: str):
    """Write to log file + print."""
    print(msg)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with open(LOG_DIR / "test_log.txt", "a") as f:
        f.write(msg + "\n")


def log_tool_call(name: str, tool_input: dict, result):
    """Pretty-print a tool call's input and output."""
    import json
    log(f"  ┌─ {name} INPUT:")
    log(json.dumps(tool_input, indent=4))
    tool_output = {
        "error": result.error,
        "file_path": result.file_path,
        "theorem_name": result.theorem_name,
        "has_sorry": result.has_sorry,
    }
    log(f"  └─ {name} OUTPUT:")
    log(json.dumps(tool_output, indent=4))


def test_successful_replacement():
    """Helper compiles, replacement type-checks → success."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_successful_replacement]")
        log(f"  Workspace: {workspace}")
        log(f"  Target: {stub_rel}")
        log(f"  Original Stub.lean:")
        log((WORK_DIR / "Stub.lean").read_text())

        tool_input = {
            "theorem_name": "helper_ne_zero",
            "theorem_statement": "theorem helper_ne_zero (x : Nat) (h : x > 0) : x ≠ 0 := by omega",
            "additional_imports": [],
            "sorry_line": 4,
            "sorry_col": 4,
            "replacement_tactic": "exact helper_ne_zero x h",
            "target_file": stub_rel,
            "workspace": workspace,
        }
        result = tools.write_helper_lemma(**tool_input)
        log_tool_call("write_helper_lemma", tool_input, result)
        assert result.error is None, f"Expected success, got: {result.error}"
        assert result.file_path is not None
        assert "lemma_helper_helper_ne_zero" in result.file_path

        # Verify target was modified
        content = (WORK_DIR / "Stub.lean").read_text()
        log(f"  Modified Stub.lean:")
        log(content)

        assert "exact helper_ne_zero x h" in content, "Replacement not found"
        assert "lemma_helper_helper_ne_zero" in content, "Import not added"

        # Verify first sorry replaced, second still there
        assert content.count("sorry") == 1, f"Expected 1 sorry remaining, got {content.count('sorry')}"

        # Verify helper file exists and show contents
        helper_path = WORK_DIR / "decomposed" / "lemma_helper_helper_ne_zero.lean"
        assert helper_path.exists(), "Helper file not created"
        log(f"  Helper file ({helper_path.name}):")
        log(helper_path.read_text())

        # Show decomposed/ listing
        decomposed = WORK_DIR / "decomposed"
        if decomposed.exists():
            log(f"  decomposed/ contents: {[f.name for f in decomposed.iterdir()]}")

        log("  ✅ test_successful_replacement")
    finally:
        tools.close()
        cleanup("successful_replacement")


def test_helper_doesnt_compile():
    """Helper with type error → everything reverted."""
    workspace, stub_rel = setup_workspace()
    original_content = (WORK_DIR / "Stub.lean").read_text()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_helper_doesnt_compile]")
        tool_input = {
            "theorem_name": "bad_helper",
            "theorem_statement": "theorem bad_helper : UndefinedType := by sorry",
            "additional_imports": [],
            "sorry_line": 4,
            "sorry_col": 4,
            "replacement_tactic": "exact bad_helper",
            "target_file": stub_rel,
            "workspace": workspace,
        }
        result = tools.write_helper_lemma(**tool_input)
        log_tool_call("write_helper_lemma", tool_input, result)
        assert result.error is not None, "Expected error"
        assert "compile" in result.error.lower() or "not" in result.error.lower()

        # Verify target unchanged
        assert (WORK_DIR / "Stub.lean").read_text() == original_content, "Target was modified!"

        # Verify no helper file left
        helper_path = WORK_DIR / "decomposed" / "lemma_helper_bad_helper.lean"
        assert not helper_path.exists(), "Helper file should not exist"

        print("  ✅ test_helper_doesnt_compile")
    finally:
        tools.close()
        cleanup("helper_doesnt_compile")


def test_replacement_doesnt_typecheck():
    """Helper compiles but replacement tactic doesn't match goal → reverts."""
    workspace, stub_rel = setup_workspace()
    original_content = (WORK_DIR / "Stub.lean").read_text()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_replacement_doesnt_typecheck]")
        tool_input = {
            "theorem_name": "wrong_type",
            "theorem_statement": "theorem wrong_type : Bool := true",
            "additional_imports": [],
            "sorry_line": 4,
            "sorry_col": 4,
            "replacement_tactic": "exact wrong_type",
            "target_file": stub_rel,
            "workspace": workspace,
        }
        result = tools.write_helper_lemma(**tool_input)
        log_tool_call("write_helper_lemma", tool_input, result)
        assert result.error is not None, "Expected error"

        # Verify target unchanged
        assert (WORK_DIR / "Stub.lean").read_text() == original_content, "Target was modified!"

        # Verify helper cleaned up
        helper_path = WORK_DIR / "decomposed" / "lemma_helper_wrong_type.lean"
        assert not helper_path.exists(), "Helper should be cleaned up"

        print("  ✅ test_replacement_doesnt_typecheck")
    finally:
        tools.close()
        cleanup("sorry_not_found")


def test_sorry_not_found():
    """Wrong line number → error."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_sorry_not_found]")
        tool_input = {
            "theorem_name": "helper_x",
            "theorem_statement": "theorem helper_x (x : Nat) (h : x > 0) : x ≠ 0 := by omega",
            "additional_imports": [],
            "sorry_line": 1,
            "sorry_col": 0,
            "replacement_tactic": "exact helper_x x h",
            "target_file": stub_rel,
            "workspace": workspace,
        }
        result = tools.write_helper_lemma(**tool_input)
        log_tool_call("write_helper_lemma", tool_input, result)
        assert result.error is not None, "Expected error"
        assert "sorry" in result.error.lower()

        print("  ✅ test_sorry_not_found")
    finally:
        tools.close()
        cleanup("axiom_rejected")


def test_axiom_rejected():
    """Helper with axiom keyword → rejected."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_axiom_rejected]")
        tool_input = {
            "theorem_name": "bad_axiom",
            "theorem_statement": "axiom bad_axiom : False",
            "additional_imports": [],
            "sorry_line": 4,
            "sorry_col": 4,
            "replacement_tactic": "exact bad_axiom.elim",
            "target_file": stub_rel,
            "workspace": workspace,
        }
        result = tools.write_helper_lemma(**tool_input)
        log_tool_call("write_helper_lemma", tool_input, result)
        assert result.error is not None, "Expected error"
        assert "axiom" in result.error.lower()

        print("  ✅ test_axiom_rejected")
    finally:
        tools.close()
        cleanup("axiom_rejected")


def test_show_file_state():
    """show_file_state returns correct summary."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_show_file_state]")
        import json

        state = tools.show_file_state(stub_rel)
        log(f"  show_file_state({stub_rel}):")
        log(json.dumps(state, indent=4))

        assert state["compiles"] is True, f"Expected compiles=True, got {state['compiles']}"
        assert state["sorry_count"] == 2, f"Expected 2 sorries, got {state['sorry_count']}"
        assert state["main_theorem"] == "main_thm", f"Expected main_thm, got {state['main_theorem']}"
        assert state["main_theorem_sorry_free"] is False
        assert len(state["theorems"]) == 1
        assert state["theorems"][0]["name"] == "main_thm"
        assert state["theorems"][0]["status"] == "sorry"

        log("  ✅ test_show_file_state")
    finally:
        tools.close()
        cleanup("show_file_state")


def test_get_sorry_positions():
    """get_sorry_positions returns correct (line, col) for each sorry."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_get_sorry_positions]")
        import json

        positions = tools.get_sorry_positions(stub_rel)
        log(f"  get_sorry_positions({stub_rel}):")
        log(json.dumps(positions, indent=4))

        # File content (0-indexed):
        # 0: -- Test file for write_helper_lemma
        # 1: (empty)
        # 2: theorem main_thm (x : Nat) (h : x > 0) : x ≠ 0 ∧ x ≥ 1 := by
        # 3:   constructor
        # 4:   · sorry
        # 5:   · sorry
        assert len(positions) == 2, f"Expected 2 positions, got {len(positions)}"
        assert positions[0]["line"] == 4, f"Expected line 4, got {positions[0]['line']}"
        assert positions[1]["line"] == 5, f"Expected line 5, got {positions[1]['line']}"

        # Show the actual file for reference
        log(f"  File content (for reference):")
        content = (WORK_DIR / "Stub.lean").read_text()
        for i, line in enumerate(content.splitlines()):
            log(f"    {i}: {line}")

        log("  ✅ test_get_sorry_positions")
    finally:
        tools.close()
        cleanup("get_sorry_positions")


def test_get_sorry_positions_ignores_comments():
    """Sorry in comments should NOT be reported."""
    workspace, stub_rel = setup_workspace()
    # Add a comment with sorry
    content = (WORK_DIR / "Stub.lean").read_text()
    content = "-- This is sorry in a comment\n/- sorry in block comment -/\n" + content
    (WORK_DIR / "Stub.lean").write_text(content)

    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_get_sorry_positions_ignores_comments]")
        import json

        positions = tools.get_sorry_positions(stub_rel)
        log(f"  get_sorry_positions (with comments):")
        log(json.dumps(positions, indent=4))

        # Only the 2 real sorries should be found (not the ones in comments)
        assert len(positions) == 2, f"Expected 2 positions (comments ignored), got {len(positions)}"

        log(f"  File content:")
        for i, line in enumerate((WORK_DIR / "Stub.lean").read_text().splitlines()):
            log(f"    {i}: {line}")

        log("  ✅ test_get_sorry_positions_ignores_comments")
    finally:
        tools.close()
        cleanup("sorry_positions_comments")


def test_show_file_state_after_helper():
    """After write_helper_lemma, show_file_state reflects the change."""
    workspace, stub_rel = setup_workspace()
    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_show_file_state_after_helper]")
        import json

        # First: write a helper
        result = tools.write_helper_lemma(
            theorem_name="helper_ne_zero",
            theorem_statement="theorem helper_ne_zero (x : Nat) (h : x > 0) : x ≠ 0 := by omega",
            additional_imports=[],
            sorry_line=4,
            sorry_col=4,
            replacement_tactic="exact helper_ne_zero x h",
            target_file=stub_rel,
            workspace=workspace,
        )
        log(f"  write_helper_lemma result: error={result.error}")
        assert result.error is None, f"Helper failed: {result.error}"

        # Now check state
        state = tools.show_file_state(stub_rel)
        log(f"  show_file_state after helper:")
        log(json.dumps(state, indent=4))

        assert state["sorry_count"] == 1, f"Expected 1 sorry, got {state['sorry_count']}"
        assert state["compiles"] is True

        # Check sorry positions — should be 1 now
        positions = tools.get_sorry_positions(stub_rel)
        log(f"  get_sorry_positions after helper:")
        log(json.dumps(positions, indent=4))
        assert len(positions) == 1, f"Expected 1 sorry position, got {len(positions)}"

        log("  ✅ test_show_file_state_after_helper")
    finally:
        tools.close()
        cleanup("file_state_after_helper")


def test_get_sorries_by_theorem():
    """get_sorries_by_theorem groups positions by theorem name."""
    workspace, stub_rel = setup_workspace()
    # Add a helper theorem with sorry above main
    content = (WORK_DIR / "Stub.lean").read_text()
    content = (
        "-- Test file\n"
        "\n"
        "theorem helper_A : Nat := by sorry\n"
        "\n"
        "theorem helper_B (n : Nat) : n = n := by sorry\n"
        "\n"
        "theorem main_thm (x : Nat) (h : x > 0) : x ≠ 0 ∧ x ≥ 1 := by\n"
        "  constructor\n"
        "  · sorry\n"
        "  · sorry\n"
    )
    (WORK_DIR / "Stub.lean").write_text(content)

    tools = SwarmLeanTools()
    try:
        log(f"\n  [test_get_sorries_by_theorem]")
        import json

        # All theorems
        result = tools.get_sorries_by_theorem(stub_rel)
        log(f"  get_sorries_by_theorem (all):")
        log(json.dumps(result, indent=4))

        assert "helper_A" in result, "helper_A should have sorry"
        assert "helper_B" in result, "helper_B should have sorry"
        assert "main_thm" in result, "main_thm should have sorry"
        assert len(result["main_thm"]) == 2, "main_thm should have 2 sorries"
        assert len(result["helper_A"]) == 1
        assert len(result["helper_B"]) == 1

        # Filtered
        filtered = tools.get_sorries_by_theorem(stub_rel, filter_names=["main_thm"])
        log(f"  get_sorries_by_theorem (filter=['main_thm']):")
        log(json.dumps(filtered, indent=4))

        assert "main_thm" in filtered
        assert "helper_A" not in filtered
        assert "helper_B" not in filtered

        log(f"  File content:")
        for i, line in enumerate((WORK_DIR / "Stub.lean").read_text().splitlines()):
            log(f"    {i}: {line}")

        log("  ✅ test_get_sorries_by_theorem")
    finally:
        tools.close()
        cleanup("sorries_by_theorem")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--preserve", action="store_true",
                        help="Keep generated Lean files in Sandbox/TestWs/ for inspection")
    args = parser.parse_args()
    PRESERVE_FILES = args.preserve

    # Clear log
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    (LOG_DIR / "test_log.txt").write_text("")

    log("=" * 60)
    log("TEST: write_helper_lemma tool")
    log("=" * 60)
    if PRESERVE_FILES:
        log("  [--preserve] Generated files will be kept for inspection")
        log(f"  Workspace: {WORK_DIR}")
    log("")

    tests = [
        ("successful_replacement", test_successful_replacement),
        ("helper_doesnt_compile", test_helper_doesnt_compile),
        ("replacement_doesnt_typecheck", test_replacement_doesnt_typecheck),
        ("sorry_not_found", test_sorry_not_found),
        ("axiom_rejected", test_axiom_rejected),
        ("show_file_state", test_show_file_state),
        ("get_sorry_positions", test_get_sorry_positions),
        ("get_sorry_positions_ignores_comments", test_get_sorry_positions_ignores_comments),
        ("show_file_state_after_helper", test_show_file_state_after_helper),
        ("get_sorries_by_theorem", test_get_sorries_by_theorem),
    ]

    passed = 0
    for name, fn in tests:
        try:
            fn()
            passed += 1
        except Exception as e:
            log(f"  ❌ {name}: {e}")
            cleanup(name)

    log(f"\n  {passed}/{len(tests)} passed")
    log(f"  Log: {LOG_DIR / 'test_log.txt'}")
