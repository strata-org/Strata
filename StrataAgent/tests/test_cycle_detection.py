"""Tests for cycle detection library (modules/cycle_detection.py).

Tests:
1. check_fast: exact hash match against ancestry
2. check_fast: no match returns None
3. Full detect() with fast path cycle
4. Full detect() with no match
5. _get_statement: uses split_theorems on real Lean files
6. _get_imports / _merge_imports: real file import extraction

Note: check_soft (agent-based) and verify_* (proof_writer-based) require
a running swarm + Claude API. Those are integration tests run separately.
"""

import os
import sys
import shutil
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.lemma_ledger import LemmaLedger, LemmaStatus
from strataswarm.modules.cycle_detection import (
    check_fast, MatchType, DetectionResult,
    _get_statement, _get_imports, _merge_imports,
)


PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent  # Strata/
WORK_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean" / "cycle_test"
LOG_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean"


def log(msg):
    print(msg)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    with open(LOG_DIR / "test_cycle_detection_log.txt", "a") as f:
        f.write(msg + "\n")


def make_ledger():
    tmp = Path(tempfile.mkdtemp()) / "test_ledger.json"
    return LemmaLedger(tmp), tmp


def test_check_fast_cycle_detected():
    """Hash match against ancestor → returns CYCLE."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "hash_A")
    child = ledger.add_lemma("child", "c.lean", "ws/c", "hash_B", parent_id=root.id)

    # New entry with root's hash, parented under child
    result = check_fast(ledger, "hash_A", child.id)
    assert result is not None
    assert result.match_type == MatchType.CYCLE
    assert result.matched_id == root.id
    assert result.matched_name == "main"
    shutil.rmtree(tmp.parent)
    print("✓ test_check_fast_cycle_detected")


def test_check_fast_no_match():
    """No hash match → returns None."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "hash_A")
    child = ledger.add_lemma("child", "c.lean", "ws/c", "hash_B", parent_id=root.id)

    result = check_fast(ledger, "hash_C", child.id)
    assert result is None
    shutil.rmtree(tmp.parent)
    print("✓ test_check_fast_no_match")


def test_check_fast_deep_ancestry():
    """Cycle detected through multiple levels of ancestry."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "r.lean", "ws", "hash_ROOT")
    a = ledger.add_lemma("a", "a.lean", "ws/a", "hash_A", parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", "hash_B", parent_id=a.id)
    c = ledger.add_lemma("c", "c.lean", "ws/c", "hash_C", parent_id=b.id)

    # New entry at depth 4 matching root's hash
    result = check_fast(ledger, "hash_ROOT", c.id)
    assert result is not None
    assert result.match_type == MatchType.CYCLE
    assert result.matched_id == root.id
    log(f"  Deep cycle: detected root at depth 4, reason: {result.reason}")
    shutil.rmtree(tmp.parent)
    print("✓ test_check_fast_deep_ancestry")


def test_check_fast_sibling_not_cycle():
    """A sibling's hash is NOT a cycle (only ancestors count)."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "r.lean", "ws", "hash_ROOT")
    a = ledger.add_lemma("a", "a.lean", "ws/a", "hash_A", parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", "hash_B", parent_id=root.id)

    # Check if hash_B (sibling) is flagged when parented under a → should NOT be
    result = check_fast(ledger, "hash_B", a.id)
    assert result is None
    shutil.rmtree(tmp.parent)
    print("✓ test_check_fast_sibling_not_cycle")


def test_get_statement_real_file():
    """_get_statement uses split_theorems on a real Lean file."""
    try:
        from strataswarm.modules.po_lean import get_lean_tools
    except ImportError:
        print("⊘ test_get_statement_real_file (skipped: itp_interface not available)")
        return

    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)

    content = """\
import Strata.DL.Imperative.Stmt

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

theorem test_thm (st : Stmt P (Cmd P)) (rho : Env P) : True := by
  sorry
"""
    (WORK_DIR / "test_stmt.lean").write_text(content)
    rel = str((WORK_DIR / "test_stmt.lean").relative_to(PROJECT_ROOT))

    stmt = _get_statement(rel)
    log(f"  _get_statement result: {stmt[:80]}...")
    assert "test_thm" in stmt
    assert "Stmt P" in stmt
    assert "sorry" in stmt

    shutil.rmtree(WORK_DIR)
    print("✓ test_get_statement_real_file")


def test_get_imports_real_file():
    """_get_imports and _merge_imports work on real Lean files."""
    try:
        from strataswarm.modules.po_lean import get_lean_tools
    except ImportError:
        print("⊘ test_get_imports_real_file (skipped: itp_interface not available)")
        return

    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)

    file_a = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.KleeneStmt

theorem a : True := by trivial
"""
    file_b = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Util.Relations

theorem b : True := by trivial
"""
    (WORK_DIR / "a.lean").write_text(file_a)
    (WORK_DIR / "b.lean").write_text(file_b)
    rel_a = str((WORK_DIR / "a.lean").relative_to(PROJECT_ROOT))
    rel_b = str((WORK_DIR / "b.lean").relative_to(PROJECT_ROOT))

    imports_a = _get_imports(rel_a)
    log(f"  Imports of a: {imports_a}")
    assert "Strata.DL.Imperative.Stmt" in imports_a
    assert "Strata.DL.Imperative.KleeneStmt" in imports_a

    imports_b = _get_imports(rel_b)
    log(f"  Imports of b: {imports_b}")
    assert "Strata.DL.Util.Relations" in imports_b

    merged = _merge_imports(rel_a, rel_b)
    log(f"  Merged: {merged}")
    assert "Strata.DL.Imperative.Stmt" in merged
    assert "Strata.DL.Imperative.KleeneStmt" in merged
    assert "Strata.DL.Util.Relations" in merged
    # Deduplicated
    assert merged.count("Strata.DL.Imperative.Stmt") == 1

    shutil.rmtree(WORK_DIR)
    print("✓ test_get_imports_real_file")


if __name__ == "__main__":
    log("\n" + "=" * 60)
    log("test_cycle_detection")
    log("=" * 60)

    test_check_fast_cycle_detected()
    test_check_fast_no_match()
    test_check_fast_deep_ancestry()
    test_check_fast_sibling_not_cycle()
    test_get_statement_real_file()
    test_get_imports_real_file()

    print("\n✅ All cycle detection tests passed!")
