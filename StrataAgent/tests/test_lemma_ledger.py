"""Tests for the Lemma Ledger (modules/lemma_ledger.py).

Tests:
1. add_lemma: root (no parent) and child (with parent)
2. Cycle detection: fast hash match against ancestors
3. add_parent: cross-branch sharing + cycle rejection
4. Priority ordering by indegree
5. Prune propagation to descendants
6. BM25 search over statements (name, types, params)
7. Search pagination and status filtering
8. DAG rendering (tree + mermaid)
9. Persistence round-trip
10. Integration with real Sandbox files (requires itp_interface)
"""

import os
import sys
import shutil
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from strataswarm.modules.lemma_ledger import LemmaLedger, LemmaStatus, SearchResult


def make_ledger():
    tmp = Path(tempfile.mkdtemp()) / "test_ledger.json"
    return LemmaLedger(tmp), tmp


def test_add_lemma_root():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main_thm", "Stub.lean", "ws", "hash_root",
                            statement="theorem main_thm (x : Nat) : x = x := by sorry")
    assert not isinstance(root, str)
    assert root.status == LemmaStatus.PROVING
    assert root.parent_id == ""
    assert root.depth == 0
    assert ledger.root_id == root.id
    shutil.rmtree(tmp.parent)
    print("✓ test_add_lemma_root")


def test_add_lemma_child():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    child = ledger.add_lemma("helper", "a.lean", "ws/a", "h_child",
                             statement="theorem helper (y : Nat) : y + 0 = y := by sorry",
                             parent_id=root.id)
    assert not isinstance(child, str)
    assert child.status == LemmaStatus.PENDING
    assert child.parent_id == root.id
    assert child.depth == 1
    assert child.id in ledger.get(root.id).children
    shutil.rmtree(tmp.parent)
    print("✓ test_add_lemma_child")


def test_cycle_detection_fast():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    child = ledger.add_lemma("helper", "a.lean", "ws/a", "h_child", parent_id=root.id)

    # Try to add grandchild with root's hash → cycle
    result = ledger.add_lemma("bad", "b.lean", "ws/b", "h_root", parent_id=child.id)
    assert isinstance(result, str) and "Cycle" in result

    # Direct parent match
    result2 = ledger.add_lemma("bad2", "c.lean", "ws/c", "h_child", parent_id=child.id)
    assert isinstance(result2, str) and "Cycle" in result2
    shutil.rmtree(tmp.parent)
    print("✓ test_cycle_detection_fast")


def test_add_parent_cross_branch():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    a = ledger.add_lemma("helper_a", "a.lean", "ws/a", "h_a", parent_id=root.id)
    b = ledger.add_lemma("helper_b", "b.lean", "ws/b", "h_b", parent_id=root.id)

    # b also depends on a
    err = ledger.add_parent(b.id, a.id)
    assert err is None
    assert ledger.indegree(a.id) == 2
    shutil.rmtree(tmp.parent)
    print("✓ test_add_parent_cross_branch")


def test_add_parent_rejects_cycle():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    a = ledger.add_lemma("a", "a.lean", "ws/a", "h_a", parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", "h_b", parent_id=a.id)

    # Can't make b a parent of a (a is ancestor of b)
    err = ledger.add_parent(b.id, a.id)
    assert err is not None and "Cycle" in err
    shutil.rmtree(tmp.parent)
    print("✓ test_add_parent_rejects_cycle")


def test_priority_by_indegree():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    a = ledger.add_lemma("a", "a.lean", "ws/a", "h_a",
                         statement="theorem a : Nat := by sorry", parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", "h_b",
                         statement="theorem b : Nat := by sorry", parent_id=root.id)
    c = ledger.add_lemma("c", "c.lean", "ws/c", "h_c",
                         statement="theorem c : Nat := by sorry", parent_id=root.id)

    # Give 'a' extra indegree
    ledger.add_parent(b.id, a.id)
    ledger.add_parent(c.id, a.id)
    assert ledger.indegree(a.id) == 3  # root + b + c depend on it

    winner = ledger.pick_next()
    assert winner.id == a.id
    assert winner.turn_budget == 25 + 3 * 5
    shutil.rmtree(tmp.parent)
    print("✓ test_priority_by_indegree")


def test_prune_cascades():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h_root")
    a = ledger.add_lemma("a", "a.lean", "ws/a", "h_a", parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", "h_b", parent_id=a.id)
    c = ledger.add_lemma("c", "c.lean", "ws/c", "h_c", parent_id=b.id)

    pruned = ledger.prune_branch(a.id, "contradictory")
    assert a.id in pruned
    assert b.id in pruned
    assert c.id in pruned
    assert ledger.get(a.id).status == LemmaStatus.PRUNED
    assert ledger.get(c.id).status == LemmaStatus.PRUNED
    shutil.rmtree(tmp.parent)
    print("✓ test_prune_cascades")


def test_search_bm25():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "s.lean", "ws", "h0")
    ledger.add_lemma("sim_canfail", "a.lean", "ws/a", "h1",
                     statement="theorem sim_canfail (extendEval : ExtendEval P) (st : Stmt P) (hFail : Transform.CanFail (Lang.det extendEval) st rho) : Transform.CanFail Lang.kleene st' rho := by sorry",
                     parent_id=root.id)
    ledger.add_lemma("sim_terminal", "b.lean", "ws/b", "h2",
                     statement="theorem sim_terminal (extendEval : ExtendEval P) (st : Stmt P) (hStar : StepStmtStar P extendEval (.stmt st rho) (.terminal rho')) : StepKleeneStar P (.stmt st' rho) (.terminal rho') := by sorry",
                     parent_id=root.id)
    ledger.add_lemma("eval_preserved", "c.lean", "ws/c", "h3",
                     statement="theorem eval_preserved (s : Stmt P) (rho rho1 : Env P) (hStar : StepStmtStar P extendEval (.stmt s rho) (.terminal rho1)) : rho1.eval = rho.eval := by sorry",
                     parent_id=root.id)

    r = ledger.search("CanFail Transform")
    assert r.hits[0].entry.name == "sim_canfail"

    r = ledger.search("StepKleeneStar terminal")
    assert r.hits[0].entry.name == "sim_terminal"

    r = ledger.search("eval preserved rho")
    assert r.hits[0].entry.name == "eval_preserved"
    shutil.rmtree(tmp.parent)
    print("✓ test_search_bm25")


def test_search_pagination():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "s.lean", "ws", "h0")
    for i in range(5):
        ledger.add_lemma(f"helper_{i}", f"{i}.lean", f"ws/{i}", f"h{i+1}",
                         statement=f"theorem helper_{i} (x : Stmt P) : x = x := by sorry",
                         parent_id=root.id)

    r = ledger.search("Stmt helper", page=0, page_size=2)
    assert len(r.hits) == 2
    assert r.has_next
    assert r.total == 5

    r2 = ledger.search("Stmt helper", page=2, page_size=2)
    assert len(r2.hits) == 1
    assert not r2.has_next
    shutil.rmtree(tmp.parent)
    print("✓ test_search_pagination")


def test_search_status_filter():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "s.lean", "ws", "h0")
    a = ledger.add_lemma("proved_one", "a.lean", "ws/a", "h1",
                         statement="theorem proved_one (x : Nat) : x = x := by sorry",
                         parent_id=root.id)
    ledger.add_lemma("pending_one", "b.lean", "ws/b", "h2",
                     statement="theorem pending_one (x : Nat) : x = x := by sorry",
                     parent_id=root.id)
    ledger.mark_proved(a.id, "ws.a.Stub")

    r = ledger.search("Nat", status_filter=[LemmaStatus.PROVED])
    assert all(h.entry.status == LemmaStatus.PROVED for h in r.hits)
    assert r.total == 1
    shutil.rmtree(tmp.parent)
    print("✓ test_search_status_filter")


def test_dag_rendering():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h0",
                            statement="theorem main : Prop := by sorry")
    a = ledger.add_lemma("child_a", "a.lean", "ws/a", "h1",
                         statement="theorem child_a : Nat := by sorry", parent_id=root.id)
    ledger.mark_proved(a.id, "ws.a")

    dag = ledger.render_dag()
    assert "main" in dag
    assert "✅" in dag
    assert "child_a" in dag

    mermaid = ledger.render_mermaid()
    assert "flowchart TD" in mermaid
    assert "main" in mermaid
    assert "child_a" in mermaid
    shutil.rmtree(tmp.parent)
    print("✓ test_dag_rendering")


def test_persistence():
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("main", "s.lean", "ws", "h0")
    a = ledger.add_lemma("helper", "a.lean", "ws/a", "h1", parent_id=root.id)
    b = ledger.add_lemma("helper2", "b.lean", "ws/b", "h2", parent_id=root.id)
    ledger.add_parent(b.id, a.id)
    ledger.mark_proved(a.id, "ws.a")
    ledger.prune_branch(b.id, "bad")
    ledger.save()

    # Reload
    ledger2 = LemmaLedger(tmp)
    assert ledger2.root_id == root.id
    assert ledger2.get(a.id).status == LemmaStatus.PROVED
    assert ledger2.get(b.id).status == LemmaStatus.PRUNED
    assert ledger2.indegree(a.id) == 2  # rebuilt from graph
    assert ledger2.get_ancestry(a.id) == [root.id]
    shutil.rmtree(tmp.parent)
    print("✓ test_persistence")


def test_integration_with_lean():
    """Full integration test: creates real .lean files, parses with itp_interface,
    registers in ledger, runs searches, tests cycle detection.

    Files are created in StrataAgent/tests/Lean/ledger_test/ and cleaned up.
    """
    try:
        from strataswarm.modules.po_lean import SwarmLeanTools
    except ImportError:
        print("⊘ test_integration_with_lean (skipped: itp_interface not available)")
        return

    PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent  # Strata/
    WORK_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean" / "ledger_test"
    LOG_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean"

    def log(msg):
        print(msg)
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        with open(LOG_DIR / "test_ledger_log.txt", "a") as f:
            f.write(msg + "\n")

    # Setup
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)
    (WORK_DIR / "decomposed").mkdir()

    log("\n" + "=" * 60)
    log("test_integration_with_lean")
    log("=" * 60)

    # Create test Lean files
    stub_content = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.KleeneStmt

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

theorem simForward
    (st : Stmt P (Cmd P)) (st' : KleeneStmt P (Cmd P))
    (hT : StmtToKleeneStmt st = some st')
    (ρ : Env P) :
    True := by
  trivial
"""
    helper_a_content = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.KleeneStmt

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

theorem sim_stmt_terminal
    (st : Stmt P (Cmd P)) (st' : KleeneStmt P (Cmd P))
    (hT : StmtToKleeneStmt st = some st')
    (ρ₀ ρ' : Env P) :
    True := by
  sorry
"""
    helper_b_content = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.KleeneStmt

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

theorem sim_canfail
    (st : Stmt P (Cmd P)) (st' : KleeneStmt P (Cmd P))
    (hT : StmtToKleeneStmt st = some st')
    (ρ₀ : Env P) :
    True := by
  sorry
"""
    helper_c_content = """\
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.KleeneStmt

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

theorem eval_preserved
    (st : Stmt P (Cmd P))
    (ρ₀ ρ₁ : Env P) :
    True := by
  sorry
"""

    (WORK_DIR / "Stub.lean").write_text(stub_content)
    (WORK_DIR / "decomposed" / "lemma_helper_sim_terminal.lean").write_text(helper_a_content)
    (WORK_DIR / "decomposed" / "lemma_helper_sim_canfail.lean").write_text(helper_b_content)
    (WORK_DIR / "decomposed" / "lemma_helper_eval_preserved.lean").write_text(helper_c_content)

    log(f"  Created test files in: {WORK_DIR}")

    # Parse with real tools
    tools = SwarmLeanTools()
    workspace_rel = str(WORK_DIR.relative_to(PROJECT_ROOT))
    stub_rel = f"{workspace_rel}/Stub.lean"

    log(f"\n  Parsing {stub_rel}...")
    split = tools.split_theorems(stub_rel)
    assert split.blocks, f"No blocks found in {stub_rel}"
    root_block = split.blocks[0]
    log(f"  Root theorem: {root_block.name}")
    log(f"  Statement: {root_block.text[:100]}...")

    # Create ledger
    ledger_path = WORK_DIR / "lemma_ledger.json"
    ledger = LemmaLedger(ledger_path)

    # Register root
    root = ledger.add_lemma(
        name=root_block.name, file_path=stub_rel, workspace=workspace_rel,
        signature_hash=LemmaLedger.compute_signature_hash(root_block.text),
        statement=root_block.text,
    )
    assert not isinstance(root, str), f"Root registration failed: {root}"
    log(f"  Registered root: {root.name} (id={root.id[:8]})")

    # Register decomposed lemmas
    log(f"\n  Registering decomposed lemmas:")
    decomposed_dir = WORK_DIR / "decomposed"
    registered = []
    for f in sorted(decomposed_dir.glob("lemma_helper_*.lean")):
        rel = str(f.relative_to(PROJECT_ROOT))
        split = tools.split_theorems(rel)
        if not split.blocks:
            log(f"    SKIP (no blocks): {f.name}")
            continue
        block = split.blocks[0]
        sig_hash = LemmaLedger.compute_signature_hash(block.text)
        result = ledger.add_lemma(
            name=block.name, file_path=rel,
            workspace=str(f.parent.relative_to(PROJECT_ROOT)),
            signature_hash=sig_hash, statement=block.text,
            parent_id=root.id,
        )
        if isinstance(result, str):
            log(f"    CYCLE: {block.name} — {result}")
        else:
            registered.append(result)
            log(f"    Added: {result.name} (id={result.id[:8]}, hash={sig_hash[:8]})")

    assert len(registered) == 3, f"Expected 3 lemmas, got {len(registered)}"

    # Search tests with logging
    log(f"\n  === BM25 Search Results ===")

    queries = [
        "Stmt KleeneStmt StmtToKleeneStmt",
        "sim_canfail",
        "sim terminal",
        "eval preserved Env",
        "sorry",  # should not match (not in statements)
    ]
    for q in queries:
        r = ledger.search(q)
        log(f"\n  Query: \"{q}\" → {r.total} hits, {r.total_pages} pages")
        for i, h in enumerate(r.hits[:5]):
            log(f"    [{i+1}] score={h.score:.3f} | {h.entry.name} | {h.entry.status.value}")

    # Specific assertions
    r = ledger.search("sim_canfail")
    assert r.total >= 1 and r.hits[0].entry.name == "sim_canfail"

    r = ledger.search("terminal Stmt")
    assert r.total >= 1 and r.hits[0].entry.name == "sim_stmt_terminal"

    r = ledger.search("eval preserved")
    assert r.total >= 1 and r.hits[0].entry.name == "eval_preserved"

    # Pagination
    r = ledger.search("Stmt", page=0, page_size=2)
    assert len(r.hits) == 2 and r.has_next
    log(f"\n  Pagination: page=0, size=2 → {len(r.hits)} hits, has_next={r.has_next}")

    # Status filter
    ledger.mark_proved(registered[0].id, "test.import")
    r = ledger.search("Stmt", status_filter=[LemmaStatus.PROVED])
    log(f"  Filter proved: {r.total} hits")
    assert all(h.entry.status == LemmaStatus.PROVED for h in r.hits)

    # Cycle detection
    log(f"\n  === Cycle Detection ===")
    cycle_result = ledger.add_lemma(
        "fake_cycle", "x.lean", "ws",
        LemmaLedger.compute_signature_hash(root_block.text),
        parent_id=root.id,
    )
    assert isinstance(cycle_result, str) and "Cycle" in cycle_result
    log(f"  Adding lemma with root's hash → {cycle_result}")

    # DAG
    log(f"\n  === DAG ===")
    ledger.save()
    dag = ledger.render_dag()
    log(dag)
    mermaid = ledger.render_mermaid()
    log(mermaid)

    # Verify files were written
    assert ledger_path.exists()
    assert (WORK_DIR / "lemma_dag.md").exists()
    assert (WORK_DIR / "lemma_dag_mermaid.md").exists()
    log(f"  Ledger saved to: {ledger_path}")

    # Copy DAG visualizations to tests/Lean/ for inspection
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy2(WORK_DIR / "lemma_dag.md", LOG_DIR / "test_ledger_dag.md")
    shutil.copy2(WORK_DIR / "lemma_dag_mermaid.md", LOG_DIR / "test_ledger_dag_mermaid.md")
    log(f"  DAG files copied to: {LOG_DIR}/test_ledger_dag*.md")

    # Cleanup
    shutil.rmtree(WORK_DIR)
    log(f"\n  Cleaned up {WORK_DIR}")
    print(f"✓ test_integration_with_lean (3 lemmas, all searches pass)")


if __name__ == "__main__":
    test_add_lemma_root()
    test_add_lemma_child()
    test_cycle_detection_fast()
    test_add_parent_cross_branch()
    test_add_parent_rejects_cycle()
    test_priority_by_indegree()
    test_prune_cascades()
    test_search_bm25()
    test_search_pagination()
    test_search_status_filter()
    test_dag_rendering()
    test_persistence()
    test_integration_with_lean()
    print("\n✅ All tests passed!")
