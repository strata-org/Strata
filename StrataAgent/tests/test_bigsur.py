"""Deterministic tests for the BigSur repair agent (PO v5) — NO LLM, NO network.

BigSur is the repair agent of last resort: on EVERY give-up, the swarm escalates
to it, and it may rewrite any contract/decomposition/ledger/snapshot ANYWHERE in
the Sandbox except the root human signature (see `project_po_v5_bigsur`). Almost
all of its machinery is pure Python and testable without spawning a real agent;
only the actual repair reasoning needs a live LLM (that is Layer 3, driven
externally via env vars).

Layer 1 — deterministic units (no agent):
  * ledger `bigsur_*` mutators: delete (refuses root), purge subtree (keeps
    diamond-shared descendants, always deletes the named root), reparent
    (cycle-guarded), update_signature (recomputes hash + resets PENDING),
    reset_to_pending.
  * the destructive ledger MCP: a tool call reaches the live ledger.
  * the Sandbox-wide destructive snapshot MCP: list / read / delete / delete-all.
  * `_root_signature_hash`: detects a changed / absent Stub.clean.lean.

Layer 2 — orchestration with a scripted fake BigSur agent (no LLM):
  * `_propagate_failure_to_parent` ALWAYS escalates (no reactivation gate) and
    still records failure text + prunes the dead child's subtree first.
  * `_run_bigsur`: tamper guard (root reference changed → reject + fail root),
    epiphany give-up (→ user_fix_request + fail root), invocation cap (no spawn),
    decision-round exhaustion (proceeds), success (teardown + no root failure).

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_bigsur.py
"""

from __future__ import annotations

import asyncio
import os
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.lemma_ledger import LemmaLedger, LemmaStatus
from strataswarm._bigsur_ledger_mcp import create_bigsur_ledger_mcp_server
from strataswarm._bigsur_snapshot_mcp import create_bigsur_snapshot_mcp_server
from strataswarm.modules import po_v5
from strataswarm.modules.po_v5 import (
    PO5State, _root_signature_hash, _run_bigsur,
    _propagate_failure_to_parent, BIGSUR_MAX_INVOCATIONS, BIGSUR_DECISION_ROUNDS,
)


# ── Small helpers ─────────────────────────────────────────────────────────────

def make_ledger():
    tmp = Path(tempfile.mkdtemp()) / "test_ledger.json"
    return LemmaLedger(tmp), tmp


def _h(text: str) -> str:
    return LemmaLedger.compute_signature_hash(text)


def call_mcp_tool(server, name: str, args: dict) -> str:
    """Invoke an SDK-MCP tool through its low-level CallTool handler, returning the
    first text block. This exercises the SAME path the agent runtime uses."""
    from mcp.types import CallToolRequest, CallToolRequestParams
    srv = server["instance"]
    handler = srv.request_handlers[CallToolRequest]
    req = CallToolRequest(
        method="tools/call",
        params=CallToolRequestParams(name=name, arguments=args))
    res = asyncio.run(handler(req))
    return res.root.content[0].text


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 1a — ledger bigsur_* mutators (direct)
# ═══════════════════════════════════════════════════════════════════════════════

def _diamond():
    """root → a, b ; a → shared ; b → shared ; a → leaf. Returns (ledger, ids)."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "Stub.lean", "ws", _h("root"))
    a = ledger.add_lemma("a", "a.lean", "ws/a", _h("a"), parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", _h("b"), parent_id=root.id)
    shared = ledger.add_lemma("shared", "s.lean", "ws/s", _h("shared"), parent_id=a.id)
    leaf = ledger.add_lemma("leaf", "l.lean", "ws/l", _h("leaf"), parent_id=a.id)
    # Make `shared` a diamond node: also a child of b.
    assert ledger.add_parent(b.id, shared.id) is None
    ids = {"root": root.id, "a": a.id, "b": b.id, "shared": shared.id, "leaf": leaf.id}
    return ledger, tmp, ids


def test_delete_entry_refuses_root():
    ledger, tmp, ids = _diamond()
    msg = ledger.bigsur_delete_entry(ids["root"])
    assert msg.startswith("REFUSED")
    assert ledger.get(ids["root"]) is not None
    shutil.rmtree(tmp.parent)
    print("✓ test_delete_entry_refuses_root")


def test_delete_entry_unlinks_from_parents():
    ledger, tmp, ids = _diamond()
    ledger.bigsur_delete_entry(ids["leaf"])
    assert ledger.get(ids["leaf"]) is None
    # No parent should still list the deleted leaf.
    assert ids["leaf"] not in ledger.get(ids["a"]).children
    shutil.rmtree(tmp.parent)
    print("✓ test_delete_entry_unlinks_from_parents")


def test_purge_subtree_deletes_named_root_and_descendants():
    """Purging `a` deletes a and leaf; `shared` survives (still a child of b)."""
    ledger, tmp, ids = _diamond()
    deleted = ledger.bigsur_purge_subtree(ids["a"])
    assert ids["a"] in deleted            # the named purge root IS deleted
    assert ids["leaf"] in deleted         # its private descendant goes too
    assert ids["shared"] not in deleted   # diamond-shared node is kept
    assert ledger.get(ids["a"]) is None
    assert ledger.get(ids["leaf"]) is None
    assert ledger.get(ids["shared"]) is not None
    # shared is unlinked from the deleted parent but still under b.
    assert ids["shared"] in ledger.get(ids["b"]).children
    assert ids["shared"] not in [c for c in (ledger.get(ids["a"]).children if ledger.get(ids["a"]) else [])]
    shutil.rmtree(tmp.parent)
    print("✓ test_purge_subtree_deletes_named_root_and_descendants")


def test_purge_subtree_refuses_root():
    ledger, tmp, ids = _diamond()
    assert ledger.bigsur_purge_subtree(ids["root"]) == []
    assert ledger.get(ids["root"]) is not None
    shutil.rmtree(tmp.parent)
    print("✓ test_purge_subtree_refuses_root")


def test_reparent_moves_and_refuses_cycle():
    ledger, tmp, ids = _diamond()
    # Move leaf from a → b (legal).
    msg = ledger.bigsur_reparent(ids["leaf"], ids["b"])
    assert "Reparented" in msg
    assert ids["leaf"] in ledger.get(ids["b"]).children
    assert ids["leaf"] not in ledger.get(ids["a"]).children
    assert ledger.get(ids["leaf"]).parent_id == ids["b"]
    # Cycle: try to parent `a` under its own descendant `shared` (a → shared) → refused.
    cyc = ledger.bigsur_reparent(ids["a"], ids["shared"])
    assert cyc.startswith("REFUSED")
    shutil.rmtree(tmp.parent)
    print("✓ test_reparent_moves_and_refuses_cycle")


def test_update_signature_recomputes_hash_and_resets_pending():
    ledger, tmp, ids = _diamond()
    leaf = ledger.get(ids["leaf"])
    ledger.mark_failed(ids["leaf"], "was false")
    assert ledger.get(ids["leaf"]).status == LemmaStatus.FAILED
    new_stmt = "theorem leaf (h : Wf env) : P := by sorry"
    ledger.bigsur_update_signature(ids["leaf"], new_stmt)
    e = ledger.get(ids["leaf"])
    assert e.statement == new_stmt
    assert e.signature_hash == _h(new_stmt)
    assert e.status == LemmaStatus.PENDING      # changed contract → re-prove
    assert e.failure_reason == ""
    assert e.priority_boost is True
    shutil.rmtree(tmp.parent)
    print("✓ test_update_signature_recomputes_hash_and_resets_pending")


def test_reset_to_pending_clears_failure():
    ledger, tmp, ids = _diamond()
    ledger.mark_failed(ids["leaf"], "boom")
    before_hash = ledger.get(ids["leaf"]).signature_hash
    ledger.bigsur_reset_to_pending(ids["leaf"])
    e = ledger.get(ids["leaf"])
    assert e.status == LemmaStatus.PENDING
    assert e.failure_reason == ""
    assert e.priority_boost is True
    assert e.signature_hash == before_hash      # signature UNCHANGED
    shutil.rmtree(tmp.parent)
    print("✓ test_reset_to_pending_clears_failure")


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 1b — destructive ledger MCP reaches the live ledger
# ═══════════════════════════════════════════════════════════════════════════════

def test_ledger_mcp_purge_mutates_live_ledger():
    ledger, tmp, ids = _diamond()
    server = create_bigsur_ledger_mcp_server(ledger)
    out = call_mcp_tool(server, "ledger_purge_subtree", {"id": ids["a"]})
    assert ids["a"] in out and ids["leaf"] in out
    # The SAME live ledger object is mutated (orchestrator's save() would persist).
    assert ledger.get(ids["a"]) is None
    assert ledger.get(ids["shared"]) is not None
    # And the root-refusal is enforced through the tool too.
    refused = call_mcp_tool(server, "ledger_delete_entry", {"id": ids["root"]})
    assert "REFUSED" in refused
    shutil.rmtree(tmp.parent)
    print("✓ test_ledger_mcp_purge_mutates_live_ledger")


def test_ledger_mcp_update_signature_tool():
    ledger, tmp, ids = _diamond()
    server = create_bigsur_ledger_mcp_server(ledger)
    call_mcp_tool(server, "ledger_update_signature",
                  {"id": ids["leaf"], "new_statement": "theorem leaf (h : Q) : R := by sorry"})
    assert ledger.get(ids["leaf"]).status == LemmaStatus.PENDING
    assert "theorem leaf (h : Q)" in ledger.get(ids["leaf"]).statement
    shutil.rmtree(tmp.parent)
    print("✓ test_ledger_mcp_update_signature_tool")


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 1c — Sandbox-wide destructive snapshot MCP
# ═══════════════════════════════════════════════════════════════════════════════

def _make_snapshots(sandbox_root: Path):
    """Two workspaces, each with a stub_versions/ dir holding banked snapshots."""
    from strataswarm._snapshot_mcp import _save_index
    for ws, tags in (("wsA", ["v1", "v2"]), ("wsB", ["v1"])):
        snap_dir = sandbox_root / ws / "stub_versions"
        snap_dir.mkdir(parents=True)
        index = {}
        for i, tag in enumerate(tags):
            (snap_dir / f"{tag}.lean").write_text(f"-- {ws} {tag}\ntheorem t : True := by sorry")
            index[tag] = {"ts": i, "sorry_count": i, "note": f"{ws}-{tag}"}
        _save_index(snap_dir, index)


def test_snapshot_mcp_list_read_delete():
    sandbox = Path(tempfile.mkdtemp())
    _make_snapshots(sandbox)
    server = create_bigsur_snapshot_mcp_server(sandbox)

    listing = call_mcp_tool(server, "list_all_snapshots", {})
    assert "wsA" in listing and "wsB" in listing
    assert '"total_snapshots": 3' in listing

    body = call_mcp_tool(server, "read_snapshot", {"workspace": "wsA", "tag": "v1"})
    assert "wsA v1" in body

    # Delete one snapshot from wsA.
    call_mcp_tool(server, "delete_snapshot", {"workspace": "wsA", "tag": "v1"})
    assert not (sandbox / "wsA" / "stub_versions" / "v1.lean").exists()
    assert (sandbox / "wsA" / "stub_versions" / "v2.lean").exists()

    # Delete ALL of wsB's snapshots (removes the dir).
    call_mcp_tool(server, "delete_snapshots_for_workspace", {"workspace": "wsB"})
    assert not (sandbox / "wsB" / "stub_versions").exists()

    listing2 = call_mcp_tool(server, "list_all_snapshots", {})
    assert "wsB" not in listing2
    assert '"total_snapshots": 1' in listing2

    shutil.rmtree(sandbox)
    print("✓ test_snapshot_mcp_list_read_delete")


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 1d — root signature hashing
# ═══════════════════════════════════════════════════════════════════════════════

def test_root_signature_hash():
    cwd = Path(tempfile.mkdtemp())
    ws = "ws"
    (cwd / ws).mkdir(parents=True)
    assert _root_signature_hash(cwd, ws) is None      # absent
    clean = cwd / ws / "Stub.clean.lean"
    clean.write_text("theorem root : True := by sorry")
    h1 = _root_signature_hash(cwd, ws)
    assert h1 is not None
    assert _root_signature_hash(cwd, ws) == h1        # stable
    clean.write_text("theorem root : False := by sorry")
    assert _root_signature_hash(cwd, ws) != h1        # detects tampering
    shutil.rmtree(cwd)
    print("✓ test_root_signature_hash")


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 2 — orchestration with a scripted fake BigSur agent (no LLM)
# ═══════════════════════════════════════════════════════════════════════════════

class _Result:
    def __init__(self, raw): self.raw_result = raw


class FakeBigSur:
    """Scripted stand-in for the spawned BigSur agent. `decisions` is the sequence
    of raw_result strings returned for each 'Decision check.' run_ai call; other
    run_ai calls (the nudge) return empty. `on_run` fires inside the initial
    free-form run() — used to simulate tampering with Stub.clean.lean."""
    def __init__(self, decisions, on_run=None):
        self.decisions = list(decisions)
        self.on_run = on_run
        self.run_calls = 0
        self.decision_calls = 0
        self.nudge_calls = 0

    async def run(self, inp=None):
        self.run_calls += 1
        if self.on_run:
            self.on_run()
        return _Result("")

    async def run_ai(self, inp=None, max_turns=None, block_tools=None):
        if inp and inp.startswith("Decision check."):
            self.decision_calls += 1
            raw = self.decisions.pop(0) if self.decisions else \
                "DECISION: not_done\nREASON: still working"
            return _Result(raw)
        self.nudge_calls += 1
        return _Result("")


class FakeAgent:
    def __init__(self, cwd: Path):
        self.swarm = object()
        self._cwd = cwd
        self.emits = []

    async def _emit(self, kind, msg):
        self.emits.append((kind, msg))


class _FakeCM:
    def __init__(self, obj): self._obj = obj
    async def __aenter__(self): return self._obj
    async def __aexit__(self, *a): return False


def _bigsur_fixture(tamper=False):
    """A ready-to-run (agent, state, ledger, entry, cwd) with a root + one failed
    child, a pristine Stub.clean.lean, and monkeypatched module-level deps."""
    cwd = Path(tempfile.mkdtemp())
    ws = "ws"
    (cwd / ws).mkdir(parents=True)
    (cwd / ws / "Stub.clean.lean").write_text("theorem root : True := by sorry")

    ledger, _tmp = make_ledger()
    # Re-home ledger json under cwd so save() (if ever hit) stays contained.
    root = ledger.add_lemma("root", "Stub.lean", ws, _h("root"))
    child = ledger.add_lemma("child", "c.lean", f"{ws}/c", _h("child"), parent_id=root.id)

    state = PO5State()
    state.root_id = root.id
    state.root_workspace = ws
    state.root_theorem_name = "root"
    state.lemma_ctx = {}

    agent = FakeAgent(cwd)
    return agent, state, ledger, child, root, cwd, ws


class _Patched:
    """Monkeypatch po_v5 module-level deps for a single _run_bigsur call, restoring
    them afterward. Records _cleanup_all_agents invocations."""
    def __init__(self, fake_bigsur, impact="impact report text"):
        self.fake_bigsur = fake_bigsur
        self.impact = impact
        self.cleanup_calls = 0
        self.spawn_calls = 0

    def __enter__(self):
        self._orig = {
            "swarm_agent": po_v5.swarm_agent,
            "_consult_guide_raw": po_v5._consult_guide_raw,
            "_cleanup_all_agents": po_v5._cleanup_all_agents,
        }

        def fake_swarm_agent(*args, **kwargs):
            self.spawn_calls += 1
            return _FakeCM(self.fake_bigsur)

        async def fake_consult(*args, **kwargs):
            return self.impact

        async def fake_cleanup(agent):
            self.cleanup_calls += 1

        po_v5.swarm_agent = fake_swarm_agent
        po_v5._consult_guide_raw = fake_consult
        po_v5._cleanup_all_agents = fake_cleanup
        return self

    def __exit__(self, *a):
        for k, v in self._orig.items():
            setattr(po_v5, k, v)
        return False


def test_propagate_always_escalates_and_prunes():
    """A give-up records failure text on the parent, prunes the dead child's
    subtree, and ALWAYS calls _run_bigsur — no local reactivation gate."""
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    grandchild = ledger.add_lemma("gc", "gc.lean", f"{ws}/gc", _h("gc"), parent_id=child.id)

    called = {"n": 0}

    async def fake_run_bigsur(*args, **kwargs):
        called["n"] += 1

    orig = po_v5._run_bigsur
    po_v5._run_bigsur = fake_run_bigsur
    try:
        asyncio.run(_propagate_failure_to_parent(
            agent, state, ledger, child, cwd, "child is false as stated"))
    finally:
        po_v5._run_bigsur = orig

    assert called["n"] == 1                                  # escalated, unconditionally
    parent_ctx = state.lemma_ctx[root.id]
    assert "child is false as stated" in parent_ctx.failure_context   # failure recorded
    assert ledger.get(grandchild.id).status == LemmaStatus.PRUNED     # dead subtree pruned
    shutil.rmtree(cwd)
    print("✓ test_propagate_always_escalates_and_prunes")


def test_run_bigsur_success_tears_down_agents():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    fake = FakeBigSur(decisions=["DECISION: done\nREASON: ledger consistent, compiles"])
    with _Patched(fake) as p:
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "give-up reason"))
    assert state.bigsur_invocations == 1
    assert p.spawn_calls == 1
    assert p.cleanup_calls == 1                              # stale agents torn down
    assert ledger.get(root.id).status != LemmaStatus.FAILED  # root NOT failed
    assert not state.user_fix_request
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_success_tears_down_agents")


def test_run_bigsur_tamper_guard_fails_root():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    clean = cwd / ws / "Stub.clean.lean"

    def tamper():
        clean.write_text("theorem root : False := by sorry")   # forbidden edit

    fake = FakeBigSur(decisions=["DECISION: done\nREASON: consistent"], on_run=tamper)
    with _Patched(fake) as p:
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "reason"))
    assert ledger.get(root.id).status == LemmaStatus.FAILED
    assert "tamper" in state.give_up_reason.lower() or \
           "immutable root" in state.give_up_reason.lower()
    assert p.cleanup_calls == 0        # tamper path returns BEFORE success teardown
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_tamper_guard_fails_root")


def test_run_bigsur_epiphany_records_user_fix_and_fails_root():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    fake = FakeBigSur(decisions=[
        "DECISION: give_up\nREASON: root admits counterexample at n=0"])
    with _Patched(fake):
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "reason"))
    assert ledger.get(root.id).status == LemmaStatus.FAILED
    assert "counterexample at n=0" in state.user_fix_request
    assert "root" in state.user_fix_request
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_epiphany_records_user_fix_and_fails_root")


def test_run_bigsur_invocation_cap_no_spawn():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    state.bigsur_invocations = BIGSUR_MAX_INVOCATIONS      # already at the cap
    fake = FakeBigSur(decisions=["DECISION: done\nREASON: x"])
    with _Patched(fake) as p:
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "last straw"))
    assert p.spawn_calls == 0                              # did NOT spawn BigSur
    assert ledger.get(root.id).status == LemmaStatus.FAILED
    assert "last straw" in state.give_up_reason
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_invocation_cap_no_spawn")


def test_run_bigsur_decision_rounds_exhausted_proceeds():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    # Always 'not_done' → loop runs the full budget, then proceeds (success routing).
    fake = FakeBigSur(decisions=["DECISION: not_done\nREASON: more work"] * (BIGSUR_DECISION_ROUNDS + 2))
    with _Patched(fake) as p:
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "reason"))
    assert fake.decision_calls == BIGSUR_DECISION_ROUNDS   # asked exactly the budget
    assert p.cleanup_calls == 1                            # proceeded to success teardown
    assert ledger.get(root.id).status != LemmaStatus.FAILED
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_decision_rounds_exhausted_proceeds")


if __name__ == "__main__":
    # Layer 1
    test_delete_entry_refuses_root()
    test_delete_entry_unlinks_from_parents()
    test_purge_subtree_deletes_named_root_and_descendants()
    test_purge_subtree_refuses_root()
    test_reparent_moves_and_refuses_cycle()
    test_update_signature_recomputes_hash_and_resets_pending()
    test_reset_to_pending_clears_failure()
    test_ledger_mcp_purge_mutates_live_ledger()
    test_ledger_mcp_update_signature_tool()
    test_snapshot_mcp_list_read_delete()
    test_root_signature_hash()
    # Layer 2
    test_propagate_always_escalates_and_prunes()
    test_run_bigsur_success_tears_down_agents()
    test_run_bigsur_tamper_guard_fails_root()
    test_run_bigsur_epiphany_records_user_fix_and_fails_root()
    test_run_bigsur_invocation_cap_no_spawn()
    test_run_bigsur_decision_rounds_exhausted_proceeds()
    print("\n✅ All BigSur tests passed!")
