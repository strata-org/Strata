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


def test_purge_subtree_keeps_deep_child_of_shared_node():
    """Bug #2 regression: purging a branch must TRANSITIVELY protect the descendants
    of a kept diamond-shared node. Layout:
        root → a, b ; a → shared ; b → shared ; shared → deep
    Purge `a`: `shared` survives (also under b), so `deep` (only under shared) MUST
    survive too — keeping the shelf is pointless if its books are thrown out."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "Stub.lean", "ws", _h("root"))
    a = ledger.add_lemma("a", "a.lean", "ws/a", _h("a"), parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", _h("b"), parent_id=root.id)
    shared = ledger.add_lemma("shared", "s.lean", "ws/s", _h("shared"), parent_id=a.id)
    deep = ledger.add_lemma("deep", "d.lean", "ws/d", _h("deep"), parent_id=shared.id)
    assert ledger.add_parent(b.id, shared.id) is None   # shared is a diamond node

    deleted = ledger.bigsur_purge_subtree(a.id)
    assert a.id in deleted                       # named purge root deleted
    assert shared.id not in deleted              # kept (also under b)
    assert deep.id not in deleted                # ← Bug #2: MUST be kept (under kept shared)
    assert ledger.get(shared.id) is not None
    assert ledger.get(deep.id) is not None
    assert deep.id in ledger.get(shared.id).children   # link intact
    shutil.rmtree(tmp.parent)
    print("✓ test_purge_subtree_keeps_deep_child_of_shared_node")


def test_delete_entry_repoints_children_no_ghost_parent():
    """Bug #3 regression: deleting a node must not leave its children pointing at a
    ghost parent_id (which truncates get_ancestry). In the diamond, `leaf`/`shared`
    are under `a`; delete `a` and its children must re-point to a surviving parent
    (root, via nothing) or clear parent_id — never keep a.id."""
    ledger, tmp, ids = _diamond()
    # leaf's only parent is a; shared has parents a AND b.
    ledger.bigsur_delete_entry(ids["a"])
    assert ledger.get(ids["a"]) is None
    # No surviving entry may still record the deleted `a` as its parent.
    for e in ledger.entries():
        assert e.parent_id != ids["a"], f"{e.name} has ghost parent_id {ids['a']}"
    # shared still has b as a real parent → repointed to b (b lists it as a child).
    assert ledger.get(ids["shared"]).parent_id == ids["b"]
    # leaf lost its only parent → orphaned (parent_id cleared).
    assert ledger.get(ids["leaf"]).parent_id == ""
    shutil.rmtree(tmp.parent)
    print("✓ test_delete_entry_repoints_children_no_ghost_parent")


def test_ancestry_intact_after_delete():
    """Bug #3 consequence: get_ancestry must not stop short after a delete. Chain
    root → a → shared (also → b) → deep; delete `a`; deep's ancestry must still
    reach root through the surviving b-path (shared repointed to b)."""
    ledger, tmp = make_ledger()
    root = ledger.add_lemma("root", "Stub.lean", "ws", _h("root"))
    a = ledger.add_lemma("a", "a.lean", "ws/a", _h("a"), parent_id=root.id)
    b = ledger.add_lemma("b", "b.lean", "ws/b", _h("b"), parent_id=root.id)
    shared = ledger.add_lemma("shared", "s.lean", "ws/s", _h("shared"), parent_id=a.id)
    deep = ledger.add_lemma("deep", "d.lean", "ws/d", _h("deep"), parent_id=shared.id)
    assert ledger.add_parent(b.id, shared.id) is None

    ledger.bigsur_delete_entry(a.id)
    anc = ledger.get_ancestry(deep.id)   # walks parent_id links
    # deep → shared → b → root, no dead-end at the deleted `a`.
    assert root.id in anc, f"ancestry truncated: {anc}"
    assert a.id not in anc
    shutil.rmtree(tmp.parent)
    print("✓ test_ancestry_intact_after_delete")


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


def test_ledger_mcp_save_persists_to_disk_and_dag():
    """ledger_save must write the mutated ledger to disk AND regenerate the DAG
    views the UI reads — so BigSur's edits are durable and shown, not just in memory."""
    import json as _json
    ledger, tmp, ids = _diamond()
    server = create_bigsur_ledger_mcp_server(ledger)
    # Mutate in memory only (no direct save), then persist via the tool.
    call_mcp_tool(server, "ledger_purge_subtree", {"id": ids["leaf"]})
    out = call_mcp_tool(server, "ledger_save", {})
    assert '"saved": true' in out
    # JSON on disk reflects the deletion.
    data = _json.loads(tmp.read_text())
    assert ids["leaf"] not in data["entries"]
    assert ids["root"] in data["entries"]
    # DAG views regenerated for the dashboard.
    assert (tmp.parent / "lemma_dag.md").exists()
    assert (tmp.parent / "lemma_dag_mermaid.md").exists()
    shutil.rmtree(tmp.parent)
    print("✓ test_ledger_mcp_save_persists_to_disk_and_dag")


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
# LAYER 1e — BigSur lake-build compile tool
# ═══════════════════════════════════════════════════════════════════════════════

def test_file_path_to_module_conversion():
    """BigSur passes a FILE PATH; the build tool converts it to a lake module name."""
    from strataswarm.modules.po_lean import file_path_to_module
    cwd = Path("/proj")
    assert file_path_to_module("StrataAgent/Sandbox/decomposed/foo/Stub.lean", cwd) \
        == "StrataAgent.Sandbox.decomposed.foo.Stub"
    assert file_path_to_module("/proj/StrataAgent/Sandbox/Stub.lean", cwd) \
        == "StrataAgent.Sandbox.Stub"                 # absolute under cwd
    assert file_path_to_module("StrataAgent.Sandbox.Stub", cwd) \
        == "StrataAgent.Sandbox.Stub"                 # already a module name
    assert file_path_to_module("Foo.lean", cwd) == "Foo"
    print("✓ test_file_path_to_module_conversion")


def test_lake_build_ok_keyed_on_exit_code():
    """lake_build must key `ok` on the EXIT CODE, not on the absence of `: error:`
    lines. A nonexistent module fails with exit 1 and lake-level `error: no such
    file` / `error: build failed` lines that are NOT in Lean's file:line:col: format
    — the old filter reported that as ok=true (dangerous false positive)."""
    from strataswarm.modules import po_lean

    class FakeProc:
        def __init__(self, rc, out, err): self.returncode, self.stdout, self.stderr = rc, out, err

    orig = po_lean.subprocess.run
    try:
        # Nonexistent module: exit 1, lake-level errors only (no ": error:").
        po_lean.subprocess.run = lambda *a, **k: FakeProc(
            1, "✖ [2/2] Running Foo\n", "error: no such file\nerror: build failed\n")
        ok, errs = po_lean.lake_build("Foo", Path("/proj"))
        assert ok is False                       # ← keyed on exit code, not the pattern
        assert any("no such file" in e for e in errs)

        # Success: exit 0, only lints/warnings.
        po_lean.subprocess.run = lambda *a, **k: FakeProc(0, "Build completed (3 jobs).\n", "")
        ok, errs = po_lean.lake_build("Foo", Path("/proj"))
        assert ok is True and errs == []

        # Real compile error: exit 1 with a Lean diagnostic line.
        po_lean.subprocess.run = lambda *a, **k: FakeProc(
            1, "", "error: Foo.lean:1:40: type mismatch\nerror: build failed\n")
        ok, errs = po_lean.lake_build("Foo", Path("/proj"))
        assert ok is False
        assert any("type mismatch" in e for e in errs)
    finally:
        po_lean.subprocess.run = orig
    print("✓ test_lake_build_ok_keyed_on_exit_code")


def test_build_mcp_tool_reports_errors(monkeypatch=None):
    """The build MCP tool converts the file path, calls lake_build, and returns
    {ok, errors}. We stub lake_build so no real Lean is needed."""
    from strataswarm import _bigsur_build_mcp as bm
    calls = {}

    def fake_lake_build(module, cwd, timeout=None):
        calls["module"] = module
        return False, ["Foo.lean:3:0: error: unsolved goals"]

    orig = bm.lake_build
    bm.lake_build = fake_lake_build
    try:
        server = bm.create_bigsur_build_mcp_server(Path("/proj"))
        out = call_mcp_tool(server, "lake_build_check",
                            {"file_path": "StrataAgent/Sandbox/decomposed/foo/Stub.lean"})
    finally:
        bm.lake_build = orig
    assert calls["module"] == "StrataAgent.Sandbox.decomposed.foo.Stub"  # converted
    assert '"ok": false' in out
    assert "unsolved goals" in out
    print("✓ test_build_mcp_tool_reports_errors")


def test_build_mcp_tool_success():
    from strataswarm import _bigsur_build_mcp as bm

    def fake_ok(module, cwd, timeout=None):
        return True, []

    orig = bm.lake_build
    bm.lake_build = fake_ok
    try:
        server = bm.create_bigsur_build_mcp_server(Path("/proj"))
        out = call_mcp_tool(server, "lake_build_check", {"file_path": "ws/Stub.lean"})
    finally:
        bm.lake_build = orig
    assert '"ok": true' in out
    assert '"error_count": 0' in out
    print("✓ test_build_mcp_tool_success")


def test_build_tool_name_no_collision_with_lsp():
    """The build tool's short (final __-segment) name must be UNIQUE — never
    'lean_build' — so it cannot collide with the blocked mcp__lean_lsp__lean_build
    under short-name (rsplit('__',1)[-1]) block-hook matching."""
    import yaml as _yaml
    from strataswarm import _bigsur_build_mcp as bm
    server = bm.create_bigsur_build_mcp_server(Path("/proj"))
    # Discover the tool's registered name via list_tools.
    from mcp.types import ListToolsRequest
    srv = server["instance"]
    res = asyncio.run(srv.request_handlers[ListToolsRequest](
        ListToolsRequest(method="tools/list")))
    names = [t.name for t in res.root.tools]
    assert names == ["lake_build_check"], names
    short = names[0].rsplit("__", 1)[-1]
    assert short != "lean_build", "collides with lean-lsp lean_build short name"
    # And the bigsur.yaml allow/deny lists must not share a short segment.
    d = _yaml.safe_load(open(Path(__file__).parent.parent
                              / "strataswarm/agent_specs/agents/bigsur.yaml"))
    allow_shorts = {t.rsplit("__", 1)[-1] for t in d["allowed_tools"] if isinstance(t, str)}
    deny_shorts = {t.rsplit("__", 1)[-1] for t in d["disallowed_tools"] if isinstance(t, str)}
    assert "lake_build_check" in allow_shorts
    assert "lake_build_check" not in deny_shorts
    assert allow_shorts.isdisjoint(deny_shorts), \
        f"allow/deny share short name(s): {allow_shorts & deny_shorts}"
    print("✓ test_build_tool_name_no_collision_with_lsp")


# ═══════════════════════════════════════════════════════════════════════════════
# LAYER 2 — orchestration with a scripted fake BigSur agent (no LLM)
# ═══════════════════════════════════════════════════════════════════════════════

class _Result:
    def __init__(self, raw): self.raw_result = raw


class FakeBigSur:
    """Scripted stand-in for the spawned BigSur agent. `decisions` is the sequence
    of raw_result strings returned for each 'Decision check.' run_ai call; other
    run_ai calls (initial briefing + nudge) return empty. `on_briefing` fires inside
    the initial repair pass — used to simulate tampering with Stub.clean.lean.

    IMPORTANT: the initial pass MUST be driven via run_ai, NOT run() — run() on a
    stateful agent never returns (freeze bug). If _run_bigsur ever calls .run(),
    `run_called` flips True and the freeze test fails."""
    def __init__(self, decisions, on_briefing=None):
        self.decisions = list(decisions)
        self.on_briefing = on_briefing
        self.run_called = False        # must stay False — .run() would freeze
        self.briefing_calls = 0
        self.decision_calls = 0
        self.nudge_calls = 0

    async def run(self, inp=None):
        # Simulate the freeze: run() on a stateful agent never returns. If the
        # product code (wrongly) calls this, the test hangs — but we also flag it.
        self.run_called = True
        raise AssertionError(
            "_run_bigsur called bigsur.run() — this freezes on a stateful agent; "
            "it must use run_ai() for the initial pass.")

    async def run_ai(self, inp=None, max_turns=None, block_tools=None):
        if inp and inp.startswith("Decision check."):
            self.decision_calls += 1
            raw = self.decisions.pop(0) if self.decisions else \
                "DECISION: not_done\nREASON: still working"
            return _Result(raw)
        # The initial briefing pass (first non-decision run_ai) or a nudge.
        if self.briefing_calls == 0 and (not inp or not inp.startswith("Continue")):
            self.briefing_calls += 1
            if self.on_briefing:
                self.on_briefing()
            return _Result("")
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
    assert fake.run_called is False        # freeze bug: must NOT call .run()
    assert fake.briefing_calls == 1        # initial pass driven via run_ai
    assert fake.decision_calls == 1        # decision loop was REACHED (not hung)
    assert p.cleanup_calls == 1                              # stale agents torn down
    assert ledger.get(root.id).status != LemmaStatus.FAILED  # root NOT failed
    assert not state.user_fix_request
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_success_tears_down_agents")


def test_run_bigsur_uses_run_ai_not_run():
    """Freeze-bug regression: the initial repair pass must be driven by run_ai. If
    _run_bigsur calls bigsur.run() (which never returns on a stateful agent), the
    FakeBigSur raises AssertionError from run() — caught here."""
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    fake = FakeBigSur(decisions=["DECISION: done\nREASON: ok"])
    with _Patched(fake):
        asyncio.run(_run_bigsur(agent, state, ledger, child, cwd, "reason"))
    assert fake.run_called is False, "_run_bigsur used .run() — reintroduced the freeze"
    assert fake.decision_calls >= 1, "decision loop never reached — likely frozen"
    shutil.rmtree(cwd)
    print("✓ test_run_bigsur_uses_run_ai_not_run")


def test_propagate_swallows_bigsur_crash():
    """Crash-guard regression: if _run_bigsur raises (network/timeout), the give-up
    must NOT propagate out of _propagate_failure_to_parent — it logs, records the
    give-up, and returns so the phase loop keeps the rest of the run alive."""
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()

    async def boom(*a, **k):
        raise RuntimeError("model timeout")

    orig = po_v5._run_bigsur
    po_v5._run_bigsur = boom
    try:
        # Must NOT raise.
        asyncio.run(_propagate_failure_to_parent(
            agent, state, ledger, child, cwd, "child gave up"))
    finally:
        po_v5._run_bigsur = orig

    assert any("BigSur failed to run" in m for _, m in agent.emits)  # logged
    assert "BigSur invocation error" in state.give_up_reason         # recorded
    shutil.rmtree(cwd)
    print("✓ test_propagate_swallows_bigsur_crash")


def test_run_bigsur_tamper_guard_fails_root():
    agent, state, ledger, child, root, cwd, ws = _bigsur_fixture()
    clean = cwd / ws / "Stub.clean.lean"

    def tamper():
        clean.write_text("theorem root : False := by sorry")   # forbidden edit

    fake = FakeBigSur(decisions=["DECISION: done\nREASON: consistent"], on_briefing=tamper)
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
    test_purge_subtree_keeps_deep_child_of_shared_node()
    test_delete_entry_repoints_children_no_ghost_parent()
    test_ancestry_intact_after_delete()
    test_update_signature_recomputes_hash_and_resets_pending()
    test_reset_to_pending_clears_failure()
    test_ledger_mcp_purge_mutates_live_ledger()
    test_ledger_mcp_update_signature_tool()
    test_ledger_mcp_save_persists_to_disk_and_dag()
    test_snapshot_mcp_list_read_delete()
    test_root_signature_hash()
    test_file_path_to_module_conversion()
    test_lake_build_ok_keyed_on_exit_code()
    test_build_mcp_tool_reports_errors()
    test_build_mcp_tool_success()
    test_build_tool_name_no_collision_with_lsp()
    # Layer 2
    test_propagate_always_escalates_and_prunes()
    test_propagate_swallows_bigsur_crash()
    test_run_bigsur_success_tears_down_agents()
    test_run_bigsur_uses_run_ai_not_run()
    test_run_bigsur_tamper_guard_fails_root()
    test_run_bigsur_epiphany_records_user_fix_and_fails_root()
    test_run_bigsur_invocation_cap_no_spawn()
    test_run_bigsur_decision_rounds_exhausted_proceeds()
    print("\n✅ All BigSur tests passed!")
