"""Regression test for the CONTINGENT scope trap (po_v5._proved_or_contingent).

Background — the callElim `defUseWF_fold` failure (session 2026-08-07_07-08-44):

  A lemma with its OWN open `sorry` got parked CONTINGENT because it happened to
  have extracted children (`entry.children` truthy), even though its own target
  still carried 11 sorries. CONTINGENT nodes are invisible to SELECT (which only
  picks PENDING) and mark_contingent clears priority_boost, so:

    BigSur threads a hypothesis → reset to PENDING (+boost) → a prover re-enters →
    `_proved_or_contingent` sees `entry.children` → marks CONTINGENT → the node
    vanishes from SELECT → its parent re-escalates to BigSur with "already
    sorry-free, nothing to do" → BigSur re-opens it → loop.

  The one node that actually needed proving was buried the instant a prover
  touched it. The fix: CONTINGENT means "locally clean, only waiting on a
  sibling/child". If THIS entry's own target(s) still carry sorry, it has real
  work and must fall through (return None) so a prover keeps driving it.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_contingent_scope.py
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules import po_v5
from strataswarm.modules.lemma_ledger import LemmaStatus


class _FakeEntry:
    def __init__(self, name, children):
        self.id = "fe00f5e1"
        self.name = name
        self.children = children
        self.status = LemmaStatus.PENDING


class _FakeLedger:
    """Records mark_contingent calls without a real ledger."""

    def __init__(self):
        self.contingent_ids: list[str] = []
        self.proved_ids: list[str] = []

    def mark_contingent(self, entry_id):
        self.contingent_ids.append(entry_id)

    def mark_proved(self, entry_id, import_path):  # not exercised here
        self.proved_ids.append(entry_id)


class _FakeTools:
    def __init__(self, local_sorry):
        self._local_sorry = local_sorry

    def get_sorries_by_theorem(self, stub_rel):
        return self._local_sorry


def _patch(monkeypatch_targets):
    """Swap module-level helpers; return a restore callable."""
    saved = {name: getattr(po_v5, name) for name in monkeypatch_targets}
    for name, fn in monkeypatch_targets.items():
        setattr(po_v5, name, fn)

    def restore():
        for name, fn in saved.items():
            setattr(po_v5, name, fn)

    return restore


def test_own_sorry_with_children_falls_through_not_contingent() -> None:
    """THE BUG: a node with its own open sorry AND children must NOT be parked
    contingent — it has real local work → return None (keep proving it)."""
    entry = _FakeEntry("callElim_body_defUseWF_fold", children=["child_a"])
    ledger = _FakeLedger()
    tools = _FakeTools({"callElim_body_defUseWF_fold": [(10, 5)]})  # own target sorried
    restore = _patch({
        "_entry_transitively_proven": lambda t, e: False,
        "_sibling_target_names": lambda *a, **k: set(),
        "_get_protected_names": lambda t, s, e: {"callElim_body_defUseWF_fold"},
    })
    try:
        verdict = po_v5._proved_or_contingent(tools, ledger, entry, cwd=None,
                                              stub_rel="Sandbox/x/Stub.lean")
    finally:
        restore()
    assert verdict is None, f"expected fall-through, got {verdict!r}"
    assert ledger.contingent_ids == [], "must NOT mark contingent with own sorry"


def test_locally_clean_with_children_is_contingent() -> None:
    """The legitimate contingent case is preserved: no OWN sorry but has children
    still in flight → CONTINGENT (waiting on the subtree)."""
    entry = _FakeEntry("parent_lemma", children=["child_a"])
    ledger = _FakeLedger()
    tools = _FakeTools({})  # no local sorry at all
    restore = _patch({
        "_entry_transitively_proven": lambda t, e: False,
        "_sibling_target_names": lambda *a, **k: set(),
        "_get_protected_names": lambda t, s, e: {"parent_lemma"},
    })
    try:
        verdict = po_v5._proved_or_contingent(tools, ledger, entry, cwd=None,
                                              stub_rel="Sandbox/x/Stub.lean")
    finally:
        restore()
    assert verdict == "contingent", f"expected contingent, got {verdict!r}"
    assert ledger.contingent_ids == [entry.id]


def test_sibling_sorry_only_still_contingent() -> None:
    """Locally clean on OWN target, no children, but a SIBLING obligation in the
    shared file is sorried → still contingent (waiting on the sibling)."""
    entry = _FakeEntry("target_a", children=[])
    ledger = _FakeLedger()
    tools = _FakeTools({"target_b": [(3, 1)]})  # a sibling's sorry, not ours
    restore = _patch({
        "_entry_transitively_proven": lambda t, e: False,
        "_sibling_target_names": lambda *a, **k: {"target_b"},
        "_get_protected_names": lambda t, s, e: {"target_a"},
    })
    try:
        verdict = po_v5._proved_or_contingent(tools, ledger, entry, cwd=None,
                                              stub_rel="Sandbox/x/Stub.lean")
    finally:
        restore()
    assert verdict == "contingent", f"expected contingent, got {verdict!r}"
    assert ledger.contingent_ids == [entry.id]


def test_clean_transitively_unproven_imported_dep_is_contingent() -> None:
    """THE canfail FIX: locally clean on its own target, NO children, NO same-file
    sibling sorry — but transitively unproven because the residual sorry lives in
    an IMPORTED cross-branch dependency the writer can't edit. Old code fell through
    to None → keep proving → give_up → BigSur (the 20× canfail loop). New rule:
    locally clean + transitively unproven = waiting on a proof in flight → contingent,
    regardless of where the residual sorry lives."""
    entry = _FakeEntry("callElim_sim_canfail", children=[])
    ledger = _FakeLedger()
    tools = _FakeTools({})  # no LOCAL sorry — residual is in an imported cousin file
    restore = _patch({
        # transitively UNPROVEN (oracle sees the imported sibling's sorry)
        "_entry_transitively_proven": lambda t, e: False,
        "_sibling_target_names": lambda *a, **k: set(),
        "_get_protected_names": lambda t, s, e: {"callElim_sim_canfail"},
    })
    try:
        verdict = po_v5._proved_or_contingent(tools, ledger, entry, cwd=None,
                                              stub_rel="Sandbox/x/Stub.lean")
    finally:
        restore()
    assert verdict == "contingent", f"expected contingent, got {verdict!r}"
    assert ledger.contingent_ids == [entry.id]


def _main() -> None:
    for fn in (
        test_own_sorry_with_children_falls_through_not_contingent,
        test_locally_clean_with_children_is_contingent,
        test_sibling_sorry_only_still_contingent,
        test_clean_transitively_unproven_imported_dep_is_contingent,
    ):
        fn()
        print(f"  {fn.__name__} OK")
    print("ALL CONTINGENT-SCOPE TESTS PASSED")


if __name__ == "__main__":
    _main()
