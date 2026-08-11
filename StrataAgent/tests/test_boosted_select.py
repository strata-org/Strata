"""Regression test for BigSur-nomination-wins SELECT (po_v5._phase_select via
LemmaLedger.pick_boosted).

Background — the callElim `defUseWF_fold` failure (session 2026-08-07_07-08-44):

  BigSur re-opened the fold with a threaded hypothesis. bigsur_update_signature /
  bigsur_reset_to_pending set status=PENDING AND priority_boost=True — a
  deliberate nomination of THE node to prove next. But _phase_select ignored the
  boost in the common (has-pending-children) case: it walked the DFS candidates
  and asked the parent's guide "pick the hardest child", and the guide — lacking
  BigSur's just-computed repair context — re-litigated into the root / sibling,
  so BigSur's re-opened node kept losing the vote and never got a prover.

  Fix: a boosted-PENDING entry wins SELECT outright, bypassing the DFS walk and
  the guide consult. pick_boosted returns it; mark_proving clears the boost so it
  fires exactly once.

These tests exercise the ledger primitive (pick_boosted) directly — the
deterministic core of the fix — plus the once-only firing via mark_proving.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_boosted_select.py
"""

from __future__ import annotations

import os
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.lemma_ledger import LemmaLedger, LemmaStatus


def _h(text: str) -> str:
    return LemmaLedger.compute_signature_hash(text)


def _tree():
    """root → defUseWF → fold ; root → sibling. Returns (ledger, tmp, ids)."""
    tmp = Path(tempfile.mkdtemp()) / "test_ledger.json"
    ledger = LemmaLedger(tmp)
    root = ledger.add_lemma("root", "Stub.lean", "ws", _h("root"))
    duw = ledger.add_lemma("defUseWF", "duw.lean", "ws/duw", _h("duw"), parent_id=root.id)
    fold = ledger.add_lemma("fold", "fold.lean", "ws/fold", _h("fold"), parent_id=duw.id)
    sib = ledger.add_lemma("sibling", "sib.lean", "ws/sib", _h("sib"), parent_id=root.id)
    ids = {"root": root.id, "duw": duw.id, "fold": fold.id, "sib": sib.id}
    return ledger, tmp, ids


def test_no_boost_returns_none():
    """With no boosted entry, pick_boosted returns None so SELECT falls through to
    the normal DFS + guide path (unchanged exploration behaviour)."""
    ledger, tmp, ids = _tree()
    try:
        assert ledger.pick_boosted() is None
    finally:
        shutil.rmtree(tmp.parent)
    print("✓ test_no_boost_returns_none")


def test_bigsur_reset_boost_wins_over_other_pending():
    """THE FIX: after bigsur_reset_to_pending on the fold, it is the boosted-PENDING
    nominee — pick_boosted returns IT, not the root or a sibling, even though those
    are also pending."""
    ledger, tmp, ids = _tree()
    try:
        ledger.bigsur_reset_to_pending(ids["fold"])
        winner = ledger.pick_boosted()
        assert winner is not None and winner.id == ids["fold"], \
            f"expected fold nominee, got {winner and winner.name}"
    finally:
        shutil.rmtree(tmp.parent)
    print("✓ test_bigsur_reset_boost_wins_over_other_pending")


def test_update_signature_also_boosts():
    """bigsur_update_signature likewise nominates its entry (PENDING + boost)."""
    ledger, tmp, ids = _tree()
    try:
        ledger.bigsur_update_signature(ids["fold"], "theorem fold (h : P) : Q := by sorry")
        winner = ledger.pick_boosted()
        assert winner is not None and winner.id == ids["fold"]
    finally:
        shutil.rmtree(tmp.parent)
    print("✓ test_update_signature_also_boosts")


def test_mark_proving_clears_boost_fires_once():
    """The nomination must fire EXACTLY once: after SELECT picks it (mark_proving),
    the boost is cleared and pick_boosted no longer returns it — so it can't pin
    that node forever."""
    ledger, tmp, ids = _tree()
    try:
        ledger.bigsur_reset_to_pending(ids["fold"])
        assert ledger.pick_boosted().id == ids["fold"]
        ledger.mark_proving(ids["fold"])          # SELECT consumes the nomination
        # boosted gone; and it's now PROVING (not PENDING), so not re-nominatable
        assert ledger.pick_boosted() is None
        assert ledger.get(ids["fold"]).status == LemmaStatus.PROVING
    finally:
        shutil.rmtree(tmp.parent)
    print("✓ test_mark_proving_clears_boost_fires_once")


def test_only_pending_boost_counts_not_proving():
    """A boost on a non-PENDING entry is not a live nomination — pick_boosted only
    considers PENDING (a PROVING/PROVED node is not up for selection)."""
    ledger, tmp, ids = _tree()
    try:
        ledger.bigsur_reset_to_pending(ids["fold"])
        ledger.mark_proving(ids["fold"])
        # Manually re-set a boost on the now-PROVING entry — must be ignored.
        ledger.get(ids["fold"]).priority_boost = True
        assert ledger.pick_boosted() is None
    finally:
        shutil.rmtree(tmp.parent)
    print("✓ test_only_pending_boost_counts_not_proving")


def _main():
    for fn in (
        test_no_boost_returns_none,
        test_bigsur_reset_boost_wins_over_other_pending,
        test_update_signature_also_boosts,
        test_mark_proving_clears_boost_fires_once,
        test_only_pending_boost_counts_not_proving,
    ):
        fn()
    print("ALL BOOSTED-SELECT TESTS PASSED")


if __name__ == "__main__":
    _main()
