"""Deterministic tests for the PO v5 leaf-sorry progress metric and its endgame
handling (po_v5._format_progress + the ENDGAME_GRACE_CHUNKS idle-clock rule).

Background — two failure modes of the OLD metric (tsm.open_sorry_count(), which
counts distinct reachable decls via the axioms verdict), both on the critical
path of a real detToKleene run:

  1. BUILD RED endgame: the writer replaced the LAST sorry with a real proof that
     has compile errors. 0 real sorries, but the axioms oracle can't confirm
     anything while the build is red, so every reachable decl read
     has_transitive_sorry=True → the count froze at the reachable-decl total and
     the line read "NO REDUCTION: still 4 ... (NOT COMPILING)". A near-done proof
     looked identical to a stall, the idle clock never reset, and a backstop
     could have killed it.
  2. 1:1 FACTORING spike: moving a sorry from the target into a fresh inline
     helper spawns a new reachable decl → the decl-count went UP (4→5) on healthy
     decomposition — the very signal feeding decompose / give-up.

The fix switches the metric to the literal LEAF-sorry count (build-independent,
flat when a sorry just moves) and gives the sorry-free-but-not-compiling endgame
its own positive framing + a bounded idle-clock credit.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_progress_metric.py
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_v5 import _format_progress, ENDGAME_GRACE_CHUNKS


def test_leaf_count_basic_transitions() -> None:
    """The ordinary compiling-file transitions read as before, on LEAF counts."""
    assert _format_progress(None, 3).startswith("Open leaf-sorries: 3")
    assert _format_progress(4, 2).startswith("PROGRESS: leaf-sorries 4 → 2")
    assert _format_progress(4, 4).startswith("NO REDUCTION: still 4")
    # count went UP while compiling (rare, but must not claim progress)
    up = _format_progress(4, 5)
    assert "PROGRESS" not in up and "5" in up


def test_factoring_is_flat_not_a_spike() -> None:
    """Moving a sorry target→helper keeps the LEAF count flat: 4 sorries before,
    4 after (one closed in the target, one opened in the new helper). The old
    decl-count spiked 4→5 here and tripped the stuck/decompose signal."""
    # Same number of literal sorries before and after the 1:1 factoring.
    line = _format_progress(4, 4)
    assert "NO REDUCTION" in line and "5" not in line, line


def test_endgame_zero_sorries_not_compiling_reads_as_progress() -> None:
    """0 leaf-sorries but not compiling = the writer closed the last sorry and is
    fixing compile errors. It must read POSITIVELY, never as a stall."""
    # transition from having a sorry to none
    line = _format_progress(1, 0, compiles=False)
    assert "PROGRESS" in line and "SKETCH COMPLETE" in line, line
    assert "NO REDUCTION" not in line
    # steady state at 0 sorries, still red (no prior known)
    line2 = _format_progress(0, 0, compiles=False)
    assert "SKETCH COMPLETE" in line2 and "stall" in line2.lower(), line2
    # and it is NOT the alarming "still N open" phrasing
    assert "NO REDUCTION" not in line2


def test_endgame_zero_sorries_compiling_is_not_the_endgame_message() -> None:
    """0 sorries AND compiling is a genuinely-done file, handled by the proved
    gate upstream — _format_progress should NOT emit the endgame 'closing compile
    errors' text for it."""
    line = _format_progress(1, 0, compiles=True)
    assert "closing compile errors" not in line
    assert "PROGRESS: leaf-sorries 1 → 0" in line


def test_endgame_grace_is_bounded() -> None:
    """The grace window is a real, small bound — enough for a one-tactic-away
    finish, not a licence to reset the backstop forever."""
    assert 1 <= ENDGAME_GRACE_CHUNKS <= 10


def _main() -> None:
    for fn in (
        test_leaf_count_basic_transitions,
        test_factoring_is_flat_not_a_spike,
        test_endgame_zero_sorries_not_compiling_reads_as_progress,
        test_endgame_zero_sorries_compiling_is_not_the_endgame_message,
        test_endgame_grace_is_bounded,
    ):
        fn()
        print(f"  {fn.__name__} OK")
    print("ALL PROGRESS-METRIC TESTS PASSED")


if __name__ == "__main__":
    _main()
