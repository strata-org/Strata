"""End-to-end tests for the TaskManager prover watchdog / escalation ladder (Bug #2).

Background: in the `type_preservation''` run the prover finished its one real leaf
and then spun for ~2 days emitting byte-identical "holding" messages while the
monitor excused the stall as "benign" — it never checked the actual target's
sorry status and never terminated. The watchdog (`_prover_watchdog` in
task_manager.py) fixes this: on each idle monitor tick during PROVING it
escalates on wall-clock elapsed (warn → redispatch → terminate) and, before any
restart/terminate, consults the authoritative oracle (`_target_proven`) to catch
a prover that is secretly already done.

These tests exercise the exact behaviors we now guard against:

  _target_proven (real Lean builds against Sandbox/Stub.lean):
    * a proven stub    → True  (spinning-but-done → escalate to success)
    * a sorry stub     → False (genuinely not done → keep escalating)
    * no theorem_names → None  (can't enumerate → defer to time-based ladder)

  _prover_watchdog (escalation ladder, with controlled time):
    * below warn threshold           → keep monitoring (None)
    * warn tier                      → nudge exactly once, then keep monitoring
    * past redispatch, target proven → PROVER_DONE (no needless kill)
    * past redispatch, not proven    → redispatch a fresh prover (bounded)
    * restarts exhausted             → terminate (force_terminate) → PROVER_DONE

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_prover_watchdog.py
"""

from __future__ import annotations

import asyncio
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules import task_manager as tm
from strataswarm.modules.task_manager import (
    WorkflowState, WorkflowMode, Stage, Transition,
    _target_proven, _prover_watchdog,
    PROVER_WARN, PROVER_REDISPATCH, MAX_REDISPATCHES,
)

STRATA_AGENT = Path(__file__).resolve().parent.parent
REPO_ROOT = STRATA_AGENT.parent
STUB_ABS = REPO_ROOT / "StrataAgent" / "Sandbox" / "Stub.lean"

PROVEN_STUB = (
    "module\n"
    "public theorem watchdog_target (a b : Nat) : a + b = b + a := by omega\n"
)
SORRY_STUB = (
    "module\n"
    "public theorem watchdog_target (a b : Nat) : a + b = b + a := by sorry\n"
)


# ── A minimal fake agent + fake asyncio task ─────────────────────────────────
class _FakeTask:
    def __init__(self, done: bool = False):
        self._done = done

    def done(self):
        return self._done


class _FakeAgent:
    """Just enough surface for the watchdog: _emit + a _prover_task handle."""

    def __init__(self):
        self.messages: list[str] = []
        self._prover_task = _FakeTask(done=False)
        self._cwd = str(REPO_ROOT)

    async def _emit(self, event_type, data=None):
        if event_type == "message":
            self.messages.append(str(data))


def _write_stub(content: str):
    STUB_ABS.parent.mkdir(parents=True, exist_ok=True)
    STUB_ABS.write_text(content, encoding="utf-8")


def _clear_stub():
    STUB_ABS.unlink(missing_ok=True)


def _fresh_state(names: list[str]) -> WorkflowState:
    st = WorkflowState()
    st.stage = Stage.IDLE
    st.mode = WorkflowMode.PROVING
    st.task = {"theorem_file": "irrelevant.lean", "theorem_names": names}
    st.prover_agent_name = "prover_v5"
    return st


# ── 1. _target_proven against real stub files ────────────────────────────────
def test_target_proven_true_on_proven_stub():
    _write_stub(PROVEN_STUB)
    try:
        agent = _FakeAgent()
        st = _fresh_state(["watchdog_target"])
        got = asyncio.run(_target_proven(st, agent))
        assert got is True, f"expected True on a proven stub, got {got}"
    finally:
        _clear_stub()
    print("✓ test_target_proven_true_on_proven_stub")


def test_target_proven_false_on_sorry_stub():
    _write_stub(SORRY_STUB)
    try:
        agent = _FakeAgent()
        st = _fresh_state(["watchdog_target"])
        got = asyncio.run(_target_proven(st, agent))
        assert got is False, f"expected False on a sorry stub, got {got}"
    finally:
        _clear_stub()
    print("✓ test_target_proven_false_on_sorry_stub")


def test_target_proven_none_without_names():
    """No explicit theorem_names ('prove ALL sorries' mode) → None so the caller
    falls back to the time-based ladder instead of guessing."""
    agent = _FakeAgent()
    st = _fresh_state([])  # empty names
    got = asyncio.run(_target_proven(st, agent))
    assert got is None, f"expected None with no names, got {got}"
    print("✓ test_target_proven_none_without_names")


# ── 2. _prover_watchdog escalation ladder (controlled time + patched oracle) ──
class _Clock:
    """Monkeypatch target for tm.time.monotonic → deterministic elapsed time."""

    def __init__(self, now: float):
        self.now = now

    def monotonic(self):
        return self.now


def _run_watchdog(state, agent, *, now_offset, proven, patch):
    """Drive _prover_watchdog with prover_start=0 and monotonic()=now_offset, a
    stubbed _target_proven verdict, and captured redispatch/cleanup calls."""
    state.prover_start = 1.0  # any positive base; elapsed = now - start
    calls = {"redispatch": 0, "cleanup": 0}

    async def _fake_target_proven(s, a):
        return proven

    async def _fake_dispatch(s, a, resume=False):
        calls["redispatch"] += 1
        # mimic the real dispatch resetting the instance clock
        s.prover_start = clock.now

    async def _fake_cleanup(a):
        calls["cleanup"] += 1

    clock = _Clock(1.0 + now_offset)
    patch(tm, "time", clock)
    patch(tm, "_target_proven", _fake_target_proven)
    patch(tm, "_dispatch_prover", _fake_dispatch)
    patch(tm, "_cleanup_prover", _fake_cleanup)

    result = asyncio.run(_prover_watchdog(state, agent))
    return result, calls


class _Patcher:
    """Tiny monkeypatch helper: records originals and restores on exit."""

    def __init__(self):
        self._saved = []

    def __call__(self, obj, attr, value):
        self._saved.append((obj, attr, getattr(obj, attr)))
        setattr(obj, attr, value)

    def restore(self):
        for obj, attr, val in reversed(self._saved):
            setattr(obj, attr, val)


def test_watchdog_below_warn_keeps_monitoring():
    agent, st = _FakeAgent(), _fresh_state(["watchdog_target"])
    p = _Patcher()
    try:
        result, calls = _run_watchdog(st, agent, now_offset=PROVER_WARN - 10,
                                      proven=False, patch=p)
    finally:
        p.restore()
    assert result is None, "below warn threshold should keep monitoring (None)"
    assert not st.prover_warned
    assert calls["redispatch"] == 0 and calls["cleanup"] == 0
    print("✓ test_watchdog_below_warn_keeps_monitoring")


def test_watchdog_warn_tier_nudges_once():
    agent, st = _FakeAgent(), _fresh_state(["watchdog_target"])
    p = _Patcher()
    try:
        # First tick in the warn window → nudge, set flag, keep monitoring.
        r1, _ = _run_watchdog(st, agent, now_offset=PROVER_WARN + 60,
                              proven=False, patch=p)
        assert r1 is None and st.prover_warned is True
        n_after_first = len([m for m in agent.messages if "watchdog" in m.lower()])
        # Second tick still in the warn window → no second nudge.
        r2, _ = _run_watchdog(st, agent, now_offset=PROVER_WARN + 120,
                              proven=False, patch=p)
        assert r2 is None
        n_after_second = len([m for m in agent.messages if "watchdog" in m.lower()])
        assert n_after_second == n_after_first, "warn tier nudged more than once"
    finally:
        p.restore()
    print("✓ test_watchdog_warn_tier_nudges_once")


def test_watchdog_proven_target_escalates_to_done():
    """Past the redispatch threshold, if the oracle says the target is proven the
    watchdog escalates to PROVER_DONE (success) instead of killing the prover."""
    agent, st = _FakeAgent(), _fresh_state(["watchdog_target"])
    p = _Patcher()
    try:
        result, calls = _run_watchdog(st, agent, now_offset=PROVER_REDISPATCH + 60,
                                      proven=True, patch=p)
    finally:
        p.restore()
    assert result == Transition.PROVER_DONE
    assert st.prover_done is True
    assert calls["redispatch"] == 0 and calls["cleanup"] == 0, "should not kill a done prover"
    print("✓ test_watchdog_proven_target_escalates_to_done")


def test_watchdog_wedged_redispatches_then_terminates():
    """Not proven + restarts remaining → redispatch (MONITOR_TICK). Once restarts
    are exhausted → terminate (force_terminate) and escalate to PROVER_DONE for
    salvage-validation."""
    agent, st = _FakeAgent(), _fresh_state(["watchdog_target"])
    p = _Patcher()
    try:
        # Redispatch tier: should restart while redispatches < MAX_REDISPATCHES.
        for i in range(MAX_REDISPATCHES):
            result, calls = _run_watchdog(st, agent, now_offset=PROVER_REDISPATCH + 60,
                                          proven=False, patch=p)
            assert result == Transition.MONITOR_TICK, f"restart {i} should keep monitoring"
            assert st.redispatches == i + 1
            assert calls["redispatch"] == 1 and calls["cleanup"] == 1
            assert st.prover_warned is False, "warn flag should reset for the new instance"

        # Now restarts are exhausted → terminate path.
        result, calls = _run_watchdog(st, agent, now_offset=PROVER_REDISPATCH + 60,
                                      proven=False, patch=p)
        assert result == Transition.PROVER_DONE, "exhausted restarts should terminate→PROVER_DONE"
        assert st.force_terminate is True
        assert st.prover_done is True
        assert calls["cleanup"] == 1 and calls["redispatch"] == 0, "terminate kills, does not restart"
    finally:
        p.restore()
    print("✓ test_watchdog_wedged_redispatches_then_terminates")


# ── 3. Transition wiring: IDLE + PROVER_DONE routes to VALIDATE (bypass gate) ─
def test_idle_prover_done_routes_to_validate():
    """The watchdog returns PROVER_DONE from the IDLE stage, which must route
    straight to VALIDATE — bypassing the thinking-stage hard gate that would
    otherwise block a TM-initiated prover_done."""
    assert tm.TRANSITIONS[(Stage.IDLE, Transition.PROVER_DONE)] == Stage.VALIDATE
    print("✓ test_idle_prover_done_routes_to_validate")


if __name__ == "__main__":
    print("=" * 60)
    print("test_prover_watchdog")
    print("=" * 60)
    test_target_proven_true_on_proven_stub()
    test_target_proven_false_on_sorry_stub()
    test_target_proven_none_without_names()
    test_watchdog_below_warn_keeps_monitoring()
    test_watchdog_warn_tier_nudges_once()
    test_watchdog_proven_target_escalates_to_done()
    test_watchdog_wedged_redispatches_then_terminates()
    test_idle_prover_done_routes_to_validate()
    print("\n✅ All prover-watchdog tests passed!")
