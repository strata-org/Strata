"""Tests for the writer's run_code-without-edit nudge (hooks.run_code_nudge_hooks
+ writer_nudge_hooks).

Background — cost analysis of the quant_coalesce_denote runs: the proof writer
iterated the whole proof in `lean_run_code` (293 probes in one run) instead of
editing the file (188 Edits), while bare Claude solved the same goal with 82
run_code + 25 Edit. Every run_code ships its snippet + full compiler output into
the transcript, re-billed as input tokens every later turn → super-linear cost,
plus divergence risk (standalone snippet ≠ the real file's imports/elaboration).

The nudge is a PostToolUse hook: it counts consecutive probe calls
(lean_run_code / lean_multi_attempt) since the last file edit and, once the count
crosses a threshold, injects a passive reminder to commit to the file. An
Edit/Write resets the streak.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_writer_nudge.py
"""

from __future__ import annotations

import asyncio
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules import hooks


class _Ref:
    """Fake agent_ref: carries the per-agent counter attr + a no-op _emit."""
    async def _emit(self, *a, **k):
        return None


def _mk(threshold=3):
    ref = _Ref()
    h = hooks.run_code_nudge_hooks(agent_ref=ref, threshold=threshold)
    hook = h["PostToolUse"][0].hooks[0]

    def call(tool, resp=""):
        return asyncio.run(hook(
            {"hook_event_name": "PostToolUse", "tool_name": tool, "tool_response": resp},
            "tid", None))

    return call


def _fired(result) -> bool:
    return bool(result) and "additionalContext" in str(result)


def test_nudge_fires_only_at_threshold():
    call = _mk(threshold=3)
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))   # 1
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))   # 2
    assert _fired(call("mcp__lean_lsp__lean_run_code"))       # 3 → nudge
    print("✓ test_nudge_fires_only_at_threshold")


def test_edit_resets_the_streak():
    call = _mk(threshold=3)
    call("mcp__lean_lsp__lean_run_code")
    call("mcp__lean_lsp__lean_run_code")
    call("Edit")                                              # reset
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))   # 1 again
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))   # 2
    assert _fired(call("mcp__lean_lsp__lean_run_code"))       # 3 → nudge
    print("✓ test_edit_resets_the_streak")


def test_multi_attempt_counts_write_resets():
    """lean_multi_attempt is also a probe; Write also resets the streak."""
    call = _mk(threshold=2)
    assert not _fired(call("mcp__lean_lsp__lean_multi_attempt"))  # 1
    assert _fired(call("mcp__lean_lsp__lean_multi_attempt"))      # 2 → nudge
    call("Write")                                                # reset
    assert not _fired(call("mcp__lean_lsp__lean_multi_attempt"))  # 1 again
    print("✓ test_multi_attempt_counts_write_resets")


def test_non_probe_tools_do_not_count():
    """A read/diagnostic between probes must NOT advance the streak (only probes do),
    and must NOT reset it either (only edits reset)."""
    call = _mk(threshold=2)
    call("mcp__lean_lsp__lean_run_code")                          # 1
    assert not _fired(call("mcp__lean_lsp__lean_diagnostic_messages"))  # neutral
    assert _fired(call("mcp__lean_lsp__lean_run_code"))          # 2 → nudge (streak kept)
    print("✓ test_non_probe_tools_do_not_count")


def test_nudge_re_arms_after_firing():
    call = _mk(threshold=2)
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))
    assert _fired(call("mcp__lean_lsp__lean_run_code"))          # fires, resets
    assert not _fired(call("mcp__lean_lsp__lean_run_code"))      # counts again from 0
    assert _fired(call("mcp__lean_lsp__lean_run_code"))          # fires again
    print("✓ test_nudge_re_arms_after_firing")


def test_writer_nudge_combines_both_hooks():
    """The writer gets snapshot-tip AND run_code-nudge merged into one PostToolUse
    matcher list (both fire independently)."""
    c = hooks.writer_nudge_hooks(agent_ref=_Ref())
    assert "PostToolUse" in c
    assert len(c["PostToolUse"]) == 2, "expected snapshot tip + run_code nudge"
    print("✓ test_writer_nudge_combines_both_hooks")


def test_turn_range_widened():
    """MIN/MAX chunk turns widened to 120-160 (fewer guide round-trips per chunk),
    paired with the nudge so the extra turns aren't spent bloating run_code."""
    from strataswarm.modules import po_v5
    assert po_v5.MIN_CHUNK_TURNS == 120, po_v5.MIN_CHUNK_TURNS
    assert po_v5.MAX_CHUNK_TURNS == 160, po_v5.MAX_CHUNK_TURNS
    print("✓ test_turn_range_widened")


def test_edit_forward_not_revert_guidance():
    """The writer must be told to EDIT FORWARD through transient errors (not revert to
    green after every error) and to restore-from-snapshot only when truly stuck — in
    BOTH the yaml system prompt and the per-chunk prompt. This is the fix for the
    writer wasting turns keeping the file compilable after every keystroke."""
    import yaml as _yaml
    d = _yaml.safe_load(open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/agent_specs/agents/proof_writer_v2.yaml")))
    sp = " ".join(d["system_prompt"].split())
    assert "EDITING FORWARD" in sp
    assert "not after every keystroke" in sp.lower()
    assert "read_snapshot to restore" in sp
    # The old "MUST compile at all times" mandate must be gone.
    assert "compile at all times" not in sp.lower(), "stale must-compile-always mandate remains"

    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert "EDIT FORWARD" in src, "per-chunk prompt not updated to edit-forward"
    assert "File MUST compile (sorry allowed)." not in src, "stale per-chunk must-compile remains"
    print("✓ test_edit_forward_not_revert_guidance")


def _main():
    for fn in (
        test_nudge_fires_only_at_threshold,
        test_edit_resets_the_streak,
        test_multi_attempt_counts_write_resets,
        test_non_probe_tools_do_not_count,
        test_nudge_re_arms_after_firing,
        test_writer_nudge_combines_both_hooks,
        test_turn_range_widened,
        test_edit_forward_not_revert_guidance,
    ):
        fn()
    print("ALL WRITER-NUDGE TESTS PASSED")


if __name__ == "__main__":
    _main()
