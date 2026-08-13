"""Tests for the ProofResearcher wiring.

The ProofResearcher is a stateless deep-research agent the guide can request
(the `research` decision) when a lemma is genuinely stuck. It READS the whole
codebase for primitives/patterns/counterexamples but must NOT edit any proof
file — its only writable surface is the per-lemma reports/ dir, enforced by an
ASYMMETRIC hook (read-broad, write-narrow).

These cover the mechanics that are easy to get wrong (no LLM needed):
  * research_workspace_hooks: reads anywhere pass; writes outside reports/ deny;
    writes inside reports/ pass; greps/lean-eval unaffected.
  * the proof_researcher spec loads as a stateless AgentSpec.
  * `research` is in the PROVE-loop decision option set.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_proof_researcher.py
"""

from __future__ import annotations

import asyncio
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.hooks import research_workspace_hooks


REPORTS = "StrataAgent/Sandbox/decomposed/lemma_x/reports"


def _run_hook(hooks, tool_name, tool_input):
    """Drive the PreToolUse hook and return its result dict ({} = allow)."""
    hook = hooks["PreToolUse"][0].hooks[0]
    input_data = {
        "hook_event_name": "PreToolUse",
        "tool_name": tool_name,
        "tool_input": tool_input,
        "cwd": "/proj",
    }
    return asyncio.run(hook(input_data, "tuid", None))


def _denied(result) -> bool:
    """A deny() result carries a permissionDecision == 'deny' somewhere."""
    import json
    return "deny" in json.dumps(result).lower() if result else False


def test_read_anywhere_allowed():
    h = research_workspace_hooks(REPORTS)
    # Reading a core library file — must be allowed (that is the whole point).
    r = _run_hook(h, "Read", {"file_path": "Strata/Transform/CallElim.lean"})
    assert not _denied(r), r
    # Reading a proof file is also fine (read is unrestricted).
    r = _run_hook(h, "Read", {"file_path": "StrataAgent/Sandbox/decomposed/lemma_x/Stub.lean"})
    assert not _denied(r), r
    print("✓ test_read_anywhere_allowed")


def test_grep_and_lean_eval_unrestricted():
    h = research_workspace_hooks(REPORTS)
    for tool, inp in [
        ("Grep", {"pattern": "mapM", "path": "Strata"}),
        ("Bash", {"command": "grep -r bind Strata/Languages"}),
        ("mcp__lean_lsp__lean_run_code", {"code": "example : True := trivial"}),
    ]:
        r = _run_hook(h, tool, inp)
        assert not _denied(r), (tool, r)
    print("✓ test_grep_and_lean_eval_unrestricted")


def test_write_outside_reports_denied():
    h = research_workspace_hooks(REPORTS)
    # Editing the proof file — MUST be denied (researcher never edits proofs).
    r = _run_hook(h, "Edit", {"file_path": "StrataAgent/Sandbox/decomposed/lemma_x/Stub.lean"})
    assert _denied(r), r
    # Writing a new file elsewhere in the Sandbox — denied.
    r = _run_hook(h, "Write", {"file_path": "StrataAgent/Sandbox/decomposed/lemma_x/sneaky.lean"})
    assert _denied(r), r
    print("✓ test_write_outside_reports_denied")


def test_write_inside_reports_allowed():
    h = research_workspace_hooks(REPORTS)
    r = _run_hook(h, "Write", {"file_path": f"{REPORTS}/lemma_x.md"})
    assert not _denied(r), r
    r = _run_hook(h, "Edit", {"file_path": f"{REPORTS}/lemma_x.md"})
    assert not _denied(r), r
    print("✓ test_write_inside_reports_allowed")


def test_spec_loads_stateless():
    import yaml
    from strataswarm._types import AgentSpec
    d = yaml.safe_load(open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/agent_specs/agents/proof_researcher.yaml")))
    spec = AgentSpec(**{k: v for k, v in d.items() if k in AgentSpec.__dataclass_fields__})
    assert spec.stateless is True
    assert spec.name == "proof_researcher"
    # Must NOT have the brute-force / prove tools.
    disallowed = " ".join(str(x) for x in d.get("disallowed_tools", []))
    assert "lean_multi_attempt" in disallowed
    assert "verify_no_sorry" in disallowed
    print("✓ test_spec_loads_stateless")


def test_research_is_a_decision_option():
    """`research` must be offered in the PROVE-loop decision option set."""
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert '"continue", "decompose", "research", "fresh_start", "give_up"' in src, \
        "research not in the prove-loop options"
    assert "_run_researcher" in src
    print("✓ test_research_is_a_decision_option")


def test_guide_decides_after_research():
    """After research, the GUIDE reads the report and makes a proceed/give_up/
    research_more call. An UNCERTAIN report must NOT force give_up — research_more
    sends it back for a deeper pass (never escalate a provable goal on low confidence,
    never blindly proceed on a shaky one)."""
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert 'options=["proceed", "give_up", "research_more"]' in src, \
        "post-research decision must offer proceed/give_up/research_more"
    # research_more branch must re-run the researcher, NOT propagate failure.
    assert 'if r_decision == "research_more":' in src
    # give_up branch still routes to the failure-propagation (→ BigSur) path.
    assert "Post-research give-up" in src
    assert "_propagate_failure_to_parent" in src
    print("✓ test_guide_decides_after_research")


def test_researcher_runs_a_decision_loop():
    """The researcher runs a BigSur-style done/not_done loop (keeps working until
    the report is complete), not a single one-shot pass."""
    import strataswarm.modules.po_v5 as m
    assert hasattr(m, "RESEARCHER_DECISION_ROUNDS") and m.RESEARCHER_DECISION_ROUNDS >= 1
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert "for round_i in range(RESEARCHER_DECISION_ROUNDS)" in src, "no researcher decision loop"
    assert "DECISION:\\s*(done|not_done)" in src or "done | not_done" in src
    print("✓ test_researcher_runs_a_decision_loop")


def test_report_has_recommendation_section():
    """The report format must offer PROCEED / GIVE_UP / UNCERTAIN, and the prompt must
    demand a confidence gate + full-footprint feasibility rigor (the fix for the
    flip-flop where a shaky PROCEED skipped the read/getVars footprint)."""
    import yaml
    d = yaml.safe_load(open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/agent_specs/agents/proof_researcher.yaml")))
    sp = d["system_prompt"]
    assert "RECOMMENDATION" in sp and "PROCEED" in sp and "GIVE_UP" in sp
    # UNCERTAIN must be a first-class outcome (never dress up doubt as confidence).
    assert "UNCERTAIN" in sp, "no UNCERTAIN verdict option"
    # Confidence gate + rigor cues.
    assert "CONFIDENCE GATE" in sp
    assert "getVars" in sp and "footprint" in sp.lower()
    print("✓ test_report_has_recommendation_section")


def test_true_goal_never_gives_up_builds_theory():
    """A TRUE-but-hard goal must NOT be GIVE_UP — the researcher must propose new
    formalizations (a decomposition) and build cumulatively on its prior report.
    This is the fix for the IMO run where it gave up on a goal it knew was true."""
    import yaml
    d = yaml.safe_load(open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/agent_specs/agents/proof_researcher.yaml")))
    sp = " ".join(d["system_prompt"].split()).lower()
    # A true goal is never give-up.
    assert "a true goal is always procee" in sp or "true goal is never" in sp, \
        "no 'true goal is never give_up' rule"
    # Must propose NEW machinery / decomposition for hard goals.
    assert "proposed decomposition" in sp
    assert "hard" in sp and ("propose" in sp or "machinery" in sp)
    # GIVE_UP narrowed to false / human-signature only.
    assert "give_up only if the goal is genuinely false" in sp
    assert "being hard" in sp or "needing new substrate" in sp
    # Cumulative across passes.
    assert "build on your own prior" in sp and "cumulative" in sp

    # And the po_v5 researcher loop must NOT push give_up on hard goals.
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read().lower()
    assert "do not give up on a true goal" in src or "never for 'hard'" in src, \
        "researcher decision loop still allows give_up on hard true goals"
    print("✓ test_true_goal_never_gives_up_builds_theory")


def test_researcher_loop_gates_on_confidence():
    """The done/not_done loop must NOT exit on a merely-complete report — it requires
    HIGH confidence, else it keeps digging (or lands on UNCERTAIN). Guards the
    flip-flop: a low/medium-confidence 'done' must be pushed back."""
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert "CONFIDENCE:" in src, "researcher check does not ask for confidence"
    # Exit condition is done AND high confidence.
    assert 'rdecision == "done" and confidence == "high"' in src, \
        "researcher loop does not gate exit on high confidence"
    # A done-but-not-high answer is explicitly not accepted.
    assert "NOT accepting" in src or "pushing for certainty" in src
    print("✓ test_researcher_loop_gates_on_confidence")


def test_report_hint_surfaces_existing_report_and_verdict():
    """An authored report must be surfaced (path + RECOMMENDATION) into prompts so
    the writer/guide/BigSur act on its verdict instead of re-diagnosing. This is the
    fix for the callElim loop where the report said GIVE_UP early but the give-up→
    BigSur pipeline re-cited the stale build-gate reason ~10× before acting."""
    import tempfile, shutil
    from pathlib import Path
    from strataswarm.modules import po_v5

    class _E:
        workspace = "StrataAgent/Sandbox"
        name = "callElim_overapproximates"

    cwd = Path(tempfile.mkdtemp())
    try:
        # No report yet → no hint, no _existing_report.
        assert po_v5._existing_report(_E(), cwd) is None
        assert po_v5._report_hint(_E(), cwd) == ""

        # Author a report with a RECOMMENDATION line.
        rdir = cwd / "StrataAgent/Sandbox/reports"
        rdir.mkdir(parents=True)
        (rdir / "callElim_overapproximates.md").write_text(
            "# Research\n## Verdict: needs-hypothesis\n"
            "body...\n## RECOMMENDATION: GIVE_UP\nfalse as stated\n")

        found = po_v5._existing_report(_E(), cwd)
        assert found is not None
        paths, rec = found
        assert "StrataAgent/Sandbox/reports/callElim_overapproximates.md" in paths
        assert "GIVE_UP" in rec

        hint = po_v5._report_hint(_E(), cwd)
        assert "StrataAgent/Sandbox/reports/callElim_overapproximates.md" in hint  # path surfaced
        assert "GIVE_UP" in hint                 # verdict is surfaced
        assert "authoritative" in hint.lower()   # instruction to act on it
    finally:
        shutil.rmtree(cwd)
    print("✓ test_report_hint_surfaces_existing_report_and_verdict")


def test_report_hint_surfaces_path_even_without_parseable_verdict():
    """CRUX of the robustness ask: the PATH must be in the prompt even when the
    RECOMMENDATION/Verdict regex does NOT match — the agent can still Read it. Also
    covers a report filename that is NOT the canonical <name>.md."""
    import tempfile, shutil
    from pathlib import Path
    from strataswarm.modules import po_v5

    class _E:
        workspace = "StrataAgent/Sandbox"
        name = "some_lemma"

    cwd = Path(tempfile.mkdtemp())
    try:
        rdir = cwd / "StrataAgent/Sandbox/reports"
        rdir.mkdir(parents=True)
        # Non-canonical name + NO RECOMMENDATION/Verdict line at all.
        (rdir / "notes_on_some_lemma.md").write_text("# findings\njust prose, no verdict header\n")
        found = po_v5._existing_report(_E(), cwd)
        assert found is not None, "must find a report even with a non-canonical name"
        paths, rec = found
        assert paths == ["StrataAgent/Sandbox/reports/notes_on_some_lemma.md"]
        assert rec == ""                          # nothing parseable — fine
        hint = po_v5._report_hint(_E(), cwd)
        assert "StrataAgent/Sandbox/reports/notes_on_some_lemma.md" in hint  # PATH still surfaced
        assert "READ" in hint.upper()
    finally:
        shutil.rmtree(cwd)
    print("✓ test_report_hint_surfaces_path_even_without_parseable_verdict")


def test_report_hint_wired_into_bigsur_and_prompts():
    """The report hint must be injected into BigSur's briefing, the guide's decision
    hint, and the writer's scope note — the three consumers that spun the loop."""
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    # BigSur briefing includes the hint + the anti-spin instruction.
    assert "report_hint = _report_hint(entry, cwd)" in src
    assert "Re-queuing a\n" in src or "only spins this loop" in src
    # guide decision hint + writer scope note both append the hint.
    assert src.count("_report_hint(entry, cwd)") >= 3, \
        "report hint not wired into all three (bigsur/guide/writer)"
    print("✓ test_report_hint_wired_into_bigsur_and_prompts")


if __name__ == "__main__":
    test_read_anywhere_allowed()
    test_grep_and_lean_eval_unrestricted()
    test_write_outside_reports_denied()
    test_write_inside_reports_allowed()
    test_spec_loads_stateless()
    test_research_is_a_decision_option()
    test_guide_decides_after_research()
    test_researcher_runs_a_decision_loop()
    test_report_has_recommendation_section()
    test_true_goal_never_gives_up_builds_theory()
    test_researcher_loop_gates_on_confidence()
    test_report_hint_surfaces_existing_report_and_verdict()
    test_report_hint_surfaces_path_even_without_parseable_verdict()
    test_report_hint_wired_into_bigsur_and_prompts()
    print("\n✅ All ProofResearcher tests passed!")
