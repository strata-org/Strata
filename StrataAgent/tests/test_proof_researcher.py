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
    """After research, the GUIDE reads the report and makes a proceed/give_up call
    (the researcher only advises; the guide owns the decision → BigSur on give_up)."""
    src = open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/modules/po_v5.py")).read()
    assert 'options=["proceed", "give_up"]' in src, "no post-research guide decision"
    # give_up branch must route to the failure-propagation (→ BigSur) path.
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
    """The researcher's report format must end with a RECOMMENDATION the guide keys on."""
    import yaml
    d = yaml.safe_load(open(os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "strataswarm/agent_specs/agents/proof_researcher.yaml")))
    sp = d["system_prompt"]
    assert "RECOMMENDATION" in sp and "PROCEED" in sp and "GIVE_UP" in sp
    print("✓ test_report_has_recommendation_section")


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
    print("\n✅ All ProofResearcher tests passed!")
