"""Verifier for goal_analyzer agent output.

Checks that the goal_analyzer produced a valid, justified assessment.
This is a lightweight verifier — the assessment is advisory, so we mainly
check structural validity (did it produce the right fields, is the reasoning
non-empty, does the assessment value make sense).

Usage with verified_loop:
    verify_fn = make_goal_analyzer_verifier()
    outcome = await verified_loop(
        agent_ctx=analyzer,
        initial_input={"goal_type": ..., "local_context": ...},
        verify=verify_fn,
        max_rounds=2,
        result_type=GoalAssessment,
    )
"""

from __future__ import annotations

from dataclasses import dataclass, field


VALID_ASSESSMENTS = {"provable", "needs_strengthening", "contradictory", "bad_goal"}


@dataclass
class GoalAssessment:
    """Structured output from goal_analyzer."""
    assessment: str = "provable"
    reasoning: str = ""
    suggestion: str = ""


def verify_goal_assessment(output: GoalAssessment | None) -> str | None:
    """Verify the goal_analyzer's output is well-formed.

    Returns None if valid, error string if not.
    """
    if output is None:
        return "No structured output produced. Call StructuredOutput with assessment, reasoning, suggestion."

    if output.assessment not in VALID_ASSESSMENTS:
        return (
            f"Invalid assessment '{output.assessment}'. "
            f"Must be one of: {sorted(VALID_ASSESSMENTS)}"
        )

    if not output.reasoning or len(output.reasoning) < 10:
        return "Reasoning is too short or empty. Explain WHY you reached this assessment."

    if not output.suggestion:
        return "Suggestion is empty. Provide a concrete next step."

    return None


def make_goal_analyzer_verifier(output_holder: list) -> callable:
    """Create a verify function for verified_loop.

    The output_holder is a mutable list that will contain [GoalAssessment]
    after the agent runs (set by the caller after parsing output).

    Usage:
        holder = [None]
        verify_fn = make_goal_analyzer_verifier(holder)
        # After agent runs:
        holder[0] = parsed_output
        # verify_fn() checks holder[0]
    """
    def verify() -> str | None:
        output = output_holder[0] if output_holder else None
        return verify_goal_assessment(output)

    return verify
