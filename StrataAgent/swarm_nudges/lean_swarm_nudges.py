"""Nudge rules for the LeanSwarm proof agents.

Each rule takes a TelemetryView and returns a tip string or None.
RULES is a list of (rule_fn, probability, cooldown_seconds).

All queries are TIME-BASED (seconds), not turn-based.
Evaluated by background NudgeMonitor every 30s.
"""

from v2.src._telemetry import TelemetryView


def edit_without_validate(view: TelemetryView) -> str | None:
    """Agent edited a file but didn't ask ProofValidator in last 2 min."""
    if view._agent.startswith("SearchAgent") or view._agent.startswith("ProofValidator"):
        return None
    if not view.tool_used("Edit", since_seconds=120):
        return None
    if view.message_sent_to("ProofValidator", since_seconds=120):
        return None
    return "Ask ProofValidator to compile-check your changes."


def spawn_without_cea(view: TelemetryView) -> str | None:
    """Prover has proof activity in last 5 min but never checked CEA."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent"):
        return None
    has_activity = (view.tool_used("spawn_agent", since_seconds=300) or
                    view.tool_used("Edit", since_seconds=300) or
                    view.tool_used("Write", since_seconds=300))
    if not has_activity:
        return None
    if view.message_sent_to("CounterExampleAgent", since_seconds=600):
        return None
    return (
        "You have NOT checked with CounterExampleAgent. Send it the theorem "
        "statement to verify soundness before continuing."
    )


def prover_idle_with_subagents(view: TelemetryView) -> str | None:
    """Prover spawned sub-agents but has been idle for 60s+."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent"):
        return None
    # Must have spawned at some point
    if view.tool_used_count("spawn_agent", since_seconds=1800) < 1:
        return None
    # If active recently, don't bother
    if not view.is_idle(idle_seconds=60):
        return None
    return (
        "Check on your sub-agents (use check_sub_agents). "
        "Report progress to TaskManager."
    )


def no_progress_report(view: TelemetryView) -> str | None:
    """Prover hasn't updated TaskManager in 5+ min."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent") or view._agent.startswith("prover_"):
        return None
    # Must have some events (agent has started)
    if view.last_event_time() is None:
        return None
    last_report = view.last_message_sent_to("TaskManager")
    if last_report and view.elapsed_since(last_report) < 300:
        return None
    return "Send a progress update to TaskManager."


def excessive_reads(view: TelemetryView) -> str | None:
    """Agent read 5+ files in last 2 min — should ask SearchAgent."""
    if view._agent.startswith("SearchAgent"):
        return None
    if view.tool_used_count("Read", since_seconds=120) < 5:
        return None
    if view.message_sent_to("SearchAgent", since_seconds=120):
        return None
    return "Ask SearchAgent instead of reading files yourself."


def stuck_same_error(view: TelemetryView) -> str | None:
    """Agent got 3+ error messages in last 5 min."""
    errors = view.messages_containing("error", since_seconds=300)
    if len(errors) < 3:
        return None
    if view.message_sent_to("SearchAgent", since_seconds=120):
        return None
    return "Try a different approach. Ask SearchAgent for alternative lemmas."


def no_broadcast_after_results(view: TelemetryView) -> str | None:
    """Prover received 2+ results from children in last 5 min but didn't broadcast."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent"):
        return None
    results = view.message_received_from("prover_*", since_seconds=300)
    if len(results) < 2:
        return None
    if view.tool_used("broadcast", since_seconds=300):
        return None
    return "Broadcast useful findings to your sub-agents."


def compile_before_submit(view: TelemetryView) -> str | None:
    """Sub-agent edited in last 2 min but didn't compile-check."""
    if view.agent_is_super():
        return None
    if not view.tool_used("Edit", since_seconds=120):
        return None
    if view.message_sent_to("ProofValidator", since_seconds=120):
        return None
    return "Ask ProofValidator to compile-check before reporting done."


def received_but_not_replied(view: TelemetryView) -> str | None:
    """Agent has pending replies overdue by 5+ min."""
    overdue = view.overdue_replies(timeout_seconds=300)
    if not overdue:
        return None
    return f"You have unanswered messages from: {', '.join(overdue)}. Reply to them now."


def prover_proving_itself(view: TelemetryView) -> str | None:
    """Prover edited or validated in last 5 min without spawning."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent"):
        return None
    edited = view.tool_used("Edit", since_seconds=300)
    validated = view.message_sent_to("ProofValidator", since_seconds=300)
    if not edited and not validated:
        return None
    if view.tool_used("spawn_agent", since_seconds=600):
        return None
    return (
        "STOP proving directly. Spawn a prover_* sub-agent instead. "
        "Write the theorem + context to a file in Sandbox/, then call spawn_agent."
    )


def consult_lemma_proposer(view: TelemetryView) -> str | None:
    """Prover should discuss proof strategy with LemmaProposer before spawning."""
    if view._agent != "Prover":
        return None
    if view.is_idle(idle_seconds=120):
        return None
    if view.message_sent_to("LemmaProposer", since_seconds=600):
        return None
    if not (view.tool_used("spawn_agent", since_seconds=600) or
            view.tool_used("Write", since_seconds=300)):
        return None
    return (
        "Discuss proof strategy with LemmaProposer before spawning more sub-agents. "
        "Get a high-level decomposition and approach suggestions first."
    )


# Registry: (rule_function, probability, cooldown_seconds)
RULES = [
    (edit_without_validate,      0.5, 120),    # 2 min cooldown
    (spawn_without_cea,          0.9, 180),    # 3 min cooldown
    (prover_idle_with_subagents, 1.0, 60),     # 1 min cooldown — keeps Prover alive
    (consult_lemma_proposer,     0.7, 300),    # 5 min cooldown — only for Prover
    (no_progress_report,         0.8, 300),    # 5 min cooldown
    (excessive_reads,            0.7, 120),    # 2 min cooldown
    (stuck_same_error,           0.5, 180),    # 3 min cooldown
    (no_broadcast_after_results, 0.3, 240),    # 4 min cooldown
    (compile_before_submit,      0.5, 90),     # 1.5 min cooldown
    (received_but_not_replied,   1.0, 120),    # 2 min cooldown — always fires
    (prover_proving_itself,      0.9, 90),     # 1.5 min cooldown
]
