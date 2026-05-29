"""Nudge rules for the LeanSwarm proof agents.

Four categories:
1. STATUS INFORMER — tells SuperAgents about their children's state (factual)
2. GENTLE POKE — asks agents to self-report or take action (infrequent)
3. HANDOFF REMINDER — tells super agents to hand off before context fills
4. VIOLATION ALERT — fires on sustained misuse patterns with evidence (rare, undeniable)

All messages are dynamic and include telemetry evidence.
Rules fire for ALL agents (including spawned sub-agents), not just the original set.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from v2.src._telemetry import TelemetryView


# =============================================================================
# CATEGORY 1: STATUS INFORMER (for SuperAgents about their children)
# =============================================================================

def super_agent_child_status(view: TelemetryView) -> str | None:
    """Inform SuperAgent about its children's status. Factual, not advisory."""
    if not view.agent_is_super():
        return None
    if view._agent.startswith("SearchAgent"):
        return None
    # Must have spawned children
    spawn_count = view.tool_used_count("spawn_agent", since_seconds=3600)
    if spawn_count < 1:
        return None
    idle_seconds = view.seconds_since_last_event()
    last_msg_from_children = view.message_received_from("prover_*", since_seconds=600)
    last_sent_to_tm = view.last_message_sent_to("TaskManager")
    tm_elapsed = view.elapsed_since(last_sent_to_tm) if last_sent_to_tm else 9999

    # Only fire if agent has been idle 5+ min
    if idle_seconds < 300:
        return None

    elapsed_min = int(view.agent_elapsed_minutes())
    cost = view.agent_cost_usd()
    cost_str = f"${cost:.3f}" if cost else "unknown"

    msg = (
        f"STATUS: You have been idle for {int(idle_seconds)}s. "
        f"Running for {elapsed_min} min total (cost: {cost_str}). "
        f"You spawned {spawn_count} sub-agent(s) this session. "
        f"Messages from children in last 10 min: {len(last_msg_from_children)}. "
        f"Last report to TaskManager: {int(tm_elapsed)}s ago. "
        f"Consider: check_sub_agents for their status, or report progress to TaskManager."
    )
    return msg


def main_prover_report_to_tm(view: TelemetryView) -> str | None:
    """Main Prover should report to TaskManager periodically."""
    if view._agent != "Prover":
        return None
    if view.last_event_time() is None:
        return None
    last_report = view.last_message_sent_to("TaskManager")
    if last_report and view.elapsed_since(last_report) < 900:  # 15 min
        return None
    idle = view.seconds_since_last_event()
    if idle == float("inf"):
        return None
    elapsed_min = int(view.agent_elapsed_minutes())
    cost = view.agent_cost_usd()
    cost_str = f"${cost:.3f}" if cost else "unknown"
    last_report_str = f"{int(view.elapsed_since(last_report))}s" if last_report else "never"
    msg = (
        f"STATUS: You haven't reported to TaskManager in {last_report_str}. "
        f"Idle for {int(idle)}s. Running {elapsed_min} min (cost: {cost_str}). "
        f"Send a brief progress update."
    )
    return msg


# =============================================================================
# CATEGORY 2: GENTLE POKE (ask agents to self-report or take action)
# =============================================================================

def poke_silent_child(view: TelemetryView) -> str | None:
    """Poke a sub-agent that's been silent for 8+ min — ask it to report to parent."""
    if view.agent_is_super():
        return None
    if view._is_reply_only:
        return None
    # Target any non-service agent (including spawned sub-agents)
    if view._agent.startswith("SearchAgent") or view._agent.startswith("ProofValidator"):
        return None
    if view._agent.startswith("LeanSyntax"):
        return None
    if view._agent in ("TaskManager", "Editor", "ProofCondenser"):
        return None
    # Silent for 8+ min
    if not view.is_idle(idle_seconds=480):
        return None
    idle = view.seconds_since_last_event()
    if idle == float("inf"):
        return None  # No events yet — agent hasn't started
    elapsed_min = int(view.agent_elapsed_minutes())
    cost = view.agent_cost_usd()
    cost_str = f" (cost so far: ${cost:.3f})" if cost else ""
    return (
        f"You have been silent for {int(idle)}s (running {elapsed_min} min total{cost_str}). "
        f"Send your parent a brief status: what you're working on, "
        f"whether you're stuck, or if you're done."
    )


def poke_idle_service_agent(view: TelemetryView) -> str | None:
    """Poke a service agent that has overdue replies but seems stuck."""
    if not view._is_reply_only:
        return None
    overdue = view.overdue_replies(timeout_seconds=180)
    if not overdue:
        return None
    idle = view.seconds_since_last_event()
    if idle == float("inf") or idle < 120:
        return None
    return (
        f"You have {len(overdue)} overdue request(s) from: {', '.join(overdue)}. "
        f"Idle for {int(idle)}s. Process their requests now."
    )


# =============================================================================
# CATEGORY 3: HANDOFF REMINDER (based strictly on token usage from backend)
# =============================================================================

def handoff_warning_context_60(view: TelemetryView) -> str | None:
    """Warn super agents at 60% context — start writing handoff notes."""
    if not view.agent_is_super():
        return None
    pct = view.context_percentage()
    if pct is None or pct < 60 or pct >= 80:
        return None
    return (
        f"HANDOFF PREP: Your context is {pct:.0f}% full. "
        f"Start writing a handoff file in your workspace (e.g., 'handoff.md') with: "
        f"what's done, what's in progress, what's left, what approaches worked/failed. "
        f"You can keep working, but prepare now so you can call designate_successor cleanly."
    )


def handoff_urgent_context_80(view: TelemetryView) -> str | None:
    """Urgent: context at 80%+ — hand off immediately."""
    if not view.agent_is_super():
        return None
    pct = view.context_percentage()
    if pct is None or pct < 80:
        return None
    return (
        f"HANDOFF NOW: Your context is {pct:.0f}% full — CRITICAL. "
        f"Write handoff.md in your workspace NOW and call designate_successor('handoff.md'). "
        f"Your successor will automatically read the handoff file and continue your work. "
        f"Do NOT keep working — you will lose the ability to write a coherent handoff."
    )


def sub_agent_context_high(view: TelemetryView) -> str | None:
    """Sub-agents at 70%+ context should report to parent immediately."""
    if view.agent_is_super():
        return None
    if view._is_reply_only:
        return None
    if view._agent in ("TaskManager", "Editor"):
        return None
    pct = view.context_percentage()
    if pct is None or pct < 70:
        return None
    return (
        f"CONTEXT ALERT: Your context is {pct:.0f}% full. "
        f"Report to your parent NOW: what you've proved, what file has the result, "
        f"what's left. Your parent can spawn a fresh agent to continue if needed. "
        f"Do not keep going until context runs out silently."
    )


# =============================================================================
# CATEGORY 4: VIOLATION ALERTS (sustained misuse, with evidence)
# =============================================================================

def validator_browsing_not_validating(view: TelemetryView) -> str | None:
    """ProofValidator is reading files excessively without using validation tools."""
    if not view._agent.startswith("ProofValidator"):
        return None
    read_count = view.tool_used_count("Read", since_seconds=300)
    bash_count = view.tool_used_count("Bash", since_seconds=300)
    lean_goal_count = view.tool_used_count("mcp__lean_lsp__lean_goal", since_seconds=300)
    lean_verify_count = view.tool_used_count("mcp__lean_lsp__lean_verify", since_seconds=300)
    validation_calls = bash_count + lean_goal_count + lean_verify_count
    if read_count < 8:
        return None
    if validation_calls >= 2:
        return None
    return (
        f"VIOLATION: You have called Read {read_count} times but only "
        f"{validation_calls} validation tools (lake lean: {bash_count}, "
        f"lean_goal: {lean_goal_count}, lean_verify: {lean_verify_count}) "
        f"in the last 5 min. Your job is VALIDATION — use lake lean, lean_goal, "
        f"or lean_verify instead of browsing files."
    )


def cea_searching_not_testing(view: TelemetryView) -> str | None:
    """CEA using Bash/grep to search instead of writing counterexample files."""
    if not view._agent.startswith("CounterExampleAgent"):
        return None
    bash_count = view.tool_used_count("Bash", since_seconds=300)
    write_count = view.tool_used_count("Write", since_seconds=300)
    if bash_count < 5:
        return None
    if write_count >= 1:
        return None
    msg_to_search = view.message_sent_to("SearchAgent", since_seconds=300)
    return (
        f"VIOLATION: You used Bash {bash_count} times but wrote 0 temp files "
        f"in the last 5 min. {'Also no messages to SearchAgent.' if not msg_to_search else ''} "
        f"Your job is to WRITE counterexample files and compile them. "
        f"For definitions, ask SearchAgent. For testing, Write a .lean file first."
    )


def reply_only_not_replying(view: TelemetryView) -> str | None:
    """Reply-only agent has overdue replies — with evidence."""
    if not view._is_reply_only:
        return None
    overdue = view.overdue_replies(timeout_seconds=300)
    if not overdue:
        return None
    idle = view.seconds_since_last_event()
    if idle == float("inf"):
        return None
    return (
        f"OVERDUE REPLIES: {', '.join(overdue)} have been waiting >5 min for your response. "
        f"You have been idle for {int(idle)}s. Process their requests now."
    )


def edit_without_compile(view: TelemetryView) -> str | None:
    """Agent edited multiple times without compile-checking — sustained pattern."""
    if view._agent.startswith("SearchAgent") or view._agent.startswith("ProofValidator"):
        return None
    if view._agent.startswith("LeanSyntax"):
        return None
    if view._is_reply_only:
        return None
    edit_count = view.tool_used_count("Edit", since_seconds=300)
    if edit_count < 3:
        return None
    if view.message_sent_to("ProofValidator", since_seconds=300):
        return None
    return (
        f"You have called Edit {edit_count} times in the last 5 min without "
        f"a single compile-check via ProofValidator. Edits without validation "
        f"accumulate errors. Send your file to ProofValidator now."
    )


def agent_using_bash_when_disallowed(view: TelemetryView) -> str | None:
    """Sub-agent attempting filesystem access when it should use SearchAgent."""
    # Only target spawned sub-agents (prover_* pattern or anything not in the base set)
    base_agents = {
        "TaskManager", "Editor", "Prover", "SearchAgent", "ProofValidator",
        "CounterExampleAgent", "LemmaProposer", "ProofCondenser", "LeanSyntaxAgent"
    }
    if view._agent in base_agents or view._agent.startswith("SearchAgent") or view._agent.startswith("ProofValidator"):
        return None
    if view._is_reply_only:
        return None
    bash_count = view.tool_used_count("Bash", since_seconds=300)
    if bash_count < 2:
        return None
    msg_to_search = view.message_sent_to("SearchAgent", since_seconds=300)
    return (
        f"VIOLATION: You used Bash {bash_count} times in the last 5 min. "
        f"You do NOT have shell access for file browsing. "
        f"{'You also never asked SearchAgent.' if not msg_to_search else ''} "
        f"For ANY codebase info → send_message(to='SearchAgent', message='<your question>'). "
        f"SearchAgent is your ONLY way to learn about the codebase."
    )


# =============================================================================
# REGISTRY
# =============================================================================

# (rule_function, probability, cooldown_seconds)
RULES = [
    # Category 1: Status informer (factual, for SuperAgents)
    (super_agent_child_status,       1.0, 300),   # 5 min cooldown
    (main_prover_report_to_tm,       1.0, 900),   # 15 min cooldown

    # Category 2: Gentle poke
    (poke_silent_child,              1.0, 480),   # 8 min cooldown
    (poke_idle_service_agent,        1.0, 300),   # 5 min cooldown

    # Category 3: Handoff reminders (token-based, from backend context %)
    (handoff_warning_context_60,     1.0, 300),   # 5 min cooldown — early warning
    (handoff_urgent_context_80,      1.0, 120),   # 2 min cooldown — urgent, keep nagging
    (sub_agent_context_high,         1.0, 180),   # 3 min cooldown — sub-agents report up

    # Category 4: Violation alerts (sustained misuse, with evidence)
    (validator_browsing_not_validating, 1.0, 300),
    (cea_searching_not_testing,      1.0, 300),
    (reply_only_not_replying,        1.0, 300),
    (edit_without_compile,           1.0, 300),
    (agent_using_bash_when_disallowed, 1.0, 180),  # 3 min — catch early
]
