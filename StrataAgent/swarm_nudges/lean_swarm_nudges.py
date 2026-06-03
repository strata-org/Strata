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
# CATEGORY 2: DONE REMINDER (for spawned agents only)
# =============================================================================

def done_reminder(view: TelemetryView) -> str | None:
    """Remind spawned agents to call done() or send a status update if idle."""
    # Only target spawned agents (not top-level, not service agents, not virtual)
    if view._is_reply_only:
        return None
    # Skip all top-level and virtual agents
    base_agents = {
        "TaskManager", "Editor", "Prover", "CounterExampleAgent", "user",
    }
    if view._agent in base_agents:
        return None
    if view._agent.startswith("SearchAgent") or view._agent.startswith("ProofValidator"):
        return None
    if view._agent.startswith("LeanSyntax") or view._agent.startswith("LemmaProposer"):
        return None
    if view._agent.startswith("ProofCondenser"):
        return None
    # Silent for 5+ min
    if not view.is_idle(idle_seconds=300):
        return None
    idle = view.seconds_since_last_event()
    if idle == float("inf"):
        return None
    elapsed_min = int(view.agent_elapsed_minutes())
    cost = view.agent_cost_usd()
    cost_str = f" (cost: ${cost:.3f})" if cost else ""
    return (
        f"You have been idle for {int(idle)}s (running {elapsed_min} min{cost_str}). "
        f"Are you done? If YES → call done(summary='<your results>') to exit cleanly. "
        f"If NO → send a status update to your parent explaining what you're waiting for. "
        f"If STUCK → ask LemmaProposer or SearchAgent for a different approach."
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
# CATEGORY 5: RESOURCE MONITORING (CPU/RAM alerts to TaskManager)
# =============================================================================

def resource_alarm(view: TelemetryView) -> str | None:
    """Alert TaskManager about high system resource usage."""
    if view._agent != "TaskManager":
        return None
    try:
        import psutil
        # System-wide metrics
        cpu_pct = psutil.cpu_percent(interval=0)
        mem = psutil.virtual_memory()
        mem_pct = mem.percent

        # Only fire if resources are stressed
        if cpu_pct < 85 and mem_pct < 80:
            return None

        # Find top memory consumers (Claude/lake processes)
        top_procs = []
        for proc in psutil.process_iter(['pid', 'name', 'memory_info', 'cmdline']):
            try:
                info = proc.info
                cmd = " ".join(info.get('cmdline', [])[:3]) if info.get('cmdline') else info.get('name', '')
                if any(k in cmd for k in ['claude', 'lake', 'lean', 'node']):
                    mem_mb = (info['memory_info'].rss / 1024 / 1024) if info.get('memory_info') else 0
                    if mem_mb > 100:
                        top_procs.append((cmd[:60], mem_mb))
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue

        top_procs.sort(key=lambda x: -x[1])
        top_str = "\n".join(f"  - {name}: {mb:.0f} MB" for name, mb in top_procs[:5])

        parts = []
        if cpu_pct >= 85:
            parts.append(f"CPU at {cpu_pct:.0f}%")
        if mem_pct >= 80:
            parts.append(f"RAM at {mem_pct:.0f}% ({mem.used // (1024**3)}GB / {mem.total // (1024**3)}GB)")

        return (
            f"RESOURCE ALERT: {', '.join(parts)}.\n"
            f"Top consumers:\n{top_str}\n"
            f"Consider: kill idle/stuck sub-agents, reduce parallelism, or wait for compilations to finish."
        )
    except ImportError:
        return None
    except Exception:
        return None


# =============================================================================
# CATEGORY 6: FORCE SPAWNING (coordinators must delegate)
# =============================================================================

def force_spawn_reminder(view: TelemetryView) -> str | None:
    """Force coordinators to spawn children if they haven't in 10+ min."""
    if not view.agent_is_super():
        return None
    if view._is_reply_only:
        return None
    if view._agent in ("TaskManager", "Editor", "user"):
        return None
    elapsed_min = view.agent_elapsed_minutes()
    if elapsed_min < 10:
        return None
    spawn_count = view.tool_used_count("spawn_agent", since_seconds=600)
    if spawn_count >= 1:
        return None
    cost = view.agent_cost_usd()
    cost_str = f" (cost: ${cost:.3f})" if cost else ""
    return (
        f"You have been working for {int(elapsed_min)} min without spawning any children{cost_str}. "
        f"You are a COORDINATOR — you should NOT be writing proofs yourself. "
        f"Decompose your current work into independent pieces and spawn sub-agents NOW. "
        f"Even small pieces (5-10 lines) should be delegated to leaf agents (recursive=false)."
    )


# =============================================================================
# REGISTRY
# =============================================================================

# (rule_function, probability, cooldown_seconds)
RULES = [
    # Category 1: Status informer (for SuperAgents only)
    (super_agent_child_status,       1.0, 300),   # 5 min cooldown
    (main_prover_report_to_tm,       1.0, 900),   # 15 min cooldown

    # Category 2: Done reminder (spawned agents only — not service, not top-level)
    (done_reminder,                  1.0, 300),   # 5 min cooldown

    # Category 3: Handoff reminders (token-based, super agents only)
    (handoff_warning_context_60,     1.0, 300),   # 5 min cooldown — early warning
    (handoff_urgent_context_80,      1.0, 120),   # 2 min cooldown — urgent, keep nagging
    (sub_agent_context_high,         1.0, 180),   # 3 min cooldown — non-super spawned agents

        # Category 5: Resource monitoring (alerts TaskManager)
    (resource_alarm,                 1.0, 120),   # 2 min cooldown — check frequently

    # Category 6: Force spawning (coordinators must delegate)
    (force_spawn_reminder,           1.0, 600),   # 10 min cooldown

    # Category 7: Violation alerts (spawned agents + CEA only)
    (cea_searching_not_testing,      1.0, 300),
    (edit_without_compile,           1.0, 300),
    (agent_using_bash_when_disallowed, 1.0, 180),  # 3 min — catch early
]


# =============================================================================
# HOOKS: Domain-specific recovery callbacks
# =============================================================================

async def _kill_lean_mcp_processes() -> list[dict]:
    """Kill all lean-lsp-mcp and lean --server processes. Returns list of killed."""
    import signal
    try:
        import psutil
    except ImportError:
        return []
    killed = []
    for proc in psutil.process_iter(['pid', 'cmdline']):
        try:
            cmd = " ".join(proc.info.get('cmdline', []) or [])
            if "lean-lsp-mcp" in cmd or "lean --server" in cmd:
                proc.send_signal(signal.SIGTERM)
                killed.append({"pid": proc.info['pid'], "cmd": cmd[:80]})
        except Exception:
            continue
    return killed


async def _reconnect_all_validators(swarm) -> list[str]:
    """Disconnect + reconnect all ProofValidator backends."""
    reconnected = []
    registry = swarm._registry
    for name, backend in list(registry.backends.items()):
        if not name.startswith("ProofValidator"):
            continue
        try:
            await backend.disconnect()
            config = getattr(backend, '_config', None)
            if config:
                await backend.connect(config)
                reconnected.append(name)
        except Exception:
            pass
    return reconnected


async def ON_STALLED_SERVICE(swarm, agent_name: str) -> None:
    """Called when any agent appears stalled (overdue replies or stall event).
    For ProofValidator: kill MCP + reconnect all replicas.
    For other agents: disconnect + reconnect that specific agent."""
    import logging
    logger = logging.getLogger("strataswarm.nudge")

    if agent_name.startswith("ProofValidator"):
        # ProofValidator stall = likely dead MCP. Kill all + reconnect all replicas.
        killed = await _kill_lean_mcp_processes()
        logger.info(f"[LEAN MCP] Stalled validator '{agent_name}' — killed {len(killed)} MCP processes")
        reconnected = await _reconnect_all_validators(swarm)
        logger.info(f"[LEAN MCP] Reconnected {len(reconnected)} validators: {reconnected}")
    else:
        # Non-validator stall: disconnect + reconnect that specific agent's backend
        registry = swarm._registry
        backend = registry.backends.get(agent_name)
        if backend:
            try:
                await backend.disconnect()
                config = getattr(backend, '_config', None)
                if config:
                    await backend.connect(config)
                    logger.info(f"[STALL RECOVERY] Reconnected '{agent_name}'")
            except Exception as e:
                logger.error(f"[STALL RECOVERY] Failed to reconnect '{agent_name}': {e}")


async def ON_MCP_RESTART(swarm) -> dict:
    """Called from /api/mcp/restart endpoint. Same logic as stall recovery."""
    import logging
    logger = logging.getLogger("strataswarm.nudge")
    killed = await _kill_lean_mcp_processes()
    logger.info(f"[LEAN MCP] Manual restart: killed {len(killed)} processes")
    reconnected = await _reconnect_all_validators(swarm)
    logger.info(f"[LEAN MCP] Manual restart: reconnected {len(reconnected)} validators")
    return {"killed": killed, "reconnected": reconnected}
