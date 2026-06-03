"""Hybrid TaskManager v2: simplified transition-based state machine.

Design principles:
- idle: thin message dispatcher — blocks on inbox, hands off to thinking
- thinking: full agent session (multi-turn, tools, messaging) — picks exit transition
- hard states: code-only, no LLM, instant execution
- Pattern: hard state → idle (wait) → thinking (full agent) → hard state → ...
"""

from __future__ import annotations

import shutil
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, TypeVar

T = TypeVar("T")

MAX_STAGE_RETRIES = 5
PROVER_TIMEOUT = 86400  # 24 hours — prover manages its own budget/time
MONITOR_INTERVAL = 600  # 10 min — idle timeout during monitoring for periodic re-ping


# ─── Transitions (read this to understand the workflow) ───────────────────────

TRANSITIONS: dict[tuple[str, str], str] = {
    # PARSE: extract task from raw_input
    ("parse", "parsed"):              "setup",
    ("parse", "need_clarification"):  "idle",

    # IDLE: wait for any message, then hand off to thinking
    ("idle", "message_received"):     "thinking",
    ("idle", "monitor_tick"):         "thinking",   # timeout during proving → thinking can ping

    # THINKING: full agent session — exits are filtered by origin_stage
    ("thinking", "new_task"):         "parse",
    ("thinking", "ready"):            "setup",
    ("thinking", "proceed"):          "dispatch",
    ("thinking", "prover_done"):      "validate",
    ("thinking", "respond"):          "idle",

    # SETUP: copy file to Sandbox
    ("setup", "ready"):               "soundness",
    ("setup", "file_not_found"):      "idle",

    # SOUNDNESS: CEA check
    ("soundness", "sound"):           "dispatch",
    ("soundness", "skipped"):         "dispatch",
    ("soundness", "unsound"):         "idle",

    # DISPATCH: launch prover, then wait
    ("dispatch", "dispatched"):       "idle",

    # VALIDATE: deep proof check
    ("validate", "passed"):           "report",
    ("validate", "failed"):           "report",
    ("validate", "inconclusive"):     "report",

    # REPORT: inform user, reset state
    ("report", "done"):               "idle",
}


# ─── Valid routes per origin_stage (what thinking can exit to) ────────────────

VALID_ROUTES: dict[str | None, dict[str, str]] = {
    # Before any task
    None: {
        "new_task": "A proof task is being provided (file path or theorem)",
        "respond": "Continue the conversation, no task transition yet",
    },
    # After parse asked for clarification
    "parse": {
        "new_task": "A proof task is being provided",
        "respond": "Continue chatting, no task yet",
    },
    # After setup failed (file not found)
    "setup": {
        "new_task": "Providing the correct file path",
        "ready": "File path issue resolved, proceed with setup",
        "respond": "Continue discussing",
    },
    # After soundness found issue
    "soundness": {
        "proceed": "Proceed with proving despite soundness concern",
        "new_task": "Abandon this theorem, start a new task",
        "respond": "Continue discussing the soundness issue",
    },
    # During prover monitoring (dispatch → idle → thinking)
    "dispatch": {
        "prover_done": "Prover has reported completion",
        "new_task": "Cancel current proof, start a new task",
        "respond": "Continue waiting / discuss progress",
    },
    # After report
    "report": {
        "new_task": "Start a new proof task",
        "respond": "Continue discussing the result",
    },
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class UserIntent:
    theorem_file: str = ""
    skip_soundness: bool = False
    notes: str = ""
    urgent: bool = False


@dataclass
class WorkflowState:
    stage: str = "idle"
    task: dict = field(default_factory=dict)
    raw_input: str = ""
    sender: str = ""
    retries: int = 0
    prover_start: float = 0.0
    prover_done: bool = False
    prover_agent_name: str | None = None
    history: list[str] = field(default_factory=list)
    validation: dict = field(default_factory=dict)
    clarification: str | None = None
    origin_stage: str | None = None


# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    """Persistent loop. Stages return transition names. Table resolves next state."""
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    # Resume from checkpoint if available
    if hasattr(agent, '_restored_state') and agent._restored_state:
        state = WorkflowState(**{
            k: v for k, v in agent._restored_state.items()
            if k in WorkflowState.__dataclass_fields__
        })
        await agent._emit("message", f"[TaskManager] Resumed from checkpoint at stage: {state.stage}")
    else:
        state = WorkflowState(stage="parse")

    agent._workflow_state = state

    while not agent.cancellation.is_cancelled:
        try:
            handler = HANDLERS[state.stage]
            transition = await handler(state, agent)

            # Thinking resolves against origin_stage
            if state.stage == "thinking" and state.origin_stage:
                lookup_stage = state.origin_stage
            else:
                lookup_stage = state.stage

            next_stage = TRANSITIONS.get((lookup_stage, transition))
            if next_stage is None:
                # If thinking returned invalid route, fallback lookup without origin
                next_stage = TRANSITIONS.get(("thinking", transition))
            if next_stage is None:
                await agent._emit("message",
                    f"[TaskManager] Unknown transition: ({lookup_stage}, {transition})")
                next_stage = "idle"

            # Track origin: remember which hard state led to idle
            # so thinking knows what exits are valid
            if next_stage == "idle" and state.stage != "thinking":
                state.origin_stage = state.stage

            # Emit state transition event for live dashboard visualization
            await agent._emit("state_transition", {
                "from": state.stage,
                "transition": transition,
                "to": next_stage,
            })

            state.stage = next_stage
            state.retries = 0
            agent._workflow_state = state

        except Exception as e:
            state.retries += 1
            await agent._emit("message",
                f"[TaskManager] Error in {state.stage}: {e} (retry {state.retries})")
            if state.retries >= MAX_STAGE_RETRIES:
                state.clarification = f"Stuck in '{state.stage}' after {state.retries} retries: {e}"
                state.origin_stage = state.stage
                state.stage = "idle"
                state.retries = 0
            agent._workflow_state = state

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"status": "cancelled", "history": state.history}
    return result


# ─── State handlers (return transition name) ─────────────────────────────────

async def _state_parse(state: WorkflowState, agent) -> str:
    """Extract task from raw_input."""
    from .._helpers import ask

    if not state.raw_input:
        state.clarification = (
            "Ready for a proof task. Please provide:\n"
            "- File path containing the theorem\n"
            "- Any instructions (e.g., 'skip soundness', 'urgent')")
        return "need_clarification"

    @dataclass
    class _Intent:
        theorem_file: str
        skip_soundness: bool
        notes: str
        urgent: bool

    result = await ask(
        inp=state.raw_input,
        result_type=_Intent,
        system_prompt=(
            "Parse the user's proof request. Extract:\n"
            "- theorem_file: the exact file path mentioned by the user (required)\n"
            "- skip_soundness: true if user says 'sound', 'skip CEA', 'pre-approved'\n"
            "- notes: any special instructions or context provided\n"
            "- urgent: true if user says 'fast', 'ASAP', 'quickly'\n\n"
            "IMPORTANT: Use the EXACT file path the user provided. Do not guess or substitute."
        ),
        cwd=agent._cwd,
    )

    if result.output and result.output.theorem_file:
        state.task = asdict(result.output)
        await agent._emit("message", f"[TaskManager] Parsed: {state.task}")
        return "parsed"

    state.clarification = (
        "I couldn't extract a clear task from your message. "
        "Could you clarify which file contains the theorem and any constraints?")
    return "need_clarification"


async def _state_idle(state: WorkflowState, agent) -> str:
    """Blocks until a message arrives (peek, non-destructive). Routes to thinking.
    During monitoring, times out periodically for re-ping."""
    if state.clarification:
        await _send_to_user(agent, state.clarification)
        state.clarification = None

    await agent._emit("message", "[TaskManager] Waiting for messages...")
    messages_ch = agent.channel_bus.get_or_create(f"{agent.spec.name}:messages")

    # Timeout only during active proving
    is_monitoring = state.prover_agent_name and not state.prover_done
    wait_timeout = MONITOR_INTERVAL if is_monitoring else None

    # Wait for message without consuming it — run_ai will pick it up
    has_msg = await messages_ch.wait_for_message(timeout=wait_timeout)

    if not has_msg:
        return "monitor_tick"

    # Peek to log what arrived (message stays in queue for run_ai)
    summary = messages_ch.peek_summary()
    if summary:
        sender, _ = summary[0]
        await agent._emit("message", f"[TaskManager] Message from {sender} — entering thinking...")

    return "message_received"


THINKING_MAX_TURNS = 20  # Cap on LLM turns during thinking phase


async def _get_thinking_agent(state: WorkflowState, agent):
    """Get or create the appropriate thinking agent based on workflow phase.
    - Pre-dispatch (no prover): tm_clarifier — narrows down the task
    - Post-dispatch (prover active): tm_monitor — monitors and relays
    Sessions persist on the agent object between calls."""
    from .._helpers import swarm_agent, agent_from_name

    is_monitoring = state.prover_agent_name and not state.prover_done

    if is_monitoring:
        # Monitor phase — get or create tm_monitor
        if not hasattr(agent, '_tm_monitor') or agent._tm_monitor is None:
            ctx = swarm_agent("tm_monitor", swarm=agent.swarm, cwd=agent._cwd)
            monitor = await ctx.__aenter__()
            agent._tm_monitor_ctx = ctx
            agent._tm_monitor = monitor
            # Send initial context so monitor knows the task
            task_file = state.task.get('theorem_file', '?')
            await agent.channel_bus.send_to(
                f"{monitor.spec.name}:messages",
                sender="system",
                payload=f"You are monitoring proof of {task_file}. Prover agent: {state.prover_agent_name}. Relay between user and Prover.",
            )
        return agent._tm_monitor
    else:
        # Clarification phase — get or create tm_clarifier
        if not hasattr(agent, '_tm_clarifier') or agent._tm_clarifier is None:
            ctx = swarm_agent("tm_clarifier", swarm=agent.swarm, cwd=agent._cwd)
            clarifier = await ctx.__aenter__()
            agent._tm_clarifier_ctx = ctx
            agent._tm_clarifier = clarifier
        return agent._tm_clarifier


async def _state_thinking(state: WorkflowState, agent) -> str:
    """Two-phase thinking:
    Phase 1: Delegate to the appropriate stateful agent (clarifier or monitor).
             Message is in the TaskManager's inbox — forward it to the thinking agent.
             The agent session persists, so it remembers prior conversation.
    Phase 2: ask() picks the route based on the agent's response.
    """
    from .._helpers import ask

    routes = VALID_ROUTES.get(state.origin_stage, VALID_ROUTES[None])

    # Get the right thinking agent for this phase
    thinking_agent = await _get_thinking_agent(state, agent)

    # Forward the pending message from TaskManager's inbox to the thinking agent's inbox
    messages_ch = agent.channel_bus.get_or_create(f"{agent.spec.name}:messages")
    msg = await messages_ch.receive(timeout=1.0)
    if msg:
        await agent.channel_bus.send_to(
            f"{thinking_agent.spec.name}:messages",
            sender=msg.sender,
            payload=msg.payload,
        )
    else:
        # Monitor tick — send system ping
        await agent.channel_bus.send_to(
            f"{thinking_agent.spec.name}:messages",
            sender="system",
            payload="Status check. Ping prover if no recent progress.",
        )

    # Phase 1: let the thinking agent run (session persists between calls)
    # Clarifier must produce a structured response; monitor uses freeform
    is_monitoring = state.prover_agent_name and not state.prover_done

    @dataclass
    class _ClarifierResponse:
        file_path: str | None = None
        theorem_names: list[str] | None = None
        has_sorry: bool = False
        needs_user_input: bool = False
        question_for_user: str | None = None
        summary: str = ""

    result_type = str if is_monitoring else _ClarifierResponse
    ai_result = await thinking_agent.run_ai(inp=None, result_type=result_type, max_turns=THINKING_MAX_TURNS)

    if is_monitoring:
        agent_response = ai_result.output or ai_result.raw_result or ""
        if agent_response:
            await _send_to_user(agent, agent_response)
            await agent._emit("message", f"[TaskManager monitor]: {agent_response}")
    else:
        clarifier_out = ai_result.output
        if clarifier_out and isinstance(clarifier_out, _ClarifierResponse):
            agent_response = clarifier_out.summary or ""
            # If clarifier needs user input, route back to idle with the question
            if clarifier_out.needs_user_input and clarifier_out.question_for_user:
                state.clarification = clarifier_out.question_for_user
                state.raw_input = agent_response
                await agent._emit("message", f"[TaskManager]: Asking user: {clarifier_out.question_for_user}")
                return "respond"
            # If we got a file path, format for downstream
            if clarifier_out.file_path:
                theorems = ", ".join(clarifier_out.theorem_names or [])
                agent_response = (
                    f"File: {clarifier_out.file_path}\n"
                    f"Theorems with sorry: {theorems}\n"
                    f"{clarifier_out.summary}"
                )
                await _send_to_user(agent, agent_response)
                await agent._emit("message", f"[TaskManager]: {agent_response}")
            else:
                await _send_to_user(agent, agent_response)
                await agent._emit("message", f"[TaskManager]: {agent_response}")
        else:
            agent_response = ai_result.raw_result or ""
            if agent_response:
                await agent._emit("message", f"[TaskManager]: {agent_response}")

    # Store for downstream states
    state.raw_input = agent_response

    # Phase 2: stateless route decision
    route_desc = "\n".join(f"- '{k}': {v}" for k, v in routes.items())

    task_info = f"Task already parsed: {state.task}\n" if state.task else ""
    context_block = task_info or "No active task."
    if state.prover_agent_name and not state.prover_done:
        context_block += f" Prover '{state.prover_agent_name}' is active."

    @dataclass
    class _RouteDecision:
        route: str
        clarification: str | None = None

    decision = await ask(
        inp=(
            f"Workflow context: {context_block}\n"
            f"Origin stage: {state.origin_stage}\n"
            f"Agent's response: {agent_response}\n\n"
            f"Pick the correct route."
        ),
        result_type=_RouteDecision,
        system_prompt=(
            f"You are a state machine router.\n\n"
            f"RULES:\n"
            f"- Response confirms a file path + theorem with sorry → 'new_task'\n"
            f"- User says 'go ahead'/'proceed'/'yes' and task already parsed → 'proceed'\n"
            f"- Response says prover is done/complete/finished → 'prover_done'\n"
            f"- Response is conversational, clarifying, or no action yet → 'respond'\n\n"
            f"VALID ROUTES:\n{route_desc}\n\n"
            f"If routing 'respond', set 'clarification' to a message for the user."
        ),
        cwd=agent._cwd,
    )

    if decision.output:
        route = decision.output.route
        if decision.output.clarification:
            state.clarification = decision.output.clarification
        if route in routes:
            return route
        non_respond = [r for r in routes if r != "respond"]
        if non_respond:
            return non_respond[0]

    return "respond"


async def _state_setup(state: WorkflowState, agent) -> str:
    """Copy theorem file to Sandbox."""
    task = UserIntent(**state.task)
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    src = cwd / task.theorem_file
    dst = cwd / "StrataAgent" / "Sandbox" / "Stub.lean"
    dst.parent.mkdir(parents=True, exist_ok=True)

    if not src.exists():
        await agent._emit("message", f"[TaskManager] File not found: {task.theorem_file}")
        state.clarification = f"File not found: {task.theorem_file}. Please provide the correct path."
        return "file_not_found"

    shutil.copy2(src, dst)
    await agent._emit("message", f"[TaskManager] Copied {task.theorem_file} → Sandbox/Stub.lean")
    return "ready"


async def _state_soundness(state: WorkflowState, agent) -> str:
    """Run CEA soundness check via swarm context."""
    from .._helpers import swarm_agent

    task = UserIntent(**state.task)
    if task.skip_soundness:
        await agent._emit("message", "[TaskManager] Soundness skipped (pre-approved).")
        return "skipped"

    await agent._emit("message", "[TaskManager] Running CEA soundness check...")

    @dataclass
    class _Verdict:
        sound: bool
        confidence: str = "medium"
        counterexample: str | None = None
        reasoning: str | None = None

    async with swarm_agent("counter_example", swarm=agent.swarm, cwd=agent._cwd) as cea:
        verdict = await cea.run(
            inp={
                "file": task.theorem_file,
                "user_request": state.raw_input,
                "action": "Read the file, identify the theorem to prove, and check soundness",
            },
            result_type=_Verdict,
        )

    if verdict.output and not verdict.output.sound:
        await agent._emit("message",
            f"[TaskManager] UNSOUND ({verdict.output.confidence}): {verdict.output.counterexample}")
        state.clarification = (
            f"Theorem may be unsound.\n"
            f"Counterexample: {verdict.output.counterexample}\n"
            f"Reasoning: {verdict.output.reasoning}\n"
            f"Should I proceed anyway, or would you like to fix the theorem first?")
        return "unsound"

    confidence = verdict.output.confidence if verdict.output else "unknown"
    await agent._emit("message", f"[TaskManager] Soundness passed ({confidence}).")
    return "sound"


async def _state_dispatch(state: WorkflowState, agent) -> str:
    """Launch prover as background task via swarm context."""
    import asyncio
    from .._helpers import swarm_agent

    task = UserIntent(**state.task)
    await agent._emit("message", "[TaskManager] Dispatching to Prover...")

    prover_ctx = swarm_agent("prover", swarm=agent.swarm, cwd=agent._cwd)
    prover = await prover_ctx.__aenter__()

    agent._prover_ctx = prover_ctx
    agent._prover_agent = prover
    state.prover_agent_name = prover.spec.name

    briefing = (
        f"Prove the theorem in {task.theorem_file}. "
        f"Soundness: {'pre-approved' if task.skip_soundness else 'checked'}. "
        f"{task.notes or 'No special constraints.'}. "
        f"Spawn sub-agents as needed. Message TaskManager when done."
    )

    async def _run_prover():
        try:
            await prover.run(inp=briefing, result_type=None)
        except Exception as e:
            await agent._emit("message", f"[TaskManager] Prover error: {e}")

    agent._prover_task = asyncio.create_task(_run_prover())

    state.prover_start = time.monotonic()
    state.prover_done = False

    # Tear down clarifier — task is confirmed, switching to monitor phase
    await _cleanup_thinking_agent(agent, "clarifier")

    await agent._emit("message", f"[TaskManager] Prover spawned: {state.prover_agent_name}")
    return "dispatched"


async def _state_validate(state: WorkflowState, agent) -> str:
    """Deep proof validation via swarm context."""
    from .._helpers import swarm_agent

    task = UserIntent(**state.task)
    await agent._emit("message", "[TaskManager] Validating proof...")

    @dataclass
    class _Validation:
        compiles: bool
        has_sorry: bool
        statements_match: bool

    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd) as validator:
        result = await validator.run(
            inp={"stub_file": task.theorem_file, "complete_file": task.theorem_file},
            result_type=_Validation,
        )

    if result.output:
        state.validation = asdict(result.output)
        v = result.output
        if v.compiles and not v.has_sorry and v.statements_match:
            await agent._emit("message", "[TaskManager] VALIDATED.")
            return "passed"
        else:
            reasons = []
            if not v.compiles: reasons.append("doesn't compile")
            if v.has_sorry: reasons.append("has sorry")
            if not v.statements_match: reasons.append("statements changed")
            await agent._emit("message", f"[TaskManager] FAILED: {', '.join(reasons)}")
            return "failed"

    await agent._emit("message", "[TaskManager] Validation inconclusive.")
    return "inconclusive"


async def _state_report(state: WorkflowState, agent) -> str:
    """Report result to user and clean up."""
    task = UserIntent(**{k: v for k, v in state.task.items() if k in UserIntent.__dataclass_fields__})
    v = state.validation

    if v.get("compiles") and not v.get("has_sorry") and v.get("statements_match"):
        state.clarification = f"Proof of {task.theorem_file} COMPLETE. No sorry, compiles, statements intact."
        state.history.append(f"proven:{task.theorem_file}:{int(time.time())}")
    else:
        reasons = []
        if not v.get("compiles", True): reasons.append("doesn't compile")
        if v.get("has_sorry", False): reasons.append("has sorry")
        if not v.get("statements_match", True): reasons.append("statements changed")
        state.clarification = f"Proof of {task.theorem_file} INCOMPLETE: {', '.join(reasons) or 'failed'}."
        state.history.append(f"failed:{task.theorem_file}:{int(time.time())}")

    await _cleanup_prover(agent, state)

    state.task = {}
    state.raw_input = ""
    state.sender = ""
    state.prover_start = 0.0
    state.prover_done = False
    state.prover_agent_name = None
    state.validation = {}
    return "done"


# ─── Handler registry ─────────────────────────────────────────────────────────

HANDLERS: dict[str, Any] = {
    "parse": _state_parse,
    "idle": _state_idle,
    "thinking": _state_thinking,
    "setup": _state_setup,
    "soundness": _state_soundness,
    "dispatch": _state_dispatch,
    "validate": _state_validate,
    "report": _state_report,
}


# ─── Helpers ──────────────────────────────────────────────────────────────────

async def _cleanup_prover(agent, state: WorkflowState):
    """Exit prover swarm_agent context and cancel background task."""
    if hasattr(agent, '_prover_task') and agent._prover_task:
        agent._prover_task.cancel()
        agent._prover_task = None
    if hasattr(agent, '_prover_ctx') and agent._prover_ctx:
        await agent._prover_ctx.__aexit__(None, None, None)
        agent._prover_ctx = None
        agent._prover_agent = None
    # Also tear down monitor since proving is done
    await _cleanup_thinking_agent(agent, "monitor")


async def _cleanup_thinking_agent(agent, which: str):
    """Tear down a thinking agent (clarifier or monitor)."""
    attr_ctx = f"_tm_{which}_ctx"
    attr_agent = f"_tm_{which}"
    if hasattr(agent, attr_agent) and getattr(agent, attr_agent) is not None:
        ctx = getattr(agent, attr_ctx, None)
        if ctx:
            await ctx.__aexit__(None, None, None)
        setattr(agent, attr_ctx, None)
        setattr(agent, attr_agent, None)


async def _send_to_agent(agent, target: str, message: str):
    await agent.channel_bus.send_to(f"{target}:messages", sender=agent.spec.name, payload=message)


async def _send_to_user(agent, message: str):
    await _send_to_agent(agent, "user", message)
