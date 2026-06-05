"""TaskManager v3: Mode-aware router with multi-agent dispatch.

Design:
- TM's own session is the router brain (persistent, contextual, no tools)
- Internal agents (clarifier, chat, monitor) do narrow work
- Modes track workflow phase: no_task → clarifying → proving → validating
- Hard states handle mechanics (setup, soundness, dispatch, validate, report)
"""

from __future__ import annotations

import shutil
import time
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

T = TypeVar("T")

MAX_STAGE_RETRIES = 5
PROVER_TIMEOUT = 86400
MONITOR_INTERVAL = 600
THINKING_MAX_TURNS = 20
ROUTER_MAX_TURNS = 3


# ─── Enums ────────────────────────────────────────────────────────────────────

class WorkflowMode(str, Enum):
    NO_TASK = "no_task"
    CLARIFYING = "clarifying"
    PROVING = "proving"
    VALIDATING = "validating"


class Transition(str, Enum):
    MESSAGE_RECEIVED = "message_received"
    MONITOR_TICK = "monitor_tick"
    NEW_TASK = "new_task"
    PROCEED = "proceed"
    PROVER_DONE = "prover_done"
    RESPOND = "respond"
    CANCEL = "cancel"
    READY = "ready"
    FILE_NOT_FOUND = "file_not_found"
    DISPATCHED = "dispatched"
    PASSED = "passed"
    FAILED = "failed"
    INCONCLUSIVE = "inconclusive"
    DONE = "done"


class Stage(str, Enum):
    IDLE = "idle"
    THINKING = "thinking"
    SETUP = "setup"
    DISPATCH = "dispatch"
    VALIDATE = "validate"
    REPORT = "report"


class Handler(str, Enum):
    CLARIFIER = "clarifier"
    MONITOR = "monitor"
    CHAT = "chat"


# ─── Transitions ──────────────────────────────────────────────────────────────

TRANSITIONS: dict[tuple[Stage, Transition], Stage] = {
    (Stage.IDLE, Transition.MESSAGE_RECEIVED):  Stage.THINKING,
    (Stage.IDLE, Transition.MONITOR_TICK):      Stage.THINKING,

    (Stage.THINKING, Transition.NEW_TASK):      Stage.SETUP,
    (Stage.THINKING, Transition.PROCEED):       Stage.DISPATCH,
    (Stage.THINKING, Transition.PROVER_DONE):   Stage.VALIDATE,
    (Stage.THINKING, Transition.RESPOND):       Stage.IDLE,
    (Stage.THINKING, Transition.CANCEL):        Stage.REPORT,

    (Stage.SETUP, Transition.READY):            Stage.DISPATCH,
    (Stage.SETUP, Transition.FILE_NOT_FOUND):   Stage.THINKING,

    (Stage.DISPATCH, Transition.DISPATCHED):    Stage.IDLE,

    (Stage.VALIDATE, Transition.PASSED):        Stage.REPORT,
    (Stage.VALIDATE, Transition.FAILED):        Stage.REPORT,
    (Stage.VALIDATE, Transition.INCONCLUSIVE):  Stage.REPORT,

    (Stage.REPORT, Transition.DONE):            Stage.IDLE,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class UserIntent:
    theorem_file: str = ""
    skip_soundness: bool = False
    notes: str = ""


@dataclass
class ClarifierResponse:
    file_path: str | None = None
    theorem_names: list[str] | None = None
    has_sorry: bool = False
    skip_soundness: bool = False
    needs_user_input: bool = False
    question_for_user: str | None = None
    summary: str = ""


@dataclass
class RouteDecision:
    state_transition: Transition = Transition.RESPOND
    user_message: str | None = None
    mode_change: WorkflowMode | None = None
    forward_to: Handler | None = None


@dataclass
class WorkflowState:
    stage: Stage = Stage.IDLE
    mode: WorkflowMode = WorkflowMode.NO_TASK
    task: dict = field(default_factory=dict)
    raw_input: str = ""
    sender: str = ""
    retries: int = 0
    prover_start: float = 0.0
    prover_done: bool = False
    prover_agent_name: str | None = None
    active_handler: Handler = Handler.CLARIFIER
    history: list[str] = field(default_factory=list)
    validation: dict = field(default_factory=dict)


# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    if hasattr(agent, '_restored_state') and agent._restored_state:
        state = WorkflowState(**{
            k: v for k, v in agent._restored_state.items()
            if k in WorkflowState.__dataclass_fields__
        })
        await agent._emit("message", f"[TM] Resumed: {state.stage.value} / {state.mode.value}")
    else:
        state = WorkflowState()

    agent._workflow_state = state

    while not agent.cancellation.is_cancelled:
        try:
            handler = STAGE_HANDLERS[state.stage]
            transition = await handler(state, agent)

            next_stage = TRANSITIONS.get((state.stage, transition))
            if next_stage is None:
                await agent._emit("message", f"[TM] Bad transition: ({state.stage.value}, {transition.value})")
                next_stage = Stage.IDLE

            await agent._emit("state_transition", {
                "from": state.stage.value, "transition": transition.value, "to": next_stage.value,
            })
            await agent._emit("message",
                f"[TM] {state.stage.value} →{transition.value}→ {next_stage.value} ({state.mode.value})")

            state.stage = next_stage
            state.retries = 0
            agent._workflow_state = state

        except Exception as e:
            state.retries += 1
            await agent._emit("message", f"[TM] Error in {state.stage.value}: {e} (retry {state.retries})")
            if state.retries >= MAX_STAGE_RETRIES:
                state.stage = Stage.IDLE
                state.retries = 0
            agent._workflow_state = state

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"status": "cancelled", "history": state.history}
    return result


# ─── State handlers ───────────────────────────────────────────────────────────

async def _state_idle(state: WorkflowState, agent) -> Transition:
    await agent._emit("message", f"[TM] Waiting ({state.mode.value})...")
    messages_ch = agent.channel_bus.get_or_create(f"{agent.spec.name}:messages")

    wait_timeout = MONITOR_INTERVAL if state.mode == WorkflowMode.PROVING else None
    has_msg = await messages_ch.wait_for_message(timeout=wait_timeout)

    if not has_msg:
        # Check if prover task crashed without sending a message
        if state.mode == WorkflowMode.PROVING and hasattr(agent, '_prover_task'):
            if agent._prover_task and agent._prover_task.done():
                state.raw_input = "Prover task completed without sending a message."
                state.sender = "system"
                return Transition.MESSAGE_RECEIVED
        return Transition.MONITOR_TICK

    summary = messages_ch.peek_summary()
    if summary:
        sender, _ = summary[0]
        # Peek the actual payload for display (non-destructive via queue internals)
        pending = list(messages_ch._queue._queue)
        payload_preview = pending[0].payload[:300] if pending else ""
        await agent._emit("message", f"[{sender}]: {payload_preview}")

    return Transition.MESSAGE_RECEIVED


async def _state_thinking(state: WorkflowState, agent) -> Transition:
    """1. Consume → 2. Delegate → 3. Handle direct actions or Route via TM"""
    # 1. Consume
    msg_text = await _consume_message(state, agent)

    # 2. Delegate to internal agent
    handler_name = _pick_handler(state)
    internal_response, direct_transition = await _delegate(state, agent, handler_name)

    # Short-circuit: delegate already handled user communication and decided transition
    if direct_transition:
        return direct_transition

    # 3. TM routes (for cases that need contextual judgment)
    decision = await _route(state, agent, msg_text, handler_name, internal_response)

    if decision.user_message:
        await _send_to_user(agent, decision.user_message)
        await agent._emit("message", f"[TM → user]: {decision.user_message}")
    if decision.mode_change:
        state.mode = decision.mode_change
    if decision.forward_to:
        state.active_handler = decision.forward_to

    return decision.state_transition


async def _state_setup(state: WorkflowState, agent) -> Transition:
    task = UserIntent(**{k: v for k, v in state.task.items() if k in UserIntent.__dataclass_fields__})
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    src = cwd / task.theorem_file
    dst = cwd / "StrataAgent" / "Sandbox" / "Stub.lean"
    dst.parent.mkdir(parents=True, exist_ok=True)

    if not src.exists():
        await agent._emit("message", f"[TM] File not found: {task.theorem_file}")
        state.raw_input = f"File not found: {task.theorem_file}"
        state.sender = "system"
        return Transition.FILE_NOT_FOUND

    shutil.copy2(src, dst)
    await agent._emit("message", f"[TM] Copied {task.theorem_file} → Sandbox/Stub.lean")
    return Transition.READY



async def _state_dispatch(state: WorkflowState, agent) -> Transition:
    import asyncio
    from .._helpers import swarm_agent

    task = UserIntent(**{k: v for k, v in state.task.items() if k in UserIntent.__dataclass_fields__})
    await agent._emit("message", "[TM] Dispatching to Prover...")

    await _cleanup_internal(agent, Handler.CLARIFIER)

    prover_ctx = swarm_agent("prover", swarm=agent.swarm, cwd=agent._cwd)
    prover = await prover_ctx.__aenter__()
    agent._prover_ctx = prover_ctx
    agent._prover_agent = prover
    state.prover_agent_name = prover.spec.name

    prover_input = {
        "theorem_file": task.theorem_file,
        "theorem_name": task.notes or "",
        "workspace": "StrataAgent/Sandbox",
        "skip_soundness": task.skip_soundness,
        "parent_agent": agent.spec.name,
    }

    async def _run_prover():
        try:
            await prover.run(inp=prover_input, result_type=None)
        except Exception as e:
            await agent._emit("message", f"[TM] Prover error: {e}")

    agent._prover_task = asyncio.create_task(_run_prover())
    state.prover_start = time.monotonic()
    state.prover_done = False
    state.mode = WorkflowMode.PROVING
    state.active_handler = Handler.MONITOR

    await agent._emit("message", f"[TM] Prover: {state.prover_agent_name}")
    return Transition.DISPATCHED


async def _state_validate(state: WorkflowState, agent) -> Transition:
    from .._helpers import swarm_agent

    task = UserIntent(**{k: v for k, v in state.task.items() if k in UserIntent.__dataclass_fields__})
    await agent._emit("message", "[TM] Validating...")
    state.mode = WorkflowMode.VALIDATING

    @dataclass
    class _Validation:
        compiles: bool
        has_sorry: bool
        statements_match: bool

    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd) as validator:
        result = await validator.run(
            inp={
                "stub_file": task.theorem_file,
                "complete_file": "StrataAgent/Sandbox/Stub.lean",
            },
            result_type=_Validation,
        )

    if result.output:
        state.validation = asdict(result.output)
        v = result.output
        if v.compiles and not v.has_sorry and v.statements_match:
            return Transition.PASSED
        reasons = []
        if not v.compiles: reasons.append("doesn't compile")
        if v.has_sorry: reasons.append("has sorry")
        if not v.statements_match: reasons.append("statements changed")
        await agent._emit("message", f"[TM] Failed: {', '.join(reasons)}")
        return Transition.FAILED

    return Transition.INCONCLUSIVE


async def _state_report(state: WorkflowState, agent) -> Transition:
    task = UserIntent(**{k: v for k, v in state.task.items() if k in UserIntent.__dataclass_fields__})
    v = state.validation

    if v.get("compiles") and not v.get("has_sorry") and v.get("statements_match"):
        msg = f"Proof of {task.theorem_file} COMPLETE."
        state.history.append(f"proven:{task.theorem_file}:{int(time.time())}")
    else:
        reasons = []
        if not v.get("compiles", True): reasons.append("doesn't compile")
        if v.get("has_sorry", False): reasons.append("has sorry")
        if not v.get("statements_match", True): reasons.append("statements changed")
        msg = f"Proof of {task.theorem_file} INCOMPLETE: {', '.join(reasons) or 'failed'}."
        state.history.append(f"failed:{task.theorem_file}:{int(time.time())}")

    await _send_to_user(agent, msg)
    await agent._emit("message", f"[TM] {msg}")

    await _cleanup_prover(agent)
    await _cleanup_internal(agent, Handler.MONITOR)

    state.task = {}
    state.raw_input = ""
    state.sender = ""
    state.prover_start = 0.0
    state.prover_done = False
    state.prover_agent_name = None
    state.validation = {}
    state.mode = WorkflowMode.NO_TASK
    state.active_handler = Handler.CLARIFIER
    return Transition.DONE


# ─── Handler registry ─────────────────────────────────────────────────────────

STAGE_HANDLERS: dict[Stage, Any] = {
    Stage.IDLE: _state_idle,
    Stage.THINKING: _state_thinking,
    Stage.SETUP: _state_setup,
    Stage.DISPATCH: _state_dispatch,
    Stage.VALIDATE: _state_validate,
    Stage.REPORT: _state_report,
}


# ─── Thinking sub-functions ───────────────────────────────────────────────────

async def _consume_message(state: WorkflowState, agent) -> str:
    """Pop message from inbox, update state, return formatted text."""
    messages_ch = agent.channel_bus.get_or_create(f"{agent.spec.name}:messages")
    msg = await messages_ch.receive(timeout=1.0)
    if msg:
        state.raw_input = msg.payload
        state.sender = msg.sender
        return f"[From {msg.sender}]: {msg.payload}"
    state.raw_input = ""
    state.sender = "system"
    return "[System]: Monitor tick."


async def _delegate(state: WorkflowState, agent, handler_name: Handler) -> tuple[str, Transition | None]:
    """Forward message to internal agent, get response.
    Returns (response_text, direct_transition_or_None).
    Direct transition short-circuits the router for deterministic cases."""
    internal_agent = await _get_internal_agent(state, agent, handler_name)

    await agent.channel_bus.send_to(
        f"{internal_agent.spec.name}:messages",
        sender=state.sender or "system",
        payload=state.raw_input or "Status check.",
    )

    if handler_name == Handler.CLARIFIER:
        result = await internal_agent.run_ai(inp=None, result_type=ClarifierResponse, max_turns=THINKING_MAX_TURNS)
        out = result.output
        if out and isinstance(out, ClarifierResponse):
            if out.needs_user_input:
                question = out.question_for_user or out.summary
                await _send_to_user(agent, question)
                await agent._emit("message", f"[TM → user]: {question}")
                state.mode = WorkflowMode.CLARIFYING
                return question, Transition.RESPOND

            if out.file_path:
                state.task = {
                    "theorem_file": out.file_path,
                    "skip_soundness": out.skip_soundness,
                    "notes": f"Theorems: {out.theorem_names or []}",
                }
                response = f"File: {out.file_path}\nTheorems with sorry: {out.theorem_names}\n{out.summary}"
                await _send_to_user(agent, response)
                await agent._emit("message", f"[TM → user]: {response}")
                state.mode = WorkflowMode.CLARIFYING
                return response, Transition.NEW_TASK

            return out.summary, None
        return result.raw_result or "", None
    else:
        result = await internal_agent.run_ai(inp=None, result_type=str, max_turns=THINKING_MAX_TURNS)
        response = result.output or result.raw_result or ""

        # Send monitor/chat response to user
        if response:
            await _send_to_user(agent, response)
            await agent._emit("message", f"[TM → user]: {response}")

        # Let the TM router decide the transition based on the full response
        return response, None


async def _route(state: WorkflowState, agent, msg_text: str, handler_name: Handler, internal_response: str) -> RouteDecision:
    """TM's own session decides routing."""
    router_prompt = (
        f"=== MESSAGE ===\n{msg_text}\n\n"
        f"=== {handler_name.value.upper()} RESPONSE ===\n{internal_response}\n\n"
        f"=== STATE ===\nMode: {state.mode.value} | Task: {state.task or 'none'} | "
        f"Prover: {state.prover_agent_name or 'inactive'}\n\n"
        f"Route this."
    )

    result = await agent.run_ai(inp=router_prompt, result_type=RouteDecision, max_turns=ROUTER_MAX_TURNS)
    return result.output if result.output else RouteDecision()


# ─── Internal agent management ───────────────────────────────────────────────

def _pick_handler(state: WorkflowState) -> Handler:
    if state.mode == WorkflowMode.PROVING:
        return Handler.MONITOR
    return state.active_handler


async def _get_internal_agent(state: WorkflowState, agent, which: Handler):
    from .._helpers import swarm_agent

    attr = f"_tm_{which.value}"
    attr_ctx = f"_tm_{which.value}_ctx"

    if getattr(agent, attr, None) is None:
        # Monitor needs workspace scoping to read Sandbox files
        workspace = "StrataAgent/Sandbox" if which == Handler.MONITOR else None
        ctx = swarm_agent(f"tm_{which.value}", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace)
        internal = await ctx.__aenter__()
        setattr(agent, attr_ctx, ctx)
        setattr(agent, attr, internal)

    return getattr(agent, attr)


async def _cleanup_internal(agent, which: Handler):
    attr = f"_tm_{which.value}"
    attr_ctx = f"_tm_{which.value}_ctx"
    if getattr(agent, attr, None) is not None:
        ctx = getattr(agent, attr_ctx, None)
        if ctx:
            await ctx.__aexit__(None, None, None)
        setattr(agent, attr_ctx, None)
        setattr(agent, attr, None)


async def _cleanup_prover(agent):
    if hasattr(agent, '_prover_task') and agent._prover_task:
        agent._prover_task.cancel()
        agent._prover_task = None
    if hasattr(agent, '_prover_ctx') and agent._prover_ctx:
        await agent._prover_ctx.__aexit__(None, None, None)
        agent._prover_ctx = None
        agent._prover_agent = None


# ─── Helpers ──────────────────────────────────────────────────────────────────

async def _send_to_user(agent, message: str):
    await agent.channel_bus.send_to("user:messages", sender=agent.spec.name, payload=message)
