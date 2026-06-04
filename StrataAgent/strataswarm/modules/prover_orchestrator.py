"""Proof Orchestrator v2: Router pattern with internal agents.

Same architecture as TaskManager:
- Orchestrator's own session is the router brain (persistent, no tools)
- Internal agents (decomposer, assembler) do the work
- Spawned agents (proof_writer, refactoring_agent, CEA) are stateless and scoped
- State machine handles mechanics
"""

from __future__ import annotations

import asyncio
import shutil
import time
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

T = TypeVar("T")

MAX_RETRIES = 3
MAX_PARALLEL_WRITERS = 3
WRITER_MAX_TURNS = 50
DECOMPOSER_MAX_TURNS = 25
ASSEMBLER_MAX_TURNS = 20
ROUTER_MAX_TURNS = 3


# ─── Enums ────────────────────────────────────────────────────────────────────

class ProverStage(str, Enum):
    IDLE = "idle"
    DECOMPOSE = "decompose"
    DIRECT_ATTEMPT = "direct_attempt"
    PROVE_LEMMAS = "prove_lemmas"
    REFACTOR = "refactor"
    VALIDATE = "validate"
    ASSEMBLE = "assemble"
    RETRY = "retry"
    DONE = "done"
    FAILED = "failed"


class ProverTransition(str, Enum):
    START = "start"
    DECOMPOSED = "decomposed"
    SIMPLE_ENOUGH = "simple_enough"
    PROOF_FOUND = "proof_found"
    NEEDS_DECOMP = "needs_decomp"
    ALL_PROVED = "all_proved"
    HAS_SORRY = "has_sorry"
    STUCK = "stuck"
    NEW_AXIOMS = "new_axioms"
    CANNOT_REFACTOR = "cannot_refactor"
    VALID = "valid"
    INVALID = "invalid"
    ASSEMBLED = "assembled"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"
    FAILED = "failed"


# ─── Transitions ──────────────────────────────────────────────────────────────

TRANSITIONS: dict[tuple[ProverStage, ProverTransition], ProverStage] = {
    (ProverStage.IDLE, ProverTransition.START):              ProverStage.DECOMPOSE,

    (ProverStage.DECOMPOSE, ProverTransition.DECOMPOSED):   ProverStage.PROVE_LEMMAS,
    (ProverStage.DECOMPOSE, ProverTransition.SIMPLE_ENOUGH): ProverStage.DIRECT_ATTEMPT,

    (ProverStage.DIRECT_ATTEMPT, ProverTransition.PROOF_FOUND): ProverStage.VALIDATE,
    (ProverStage.DIRECT_ATTEMPT, ProverTransition.NEEDS_DECOMP): ProverStage.DECOMPOSE,
    (ProverStage.DIRECT_ATTEMPT, ProverTransition.FAILED):  ProverStage.RETRY,

    (ProverStage.PROVE_LEMMAS, ProverTransition.ALL_PROVED): ProverStage.VALIDATE,
    (ProverStage.PROVE_LEMMAS, ProverTransition.HAS_SORRY): ProverStage.REFACTOR,
    (ProverStage.PROVE_LEMMAS, ProverTransition.STUCK):     ProverStage.RETRY,

    (ProverStage.REFACTOR, ProverTransition.NEW_AXIOMS):    ProverStage.PROVE_LEMMAS,
    (ProverStage.REFACTOR, ProverTransition.CANNOT_REFACTOR): ProverStage.RETRY,

    (ProverStage.VALIDATE, ProverTransition.VALID):         ProverStage.ASSEMBLE,
    (ProverStage.VALIDATE, ProverTransition.INVALID):       ProverStage.REFACTOR,
    (ProverStage.VALIDATE, ProverTransition.STUCK):         ProverStage.RETRY,

    (ProverStage.ASSEMBLE, ProverTransition.ASSEMBLED):     ProverStage.DONE,
    (ProverStage.ASSEMBLE, ProverTransition.FAILED):        ProverStage.RETRY,

    (ProverStage.RETRY, ProverTransition.NEW_APPROACH):     ProverStage.DECOMPOSE,
    (ProverStage.RETRY, ProverTransition.MAX_RETRIES):      ProverStage.FAILED,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class ProverState:
    stage: ProverStage = ProverStage.IDLE
    theorem_file: str = ""
    theorem_name: str = ""
    workspace: str = ""
    axiom_files: list[str] = field(default_factory=list)
    proved_files: list[str] = field(default_factory=list)
    attempt: int = 0
    attempt_logs: list[str] = field(default_factory=list)
    parent_agent: str = "TaskManager"


@dataclass
class ProverRouteDecision:
    transition: ProverTransition = ProverTransition.STUCK
    message_to_parent: str | None = None


# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    # Parse input
    if isinstance(inp, dict):
        theorem_file = inp.get("theorem_file", "")
        theorem_name = inp.get("theorem_name", "")
        parent_agent = inp.get("parent_agent", "TaskManager")
    elif isinstance(inp, str):
        theorem_file = inp
        theorem_name = ""
        parent_agent = "TaskManager"
    else:
        theorem_file = str(inp)
        theorem_name = ""
        parent_agent = "TaskManager"

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    base_name = Path(theorem_file).stem
    workspace = cwd / "StrataAgent" / "Sandbox" / base_name
    workspace.mkdir(parents=True, exist_ok=True)

    # Copy source file to workspace
    src = cwd / theorem_file
    dst = workspace / "Stub.lean"
    if src.exists() and not dst.exists():
        shutil.copy2(src, dst)

    state = ProverState(
        stage=ProverStage.DECOMPOSE,
        theorem_file=theorem_file,
        theorem_name=theorem_name,
        workspace=str(workspace),
        parent_agent=parent_agent,
    )
    agent._workflow_state = state

    await agent._emit("message", f"[Prover] Starting: {theorem_name} in {theorem_file}")
    await agent._emit("message", f"[Prover] Workspace: {workspace}")

    while not agent.cancellation.is_cancelled:
        if state.stage in (ProverStage.DONE, ProverStage.FAILED):
            break

        try:
            handler = STAGE_HANDLERS.get(state.stage)
            if not handler:
                break

            transition = await handler(state, agent)

            next_stage = TRANSITIONS.get((state.stage, transition))
            if next_stage is None:
                await agent._emit("message", f"[Prover] Bad transition: ({state.stage.value}, {transition.value})")
                next_stage = ProverStage.RETRY

            await agent._emit("state_transition", {
                "from": state.stage.value, "transition": transition.value, "to": next_stage.value,
            })
            await agent._emit("message",
                f"[Prover] {state.stage.value} →{transition.value}→ {next_stage.value}")

            state.stage = next_stage
            agent._workflow_state = state

        except Exception as e:
            await agent._emit("message", f"[Prover] Error in {state.stage.value}: {e}")
            state.stage = ProverStage.RETRY
            agent._workflow_state = state

    # Notify parent
    status_msg = f"Proof {'complete' if state.stage == ProverStage.DONE else 'failed'}: {theorem_file}"
    await _notify_parent(agent, state, status_msg)

    # Cleanup internal agents
    await _cleanup_internal(agent, "decomposer")
    await _cleanup_internal(agent, "assembler")

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"stage": state.stage.value, "theorem_file": theorem_file, "attempts": state.attempt}
    return result


# ─── Stage handlers ───────────────────────────────────────────────────────────

async def _stage_decompose(state: ProverState, agent) -> ProverTransition:
    """Decomposer agent analyzes theorem and proposes strategy."""
    decomposer = await _get_internal(agent, "decomposer")

    attempt_context = ""
    if state.attempt_logs:
        attempt_context = f"\nPrevious failed attempts:\n" + "\n".join(state.attempt_logs[-2:])

    await agent.channel_bus.send_to(
        f"{decomposer.spec.name}:messages",
        sender="system",
        payload=(
            f"Decompose theorem: {state.theorem_name}\n"
            f"File: {state.workspace}/Stub.lean\n"
            f"Attempt: {state.attempt + 1}/{MAX_RETRIES}\n"
            f"{attempt_context}\n"
            f"Read the file, use lean_hover_info on the sorry, and decide strategy."
        ),
    )

    @dataclass
    class _DecomposeResult:
        strategy: str = "decompose"  # "direct" or "decompose"
        axiom_files_created: list[str] = field(default_factory=list)
        reasoning: str = ""

    result = await decomposer.run_ai(inp=None, result_type=_DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)

    if result.output:
        if result.output.strategy == "direct":
            await agent._emit("message", "[Prover] Strategy: direct attempt")
            return ProverTransition.SIMPLE_ENOUGH

        state.axiom_files = result.output.axiom_files_created or []
        await agent._emit("message", f"[Prover] Decomposed: {len(state.axiom_files)} axioms")

        if state.axiom_files:
            return ProverTransition.DECOMPOSED

    return ProverTransition.SIMPLE_ENOUGH


async def _stage_direct_attempt(state: ProverState, agent) -> ProverTransition:
    """Single proof_writer on the stub file."""
    target = str(Path(state.workspace) / "Stub.lean")

    @dataclass
    class _ProofResult:
        success: bool
        needs_decomposition: bool = False
        blocking_reason: str = ""

    async with _scoped_agent("proof_writer", agent, state.workspace) as writer:
        result = await writer.run(
            inp={"file": target, "theorem": state.theorem_name, "action": "Prove the sorry"},
            result_type=_ProofResult,
        )

    if result.output:
        if result.output.success:
            state.proved_files = [target]
            return ProverTransition.PROOF_FOUND
        if result.output.needs_decomposition:
            return ProverTransition.NEEDS_DECOMP

    return ProverTransition.FAILED


async def _stage_prove_lemmas(state: ProverState, agent) -> ProverTransition:
    """Proof_writer on each axiom (parallel, capped)."""
    await agent._emit("message", f"[Prover] Proving {len(state.axiom_files)} lemmas...")

    semaphore = asyncio.Semaphore(MAX_PARALLEL_WRITERS)
    proved = []
    failed = []

    async def _prove_one(axiom_file: str):
        async with semaphore:
            @dataclass
            class _Result:
                success: bool
                blocking_reason: str = ""

            axiom_dir = str(Path(axiom_file).parent)
            async with _scoped_agent("proof_writer", agent, axiom_dir) as writer:
                result = await writer.run(
                    inp={"file": axiom_file, "action": "Prove the sorry"},
                    result_type=_Result,
                )

            if result.output and result.output.success:
                proved.append(axiom_file)
            else:
                failed.append(axiom_file)

    await asyncio.gather(*[_prove_one(f) for f in state.axiom_files])

    state.proved_files = proved
    await agent._emit("message", f"[Prover] Proved {len(proved)}/{len(state.axiom_files)}")

    if len(proved) == len(state.axiom_files):
        return ProverTransition.ALL_PROVED
    if failed:
        return ProverTransition.HAS_SORRY
    return ProverTransition.STUCK


async def _stage_refactor(state: ProverState, agent) -> ProverTransition:
    """Refactoring agent on unproved files."""
    unproved = [f for f in state.axiom_files if f not in state.proved_files]
    await agent._emit("message", f"[Prover] Refactoring {len(unproved)} files...")

    @dataclass
    class _RefactorResult:
        new_axiom_files: list[str] = field(default_factory=list)
        cannot_refactor: bool = False

    async with _scoped_agent("refactoring_agent", agent, state.workspace) as refactorer:
        result = await refactorer.run(
            inp={
                "files": unproved,
                "workspace": state.workspace,
                "action": "Use lean_hover_info at each sorry, create axiom files for sub-goals",
            },
            result_type=_RefactorResult,
        )

    if result.output and result.output.new_axiom_files:
        state.axiom_files = state.proved_files + result.output.new_axiom_files
        return ProverTransition.NEW_AXIOMS

    return ProverTransition.CANNOT_REFACTOR


async def _stage_validate(state: ProverState, agent) -> ProverTransition:
    """Assembler agent validates proved files compile and are sorry-free."""
    assembler = await _get_internal(agent, "assembler")

    files_list = "\n".join(state.proved_files)
    await agent.channel_bus.send_to(
        f"{assembler.spec.name}:messages",
        sender="system",
        payload=(
            f"Validate these proved files (lean_verify each, check for sorry):\n{files_list}\n"
            f"Workspace: {state.workspace}"
        ),
    )

    @dataclass
    class _ValidateResult:
        all_valid: bool
        issues: list[str] = field(default_factory=list)

    result = await assembler.run_ai(inp=None, result_type=_ValidateResult, max_turns=ASSEMBLER_MAX_TURNS)

    if result.output and result.output.all_valid:
        return ProverTransition.VALID
    if result.output and result.output.issues:
        await agent._emit("message", f"[Prover] Validation issues: {result.output.issues}")
        return ProverTransition.INVALID

    return ProverTransition.STUCK


async def _stage_assemble(state: ProverState, agent) -> ProverTransition:
    """Assembler combines proofs into the original file."""
    assembler = await _get_internal(agent, "assembler")

    await agent.channel_bus.send_to(
        f"{assembler.spec.name}:messages",
        sender="system",
        payload=(
            f"Assemble final proof:\n"
            f"- Original: {state.workspace}/Stub.lean\n"
            f"- Proved files: {state.proved_files}\n"
            f"Replace axioms/sorry with actual proofs. Run lean_verify on result."
        ),
    )

    @dataclass
    class _AssembleResult:
        success: bool
        output_file: str = ""
        error: str = ""

    result = await assembler.run_ai(inp=None, result_type=_AssembleResult, max_turns=ASSEMBLER_MAX_TURNS)

    if result.output and result.output.success:
        await agent._emit("message", f"[Prover] Assembled: {result.output.output_file}")
        return ProverTransition.ASSEMBLED

    return ProverTransition.FAILED


async def _stage_retry(state: ProverState, agent) -> ProverTransition:
    """Log attempt, decide retry or give up."""
    state.attempt += 1

    workspace = Path(state.workspace)
    log_file = workspace / f"attempt_{state.attempt}.md"
    log_content = (
        f"# Attempt {state.attempt}\n\n"
        f"Theorem: {state.theorem_file} / {state.theorem_name}\n"
        f"Axioms tried: {state.axiom_files}\n"
        f"Proved: {state.proved_files}\n"
        f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\n"
    )
    log_file.write_text(log_content)
    state.attempt_logs.append(log_content)

    await agent._emit("message", f"[Prover] Attempt {state.attempt}/{MAX_RETRIES} logged")

    if state.attempt >= MAX_RETRIES:
        return ProverTransition.MAX_RETRIES

    # Reset for next attempt
    state.axiom_files = []
    state.proved_files = []
    return ProverTransition.NEW_APPROACH


# ─── Stage handler registry ──────────────────────────────────────────────────

STAGE_HANDLERS: dict[ProverStage, Any] = {
    ProverStage.DECOMPOSE: _stage_decompose,
    ProverStage.DIRECT_ATTEMPT: _stage_direct_attempt,
    ProverStage.PROVE_LEMMAS: _stage_prove_lemmas,
    ProverStage.REFACTOR: _stage_refactor,
    ProverStage.VALIDATE: _stage_validate,
    ProverStage.ASSEMBLE: _stage_assemble,
    ProverStage.RETRY: _stage_retry,
}


# ─── Internal agent management ───────────────────────────────────────────────

async def _get_internal(agent, which: str):
    """Get or create an internal agent (decomposer, assembler). Session persists."""
    from .._helpers import swarm_agent

    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"

    if getattr(agent, attr, None) is None:
        ctx = swarm_agent(f"po_{which}", swarm=agent.swarm, cwd=agent._cwd)
        internal = await ctx.__aenter__()
        setattr(agent, attr_ctx, ctx)
        setattr(agent, attr, internal)

    return getattr(agent, attr)


async def _cleanup_internal(agent, which: str):
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"
    if getattr(agent, attr, None) is not None:
        ctx = getattr(agent, attr_ctx, None)
        if ctx:
            await ctx.__aexit__(None, None, None)
        setattr(agent, attr_ctx, None)
        setattr(agent, attr, None)


# ─── Scoped agent spawning ───────────────────────────────────────────────────

class _scoped_agent:
    """Creates a workspace-scoped stateless agent. Mirrors _spawn.py's workspace isolation."""

    def __init__(self, spec_name: str, parent_agent, scope_dir: str):
        self._spec_name = spec_name
        self._parent = parent_agent
        self._scope_dir = scope_dir
        self._agent = None
        self._unique_name = None

    async def __aenter__(self):
        from .._helpers import _load_spec, AGENT_SPECS_DIR
        from .._types import Workspace
        from .._tools import ToolSet
        from .._agent import SwarmAgent
        from .._messaging import create_messaging_server
        from .._directory import create_directory_server
        import time as _time

        path = AGENT_SPECS_DIR / f"{self._spec_name}.yaml"
        spec = _load_spec(path, {})

        # Scope workspace
        scope = f"{self._scope_dir}/**"
        spec.workspace = Workspace(read=[scope], write=[scope], edit=[scope])

        # Rebuild tools with scoped paths
        tools = ToolSet()
        tools.allow(f"Read({scope})")
        tools.allow(f"Write({scope})")
        tools.allow(f"Edit({scope})")
        if spec.tools:
            for t in spec.tools.allowed:
                if not any(t.name.startswith(p) for p in ("Read", "Write", "Edit")):
                    tools.allow(t.to_claude_format())
            for t in spec.tools.disallowed:
                tools.disallow(t.to_claude_format())
        spec.tools = tools

        # Unique name
        self._unique_name = f"{spec.name}_{int(_time.time()) % 100000}"
        spec.name = self._unique_name

        swarm = self._parent.swarm
        cwd = self._parent._cwd

        # Build MCP servers
        mcp_servers = dict(spec.mcp_servers or {})
        messaging_server = create_messaging_server(
            agent_name=self._unique_name,
            channel_bus=swarm._channel_bus,
            known_agents=[n for n in swarm._registry.nodes if n != self._unique_name],
            can_message=swarm.can_message,
            route_message=swarm._route_message,
            get_sender_display=swarm._get_sender_display,
            on_tool_call=swarm._record_tool_call,
            reply_only_mode=spec.reply_only,
            known_service_agents=set(),
            start_time=None,
            is_agent_alive=lambda r: r in swarm._registry.nodes or r in swarm._registry.sharded_agents,
            outbound_limit=spec.max_outbound_length,
            outbound_limit_response=spec.max_outbound_response,
            get_inbound_limit=swarm._get_inbound_limit,
        )
        mcp_servers["agent_messaging"] = messaging_server
        mcp_servers["agent_directory"] = create_directory_server(agent_name=self._unique_name, swarm=swarm)

        on_event = getattr(swarm, '_on_event_with_telemetry', None)

        self._agent = SwarmAgent(
            spec=spec,
            channel_bus=swarm._channel_bus,
            cwd=cwd,
            on_event=on_event,
            mcp_servers_override=mcp_servers,
            backend_factory=swarm._backend_factory,
        )
        self._agent.swarm = swarm

        # Register
        swarm._registry.add(spec)
        swarm._registry.agents[self._unique_name] = self._agent
        swarm._registry.visibility_graph[self._unique_name] = set(swarm._registry.visibility_graph.keys())
        for visible_set in swarm._registry.visibility_graph.values():
            visible_set.add(self._unique_name)

        # Create workspace directory
        Path(cwd or ".").joinpath(self._scope_dir).mkdir(parents=True, exist_ok=True)

        return self._agent

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        if self._unique_name and self._parent.swarm:
            swarm = self._parent.swarm
            await swarm._registry.remove(self._unique_name, cancel_task=False)
            swarm._channel_bus._channels.pop(f"{self._unique_name}:messages", None)
            self._agent = None
        return False


# ─── Helpers ──────────────────────────────────────────────────────────────────

async def _notify_parent(agent, state: ProverState, message: str):
    try:
        await agent.channel_bus.send_to(
            f"{state.parent_agent}:messages",
            sender=agent.spec.name,
            payload=message,
        )
    except Exception:
        pass
    await agent._emit("message", f"[Prover → {state.parent_agent}]: {message}")
