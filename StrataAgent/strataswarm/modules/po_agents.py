"""PO Agent helpers: spawn agents + generic verified agent loop.

The core pattern: `verified_loop` — runs any agent with a pluggable
verifier. The agent stays alive across rounds, receives verification
feedback in-context, and retries until the verifier passes or rounds
are exhausted.

Every stage that uses an agent MUST use this pattern.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, TypeVar, Callable, Awaitable

from .._helpers import swarm_agent

T = TypeVar("T")


# ─── Structured output types ─────────────────────────────────────────────────

@dataclass
class ProofResult:
    success: bool = False
    has_sorry: bool = True
    sorry_count: int = 0
    helper_sorries: list[str] = field(default_factory=list)
    blocking_reason: str = ""


@dataclass
class SketchResult:
    success: bool = False
    blocking_reason: str = ""


@dataclass
class ValidationResult:
    compiles: bool = False
    has_sorry: bool = True
    statements_match: bool = False


@dataclass
class VerifyResult:
    compiles: bool = False
    has_sorry: bool = True


@dataclass
class SoundnessVerdict:
    sound: bool = False
    confidence: str = "medium"
    counterexample: str | None = None
    reasoning: str | None = None


@dataclass
class SplitResult:
    success: bool = False
    error: str = ""


# ─── Verified Loop ───────────────────────────────────────────────────────────

@dataclass
class LoopOutcome:
    """Result of a verified agent loop."""
    success: bool
    output: Any = None
    rounds: int = 0
    last_error: str = ""


async def verified_loop(
    agent_ctx,
    initial_input: Any,
    verify: Callable[[], str | None],
    max_rounds: int = 3,
    max_turns: int = 50,
    result_type: type | None = None,
    use_run_ai: bool = True,
    feedback_prefix: str = "VERIFICATION FAILED",
) -> LoopOutcome:
    """Run any agent in a verify→feedback loop.

    The agent stays alive across all rounds. After each round the verifier
    runs. If it returns None → success. If it returns an error string →
    that string is fed back to the agent as the next prompt.

    Args:
        agent_ctx: A living agent (entered swarm_agent ctx, or persistent internal agent).
                   Must support run_ai() (if use_run_ai=True) or run() (if False).
        initial_input: First input to send (str, dict, or Any with __str__).
        verify: Callable that checks the result AFTER the agent runs.
                Returns None if OK, or an error string to feed back.
        max_rounds: Maximum verify→feedback cycles.
        max_turns: Turns per run_ai/run call.
        result_type: Expected structured output (None = freeform text).
        use_run_ai: True → agent_ctx.run_ai() (persistent session).
                    False → agent_ctx.run() (single shot, for stateless agents).
        feedback_prefix: Prefix for feedback messages (helps agent distinguish
                         verification feedback from normal prompts).

    Returns:
        LoopOutcome with success, last output, round count, and last error.

    Examples:
        # proof_writer: verify no sorry + DAG check
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input={"file": f, "action": "prove this"},
            verify=lambda: _check_proof(cwd, f, workspace),
            max_rounds=3, max_turns=50,
            result_type=ProofResult,
        )

        # decomposer: verify files exist + sketch compiles
        outcome = await verified_loop(
            agent_ctx=decomposer,
            initial_input="Decompose theorem X...",
            verify=lambda: _check_decomposition(cwd, workspace),
            max_rounds=2, max_turns=100,
            result_type=DecomposeResult,
        )

        # sketcher (stateless, single shot with verify)
        outcome = await verified_loop(
            agent_ctx=sketcher,
            initial_input={"file": f, "action": "stitch lemmas"},
            verify=lambda: None if stub_compiles() else "Stub.lean doesn't compile",
            max_rounds=1, max_turns=50,
            result_type=SketchResult,
            use_run_ai=False,
        )
    """
    last_output = None
    last_error = ""

    for round_num in range(max_rounds):
        # Determine input for this round
        inp = initial_input if round_num == 0 else f"{feedback_prefix}: {last_error}\nFix the issue and try again."

        # Run the agent
        if use_run_ai:
            result = await agent_ctx.run_ai(inp=inp, result_type=result_type, max_turns=max_turns)
        else:
            result = await agent_ctx.run(inp=inp, result_type=result_type)

        last_output = result.output if hasattr(result, 'output') else result

        # Verify
        error = verify()
        if error is None:
            return LoopOutcome(success=True, output=last_output, rounds=round_num + 1)

        last_error = error

    return LoopOutcome(success=False, output=last_output, rounds=max_rounds, last_error=last_error)


# ─── Agent Runners (use verified_loop internally) ────────────────────────────

async def run_proof_writer(agent, workspace: str, file: str, action: str,
                           max_turns: int = 50, max_rounds: int = 2,
                           verify: Callable[[], str | None] | None = None) -> LoopOutcome:
    """Spawn proof_writer with in-context verification loop."""
    from .po_verify import check_import_dag, verify_no_sorry, count_sorries

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    def _default_verify() -> str | None:
        bad = check_import_dag(cwd / file, workspace)
        if bad:
            return f"Illegal imports {bad}. Only import from {workspace}/ or external (Strata.*, etc)."
        if verify_no_sorry(cwd, file):
            return None
        return f"{count_sorries(cwd, file)} sorry(s) remain. Continue filling them."

    async with swarm_agent("proof_writer", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=workspace, stateless=False) as writer:
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input={"file": file, "action": action},
            verify=verify or _default_verify,
            max_rounds=max_rounds,
            max_turns=max_turns,
            result_type=ProofResult,
            use_run_ai=True,
            feedback_prefix="PROOF VERIFICATION",
        )

    return outcome


async def run_cea(agent, workspace: str, file: str, theorem: str) -> SoundnessVerdict | None:
    """Spawn CEA (stateless, no loop needed — one-shot check)."""
    async with swarm_agent("counter_example", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as cea:
        result = await cea.run(
            inp={"file": file, "theorem": theorem, "action": f"Check soundness of: {theorem}"},
            result_type=SoundnessVerdict,
        )
    return result.output


async def run_validator(agent, workspace: str, stub_file: str, complete_file: str) -> ValidationResult | None:
    """Spawn deep_proof_validator (stateless)."""
    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as v:
        result = await v.run(
            inp={"stub_file": stub_file, "complete_file": complete_file},
            result_type=ValidationResult,
        )
    return result.output


async def run_splitter(agent, workspace: str, file: str,
                       verify: Callable[[], str | None] | None = None) -> LoopOutcome:
    """Spawn po_splitter with optional verification loop."""
    from .po_verify import verify_split_complete

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    def _default_verify() -> str | None:
        if verify_split_complete(cwd, workspace):
            return None
        return "Split incomplete: Stub/Def.lean missing or Stub.lean doesn't import it."

    async with swarm_agent("po_splitter", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as splitter:
        outcome = await verified_loop(
            agent_ctx=splitter,
            initial_input={
                "file": file, "workspace": workspace,
                "action": "Split into Stub/Def.lean (definitions) and Stub.lean (theorem only, imports defs)",
            },
            verify=verify or _default_verify,
            max_rounds=2,
            max_turns=50,
            result_type=SplitResult,
            use_run_ai=False,
            feedback_prefix="SPLIT VERIFICATION",
        )

    return outcome


async def run_sketcher(agent, workspace: str, file: str, theorem: str,
                       all_lemmas: list[str], proof_sketch: str,
                       verify: Callable[[], str | None] | None = None) -> LoopOutcome:
    """Spawn po_sketcher with verification."""
    from .po_verify import check_import_dag

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    def _default_verify() -> str | None:
        bad = check_import_dag(cwd / file, workspace)
        if bad:
            return f"Sketch has illegal imports: {bad}"
        return None

    async with swarm_agent("po_sketcher", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as writer:
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input={
                "file": file, "theorem": theorem,
                "action": (
                    f"SKETCH STITCHING: wire decomposed lemmas together.\n\n"
                    f"Lemma files have theorems with `sorry` — treat as axioms.\n\n"
                    f"IMPORTS (use ONLY these):\n"
                    f"{chr(10).join('import ' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in all_lemmas)}\n\n"
                    f"Sketch: {proof_sketch}\n\n"
                    f"Add imports, fill proof body, run lean_verify."
                ),
            },
            verify=verify or _default_verify,
            max_rounds=1,
            max_turns=50,
            result_type=SketchResult,
            use_run_ai=False,
            feedback_prefix="SKETCH VERIFICATION",
        )

    return outcome


async def run_child_po(agent, child_workspace: str, lemma_file: str, depth: int) -> dict | None:
    """Spawn a child PO (module agent, no loop — it has its own internal loop)."""
    async with swarm_agent("prover", swarm=agent.swarm, cwd=agent._cwd, workspace=child_workspace) as child:
        result = await child.run(
            inp={
                "theorem_file": lemma_file,
                "theorem_name": Path(lemma_file).stem,
                "workspace": child_workspace,
                "skip_soundness": True,
                "parent_agent": agent.spec.name,
                "depth": depth,
            },
            result_type=None,
        )
    return result.output if result else None


# ─── Swarm checkpoint ────────────────────────────────────────────────────────

async def swarm_checkpoint(agent, reason: str):
    """Trigger swarm-level checkpoint. Non-blocking."""
    swarm = getattr(agent, 'swarm', None)
    if swarm and hasattr(swarm, 'checkpoint'):
        try:
            await swarm.checkpoint(reason=reason)
        except Exception:
            pass
