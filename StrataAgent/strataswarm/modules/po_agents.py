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
        if round_num == 0:
            inp = initial_input
        # Run the agent (fix rounds get fewer turns — just enough to fix compilation)
        turns = max_turns if round_num == 0 else min(max_turns, 12)

        if round_num > 0:
            inp = (
                f"{feedback_prefix}: {last_error}\n\n"
                f"Your allocated turns are over. The guide will review your work and advise\n"
                f"on how to proceed or whether the current direction is right.\n"
                f"You have {turns} turns to ONLY fix the compilation error so the file compiles.\n"
                f"Do NOT continue proving — leave sorry where needed. Just make it compile."
            )
        if use_run_ai:
            result = await agent_ctx.run_ai(inp=inp, result_type=result_type, max_turns=turns)
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

async def run_splitter(agent, workspace: str, file: str,
                       verify: Callable[[], str | None] | None = None) -> LoopOutcome:
    """Spawn po_splitter with optional verification loop."""
    from .po_verify import verify_file_exists, verify_stub_imports_def

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    def _default_verify() -> str | None:
        from .po_lean import get_lean_tools
        tools = get_lean_tools()
        def_rel = f"{workspace}/Stub/Def.lean"
        stub_rel = f"{workspace}/Stub.lean"

        # 1. Both files must exist (pure filesystem check — no oleans needed).
        if not (verify_file_exists(cwd, def_rel) and verify_file_exists(cwd, stub_rel)):
            return "Split incomplete: Stub/Def.lean or Stub.lean is missing."

        # 2. Build Stub/Def.lean FIRST. `check_compiles` runs `lake build`, which
        #    produces the .olean for the new Stub.Def module. This MUST happen
        #    before any LSP/import check, otherwise those checks fail with a stale
        #    "Imports are out of date and must be rebuilt" error and the split is
        #    wrongly reported as broken (the build was never delegated downstream).
        cr_def = tools.check_compiles(def_rel)
        if not cr_def.success:
            return f"Stub/Def.lean doesn't compile. Fix compilation errors."

        # 3. Build Stub.lean (its imports of Stub.Def now resolve to a fresh olean).
        cr_stub = tools.check_compiles(stub_rel)
        if cr_stub.has_error:
            return f"Stub.lean has compilation errors (not sorry). Fix them."

        # 4. Structural check LAST: Stub.lean must import Stub.Def. Now that the
        #    oleans are built this reads cleanly instead of hitting a stale cache.
        if not verify_stub_imports_def(cwd, workspace):
            return "Stub.lean must import Stub.Def (the split-out definitions)."
        return None

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
