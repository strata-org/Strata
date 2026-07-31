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
                f"You have {turns} turns to make the file COMPILE — no more.\n\n"
                f"BANK YOUR PROGRESS — do NOT throw work away:\n"
                f"- Do NOT revert a partial proof back to a bare `:= by sorry`. Keep every\n"
                f"  step you already proved.\n"
                f"- If one subgoal is still open, cap ONLY that goal with `sorry` (e.g.\n"
                f"  `· sorry` on that branch) and leave the rest of the proof intact.\n"
                f"- If a sub-lemma is genuinely hard, factor it into a NEW named helper\n"
                f"  theorem declared ABOVE (with its own `sorry`) and close the goal with\n"
                f"  `exact helper ...`. That preserves the structure and lets the guide\n"
                f"  direct the helper next.\n"
                f"Just make it compile while keeping the most-proven state you can."
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
    from .po_lean import get_lean_tools

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    # Snapshot the ORIGINAL local-sorry count BEFORE the splitter runs. The
    # splitter must only MOVE text between files — it must never close a goal.
    # If the combined post-split sorry count drops below this, the splitter
    # proved (or dropped) a theorem, which is a hard role violation: the whole
    # decompose→prove→assemble pipeline assumes the Stub still carries its
    # obligations. We revert and fail rather than let a splitter-written proof
    # (or, worse, a silently dropped goal) propagate into Stub.clean.lean.
    _orig_sorries = get_lean_tools().count_sorries(file).total

    def _default_verify() -> str | None:
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

        # 4. Structural check: Stub.lean must import Stub.Def. Now that the
        #    oleans are built this reads cleanly instead of hitting a stale cache.
        if not verify_stub_imports_def(cwd, workspace):
            return "Stub.lean must import Stub.Def (the split-out definitions)."

        # 5. Sorry-preservation check LAST — the anti-cheat guard. The splitter
        #    is a text mover, not a prover: every `sorry` in the original file
        #    must survive across the two output files (defs never carry sorry, so
        #    Stub.lean carries all of them). A drop means the splitter closed a
        #    goal (wrote a proof) or dropped a theorem — reject and revert.
        post_sorries = (tools.count_sorries(def_rel).total
                        + tools.count_sorries(stub_rel).total)
        if post_sorries < _orig_sorries:
            return (
                f"You PROVED or DROPPED a theorem — forbidden. The input had "
                f"{_orig_sorries} `sorry`(s); after the split only {post_sorries} "
                f"remain. Your ONLY job is to MOVE text between files. Every "
                f"`sorry` must stay a `sorry` (proving is the proof_writer's job). "
                f"Restore each theorem body to exactly `:= by\\n  sorry` and split again."
            )
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
