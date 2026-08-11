"""Proof Orchestrator v5: Guide-Centric Architecture.

Every phase follows one pattern:
  1. Worker does mechanical work
  2. Guide reviews result via _consult_guide_raw()
  3. Guide decides next step via _consult_guide_decide()

The guide is the sole decision-maker for its lemma. The orchestrator handles
only plumbing (transitions, state persistence, agent lifecycle).

Two guide APIs:
  _consult_guide_raw(task)   → free-text response (advice, diagnosis)
  _consult_guide_decide(options, task) → structured choice + reason

Per-lemma state (LemmaContext):
  current_task     — what guide should focus on (set by caller, sticky)
  failure_context  — last error (set by any phase, sticky)
  needs_fresh_guide — dump .md + destroy + new guide reads .md
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import os
import re
import shutil
import time as _time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import verified_loop, run_splitter, LoopOutcome
from .po_lean import get_lean_tools, MoveSession, lake_build, file_path_to_module
from .po_util import setup_child_workspace, copy_cheat_sheet, cheat_sheet_name, cheat_sheet_source
from .lemma_ledger import LemmaLedger, LemmaEntry, LemmaStatus
from .cycle_detection import detect, MatchType
from .verifiers.proof_writer_verifier import make_proof_writer_verifier
from .._helpers import swarm_agent
from .._lean_tools_mcp import create_extractor_mcp_server
from .._tokens import CancellationToken
from .._agent import SwarmAgent

T = TypeVar("T")

MAX_DEPTH = 5
MIN_CHUNK_TURNS = 120
MAX_CHUNK_TURNS = 160
CHUNK_TURNS = MIN_CHUNK_TURNS
GRACE_TURNS = 20
# NO per-lemma or run-level backstops. A lemma is only ever stopped by a NATURAL
# give_up (the guide decides false / needs a contract change → give_up → BigSur) or
# by BigSur's own global cap (BIGSUR_MAX_INVOCATIONS). We removed the idle-minutes
# budget, the per-lemma chunk cap, and the run-level max-minutes ceiling — blunt
# timeouts killed slow-but-progressing proofs and forced churn. The guide keeps
# working (continue/decompose/research/fresh_start/give_up) until it or BigSur ends it.
# ENDGAME grace: chunks with 0 leaf-sorries but a not-yet-compiling proof — tracked
# ONLY to drive the guide-facing stuck_hint (no backstop consumes it anymore).
ENDGAME_GRACE_CHUNKS = 4
# BigSur — the repair agent of last resort. EVERY give-up that reaches
# _propagate_failure_to_parent escalates straight to BigSur (no local
# parent-reactivation first — a give-up's real cause usually lives ABOVE the parent,
# which a parent-only re-decompose cannot fix). BigSur is a powerful agent that may
# rewrite any contract/decomposition/ledger/snapshot ANYWHERE in the Sandbox except
# the root human signature. BIGSUR_DECISION_ROUNDS bounds the "are you done and
# consistent?" run_ai loop after BigSur's initial free-form repair run;
# BIGSUR_MAX_INVOCATIONS bounds how many times BigSur may be invoked across the whole
# run (a global backstop against a repair ↔ re-fail loop).
BIGSUR_DECISION_ROUNDS = 6
BIGSUR_MAX_INVOCATIONS = 100
# Turn budget for BigSur's initial free-form repair pass (the run_ai that reads the
# briefing + impact report and rewrites contracts/ledger/snapshots). Generous — a
# real repair reads many files and edits several — but bounded so a wedged pass is
# eventually reaped and the decision loop takes over.
BIGSUR_INITIAL_TURNS = 200
# Periodic full-swarm checkpoint interval (seconds). A safety net for a long grind
# with no proved lemma: if no full checkpoint has happened in this long, take one on
# the next chunk boundary. Any full checkpoint (proved-lemma / run-done) resets the
# clock, so this only fires when nothing else has checkpointed recently.
CHECKPOINT_INTERVAL_SECONDS = 3600  # 1 hour
# ProofResearcher — a deep-research pass the guide can request (the `research`
# decision) when a lemma is genuinely stuck. It reads the whole codebase for
# primitives/patterns/counterexamples and writes a findings report the writer and
# guide then read. RESEARCHER_TURNS bounds its initial free-form dig;
# RESEARCHER_DECISION_ROUNDS bounds the "have you finished the report?" loop that
# keeps it working until it attests done (like BigSur's decision loop).
RESEARCHER_TURNS = 120
RESEARCHER_DECISION_ROUNDS = 4


def _env_float(name: str, default: float) -> float:
    """Read a positive float from the environment, falling back to `default`."""
    try:
        v = float(os.environ.get(name, "").strip())
        return v if v > 0 else default
    except (ValueError, AttributeError):
        return default


# An agent's context window is rotated (swapped for a fresh instance) once usage
# crosses this. NOTE: the figure everywhere in this module is context *USED* —
# a LOW number means the agent has lots of runway left, NOT that it is exhausted.
# This same threshold sets the guide's runway bands (_runway_note): the guide
# perceives the writer as "FULL" once usage reaches it, which is the primary
# signal steering it toward `decompose`. Overridable so a test can LOWER it to make
# the guide decompose much earlier than a healthy proof would — driving the
# give-up/re-decompose churn that escalates to BigSur end-to-end (Layer 3).
CONTEXT_ROTATION_THRESHOLD = _env_float("STRATA_CONTEXT_ROTATION_PCT", 75.0)  # percent USED


def _runway_note(pct: float | None) -> str:
    """Render a writer's context-usage % as an unambiguous runway phrase for the
    guide's prompt.

    This exists because a bare "Writer context: 5%" was repeatedly misread by the
    guide as "5% left → exhausted" and triggered a premature `decompose` on turn 1
    (the number is context USED, so 5% means 95% free). We spell out both the
    number and its meaning so the signal cannot be inverted.

    We also state the DECOMPOSITION THRESHOLD explicitly — the context-usage %
    (CONTEXT_ROTATION_THRESHOLD, set by the user via STRATA_CONTEXT_ROTATION_PCT)
    at which the writer is "FULL" and decomposition becomes warranted — so the
    guide knows the exact point it is aiming at rather than inferring it from the
    band label alone.
    """
    used = pct or 0.0
    free = 100.0 - used
    thr = CONTEXT_ROTATION_THRESHOLD
    if used < thr * 0.6:                # < 60% of the threshold
        band = "HEALTHY — plenty of runway, keep the writer working"
    elif used < thr:                    # approaching the threshold
        band = "GETTING FULL — rotation approaching, wrap up soon"
    else:                               # at/over the threshold
        band = "FULL — will rotate to a fresh writer"
    return (f"Writer runway: {band} "
            f"({used:.0f}% of context USED, {free:.0f}% free). "
            f"Decomposition threshold (set by the user): {thr:.0f}% context USED — "
            f"decompose once usage reaches this and the writer is genuinely stuck.")


# ═══════════════════════════════════════════════════════════════════════════════
# State Machine
# ═══════════════════════════════════════════════════════════════════════════════

class Phase(str, Enum):
    INIT = "init"
    SELECT = "select"
    PROVE = "prove"
    EXTRACT = "extract"
    DETECT = "detect"
    UPDATE = "update"
    CHECK = "check"
    ASSEMBLING = "assembling"
    DONE = "done"
    FAILED = "failed"


class Trans(str, Enum):
    REGISTERED = "registered"
    PICKED = "picked"
    PROVED = "proved"
    HAS_SORRY = "has_sorry"
    CONTINGENT = "contingent"
    CONTRADICTORY = "contradictory"
    EXTRACTED = "extracted"
    CHECKED = "checked"
    NO_CYCLE = "no_cycle"
    ALL_PROVED = "all_proved"
    HAS_PENDING = "has_pending"
    BLOCKED = "blocked"
    ASSEMBLED = "assembled"
    ASSEMBLY_FAILED = "assembly_failed"
    RETRY = "retry"


TRANSITIONS: dict[tuple[str, str], str] = {
    (Phase.INIT, Trans.REGISTERED):       Phase.SELECT,
    (Phase.INIT, Trans.BLOCKED):          Phase.FAILED,

    (Phase.SELECT, Trans.PICKED):         Phase.PROVE,
    (Phase.SELECT, Trans.BLOCKED):        Phase.FAILED,

    (Phase.PROVE, Trans.PROVED):          Phase.UPDATE,
    (Phase.PROVE, Trans.HAS_SORRY):       Phase.EXTRACT,
    (Phase.PROVE, Trans.CONTINGENT):      Phase.UPDATE,
    (Phase.PROVE, Trans.CONTRADICTORY):   Phase.UPDATE,
    (Phase.PROVE, Trans.RETRY):           Phase.PROVE,

    (Phase.EXTRACT, Trans.EXTRACTED):     Phase.DETECT,
    (Phase.EXTRACT, Trans.RETRY):         Phase.PROVE,
    (Phase.EXTRACT, Trans.CONTRADICTORY): Phase.UPDATE,

    (Phase.DETECT, Trans.NO_CYCLE):       Phase.UPDATE,
    (Phase.DETECT, Trans.RETRY):          Phase.PROVE,
    (Phase.DETECT, Trans.CONTRADICTORY):  Phase.UPDATE,

    (Phase.UPDATE, Trans.CHECKED):        Phase.CHECK,

    (Phase.CHECK, Trans.ALL_PROVED):      Phase.ASSEMBLING,
    (Phase.CHECK, Trans.HAS_PENDING):     Phase.SELECT,
    (Phase.CHECK, Trans.BLOCKED):         Phase.FAILED,

    (Phase.ASSEMBLING, Trans.ASSEMBLED):          Phase.DONE,
    (Phase.ASSEMBLING, Trans.ASSEMBLY_FAILED):    Phase.FAILED,
    (Phase.ASSEMBLING, Trans.RETRY):              Phase.PROVE,
}


# ═══════════════════════════════════════════════════════════════════════════════
# State
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class LemmaContext:
    """Per-lemma communication channel between phases."""
    current_task: str = ""
    failure_context: str = ""
    needs_fresh_guide: bool = False
    needs_fresh_writer: bool = False


@dataclass
class PO5State:
    root_workspace: str = ""
    root_theorem_name: str = ""
    root_theorem_file: str = ""
    # Theorems the user explicitly requested. Empty = prove ALL sorry-theorems.
    requested_theorem_names: list[str] = field(default_factory=list)
    root_id: str = ""
    stage: str = "init"
    current_lemma_id: str = ""
    skip_soundness: bool = False
    # Cheat sheet (project-specific proof playbook) config. use_cheat_sheet=False
    # disables it entirely; cheat_sheet_path="" uses the bundled default.
    use_cheat_sheet: bool = True
    cheat_sheet_path: str = ""
    # TIER 2 backstop: hard upper bound (minutes) on the ENTIRE run wall-clock.
    # None ⇒ no hard stop (run until proved or the run is killed externally).
    max_run_minutes: float | None = None
    agent_registry: dict = field(default_factory=dict)
    lemma_ctx: dict = field(default_factory=dict)  # lemma_id → LemmaContext
    total_attempts: int = 0
    lemmas_proved: int = 0
    cycles_detected: int = 0
    # Full accumulated give-up reason(s), propagated to the Task Manager → user.
    give_up_reason: str = ""
    # If the guide, on giving up on a TOP-LEVEL requested theorem, says the user
    # must fix something (false/mis-stated goal, wrong def, missing hypothesis,
    # unavailable dependency), the specific request(s) are captured here.
    user_fix_request: str = ""
    # How many times the BigSur repair agent has been invoked this run. Bounded by
    # BIGSUR_MAX_INVOCATIONS — a global backstop against a repair ↔ re-fail loop.
    bigsur_invocations: int = 0
    # The LAST BigSur completion note (what it attested when it finished its most
    # recent repair, and on which lemma). Surfaced in the next SELECT so the guide
    # knows BigSur already ran — and doesn't re-give-up on a node BigSur just handled
    # (the callElim spin: the guide kept re-escalating the same node, unaware BigSur
    # had already attested "done, nothing to change"). Format: (lemma_name, note).
    last_bigsur_note: str = ""


def _read_hint(state: PO5State) -> str:
    """'the cheat sheet and the file' / 'the file' depending on cheat-sheet config."""
    return "the cheat sheet and the file" if cheat_sheet_name(
        state.use_cheat_sheet, state.cheat_sheet_path) else "the file"


# ═══════════════════════════════════════════════════════════════════════════════
# Guide APIs — the only way to interact with the guide
# ═══════════════════════════════════════════════════════════════════════════════

# Tools blocked while the orchestrator drives the guide via run_ai for strategy /
# a decision. The guide's reply TEXT is already copied into the writer's next
# prompt, so a send_message here would double-message the writer AND auto-start
# its listener out of sequence. wait_for_reply is blocked too: a blocking wait
# during a synchronous decision call would stall the orchestrator. Passed as bare
# names — blocked_tools_hooks matches on the MCP tool's final `__` segment.
_GUIDE_DECISION_BLOCK = ["send_message", "wait_for_reply"]

# Inline reminder prepended to every strategy/decision prompt, matching
# _GUIDE_DECISION_BLOCK. Told UP FRONT so the guide simply answers inline instead
# of attempting a send_message that the block hook would deny — a denied call
# still costs a turn. The hook stays as the failsafe.
_GUIDE_DECISION_NO_MSG = (
    "⚠️ ANSWER INLINE ONLY. Your reply text below is delivered to the writer "
    "automatically — do NOT call send_message or wait_for_reply in this response "
    "(they are disabled for this turn). You MAY still READ your mailbox first "
    "(get_messages_by_sender / get_thread / list_recent_messages / "
    "list_all_unread_mail) if you need to recall what you and the writer agreed — "
    "reading is fine; only sending is disabled. Then write your answer.\n\n"
)


async def _consult_guide_raw(agent, state: PO5State, ledger: LemmaLedger,
                              entry: LemmaEntry, cwd: Path,
                              task: str | None = None) -> str:
    """Send a prompt to the lemma's guide. Returns raw text.

    If task is None → prompt built from ctx.current_task + ctx.failure_context.
    If task is provided → sent as-is. Context is NOT consumed.
    """
    guide = await _get_guide(agent, entry, state, ledger)

    if task is None:
        ctx = state.lemma_ctx.get(entry.id)
        parts = []
        if ctx and ctx.current_task:
            parts.append(ctx.current_task)
        if ctx and ctx.failure_context:
            parts.append(f"⚠️ FAILURE:\n{ctx.failure_context}")
        task = "\n\n".join(parts) if parts else "Continue. Read the file and advise."

    result = await guide.run_ai(inp=_GUIDE_DECISION_NO_MSG + task,
                                block_tools=_GUIDE_DECISION_BLOCK)
    return result.raw_result or ""


async def _consult_guide_decide(agent, state: PO5State, ledger: LemmaLedger,
                                 entry: LemmaEntry, cwd: Path,
                                 options: list[str],
                                 task: str | None = None,
                                 post_prompt: str = "",
                                 post_prompt_parser: callable = None,
                                 ) -> tuple[str, str, dict]:
    """Send a prompt + force a structured decision.

    Returns (choice, reason, extras).
    extras is empty dict unless post_prompt_parser is provided.

    post_prompt: additional lines appended to the decision prompt (e.g. "TURNS: <50-100>")
    post_prompt_parser: callable(raw_text) -> dict of extra parsed fields
    """
    guide = await _get_guide(agent, entry, state, ledger)

    if task is None:
        ctx = state.lemma_ctx.get(entry.id)
        parts = []
        if ctx and ctx.current_task:
            parts.append(ctx.current_task)
        if ctx and ctx.failure_context:
            parts.append(f"⚠️ FAILURE:\n{ctx.failure_context}")
        task = "\n\n".join(parts) if parts else "Decide."

    options_str = " | ".join(options)
    prompt = (
        f"{_GUIDE_DECISION_NO_MSG}"
        f"{task}\n\n"
        f"DECIDE one of: [{options_str}]\n"
        f"Reply EXACTLY:\n"
        f"DECISION: <{options_str}>\n"
    )
    if post_prompt:
        prompt += post_prompt + "\n"
    prompt += "REASON: <one sentence>"

    result = await guide.run_ai(inp=prompt, block_tools=_GUIDE_DECISION_BLOCK)
    raw = result.raw_result or ""

    pattern = "|".join(re.escape(o) for o in options)
    match = re.search(rf'DECISION:\s*({pattern})', raw, re.IGNORECASE)
    reason_match = re.search(r'REASON:\s*(.+)', raw)

    decision = match.group(1).lower() if match else options[0]
    reason = reason_match.group(1).strip() if reason_match else raw[:100]
    extras = post_prompt_parser(raw) if post_prompt_parser else {}
    return decision, reason, extras


async def _dump_guide_to_disk(agent, state: PO5State, ledger: LemmaLedger,
                               entry: LemmaEntry, cwd: Path):
    """Legacy wrapper — rotation is now handled inside _get_guide/_get_writer."""
    pass


# ═══════════════════════════════════════════════════════════════════════════════
# Registration helper
# ═══════════════════════════════════════════════════════════════════════════════

def _register_lemma(state: PO5State, ledger: LemmaLedger, **kwargs) -> LemmaEntry | str:
    """Add lemma to ledger + initialize its LemmaContext."""
    entry = ledger.add_lemma(**kwargs)
    if not isinstance(entry, str):
        state.lemma_ctx[entry.id] = LemmaContext()
    return entry


async def _propagate_failure_to_parent(agent, state: PO5State, ledger: LemmaLedger,
                                        entry: LemmaEntry, cwd: Path, message: str):
    """A child gave up — ALWAYS escalate to BigSur, the repair agent.

    We do NOT try local parent-reactivation first. A give-up almost always means a
    decomposition boundary is wrong — the child's contract needs a fact (a
    well-formedness / freshness / shape hypothesis) that lives ABOVE the parent
    (see the terminal_sim reset-loop). A parent-only re-decompose cannot express
    that fix, so it just re-derives the same give-up until it exhausts its budget.
    Instead, on every give-up we go straight to `_run_bigsur`, which:
      1. Re-consults the give-up guide to scan the ancestry (ledger + SearchAgent)
         and produce an IMPACT REPORT of what must change and where.
      2. Spawns BigSur to rewrite whatever contracts/decompositions/ledger/snapshots
         are needed across the Sandbox to make the project self-consistent again —
         everything except the root human signature — or give up with an epiphany
         that the ROOT theorem itself is the problem (→ propagate to top and fail).

    Steps here just prepare the ground:
      1. Record the failure text on the parent's context.
      2. Prune the failed child's subtree so dead siblings/imports don't linger.
    """
    from .lemma_ledger import LemmaStatus

    parent = ledger.get_parent(entry.id)

    if parent is not None:
        parent_ctx = state.lemma_ctx.get(parent.id)
        if parent_ctx is None:
            parent_ctx = LemmaContext()
            state.lemma_ctx[parent.id] = parent_ctx
        # Record failure text (append — parent may have multiple failed children).
        if parent_ctx.failure_context:
            parent_ctx.failure_context += f"\n{message}"
        else:
            parent_ctx.failure_context = message

    # Prune the dead child's subtree (mark_failed already set the child FAILED;
    # prune_branch skips PROVED/FAILED roots, so prune its children explicitly).
    for cid in list(entry.children):
        ledger.prune_branch(cid, f"parent child '{entry.name}' gave up")

    # ALWAYS escalate to BigSur (guide impact-report consult happens inside).
    # BigSur is an AI agent and a LAST resort, so a failure to even run it (network
    # hiccup, model timeout, subprocess death) must NOT crash the whole proof run —
    # the phase loop does not wrap handler() in a try, so an exception here would
    # propagate out and abandon all work on every other lemma. Swallow it: log,
    # leave this lemma given-up, and let the rest of the run continue.
    try:
        await _run_bigsur(agent, state, ledger, entry, cwd, message)
    except Exception as e:
        await agent._emit("message",
            f"[PO5] ⚠️ BigSur failed to run on '{entry.name}' ({type(e).__name__}: {e}); "
            f"leaving it given-up and continuing.")
        _record_give_up(state, entry, f"BigSur invocation error: {e}")


# ═══════════════════════════════════════════════════════════════════════════════
# BigSur — the repair agent of last resort
# ═══════════════════════════════════════════════════════════════════════════════

def _root_signature_hash(cwd: Path, workspace: str) -> str | None:
    """SHA-256 of the pristine root signature file (Stub.clean.lean), or None if
    absent. Used to detect whether BigSur tampered with the immutable reference."""
    clean = cwd / workspace / "Stub.clean.lean"
    if not clean.exists():
        return None
    return hashlib.sha256(clean.read_bytes()).hexdigest()


async def _run_bigsur(agent, state: PO5State, ledger: LemmaLedger,
                      entry: LemmaEntry, cwd: Path, give_up_reason: str):
    """Escalate a give-up to BigSur, the repair agent of last resort.

    Flow:
      1. Re-consult the give-up guide (the one that owns `entry`) to scan the
         ancestry (ledger + SearchAgent) and produce an IMPACT REPORT of what needs
         to change and where.
      2. Hash the pristine root signature (Stub.clean.lean) so we can detect
         tampering afterward.
      3. Spawn BigSur (`run`, unlimited turns) with the give-up reason + impact
         report. BigSur may rewrite any contract/decomposition/ledger/snapshot in
         the Sandbox EXCEPT the root human signature, using its BigSur-only
         destructive ledger + snapshot MCPs.
      4. Loop a run_ai decision question — "is everything consistent (ledger, no
         stale snapshots, no bad decomposition, compiles)?" — until BigSur attests
         DONE, gives up with an epiphany, or we exhaust BIGSUR_DECISION_ROUNDS.
      5. Enforce the ONE hard rule: if the Stub.clean.lean hash changed, BigSur
         tampered with the immutable reference → treat as a failed repair and
         propagate to the top.
      6. If BigSur gave up (root theorem itself is wrong), record it as a user-fix
         request and fail the root. Otherwise BigSur re-opened work in the ledger;
         the main loop's next SELECT picks it up against the corrected contracts.
    """
    from .._bigsur_ledger_mcp import create_bigsur_ledger_mcp_server
    from .._bigsur_snapshot_mcp import create_bigsur_snapshot_mcp_server
    from .._bigsur_build_mcp import create_bigsur_build_mcp_server

    root_entry = ledger.get(state.root_id)

    # Global backstop: don't let BigSur churn forever against an unfixable project.
    if state.bigsur_invocations >= BIGSUR_MAX_INVOCATIONS:
        await agent._emit("message",
            f"[PO5] BigSur invocation cap reached ({BIGSUR_MAX_INVOCATIONS}); "
            f"propagating failure to root.")
        _record_give_up(state, root_entry or entry,
                        f"BigSur could not repair after {BIGSUR_MAX_INVOCATIONS} "
                        f"attempts; last give-up: {give_up_reason}")
        if root_entry:
            ledger.mark_failed(state.root_id, f"BigSur exhausted: {give_up_reason}")
        return
    state.bigsur_invocations += 1

    await agent._emit("message",
        f"[PO5] ⛰️  Escalating give-up on '{entry.name}' to BigSur "
        f"(#{state.bigsur_invocations}/{BIGSUR_MAX_INVOCATIONS}): {give_up_reason}")

    # 1. Impact report from the give-up guide (best-effort — BigSur can also scan).
    impact_report = ""
    try:
        impact_report = await _consult_guide_raw(
            agent, state, ledger, entry, cwd,
            task=(
                f"You gave up on '{entry.name}'. Reason: {give_up_reason}\n\n"
                f"Before we hand this to the BigSur repair agent, scan the ANCESTRY "
                f"of this lemma (use ledger_ancestry / ledger_get / ledger_children "
                f"on the ledger, and SearchAgent for the actual files) and produce a "
                f"concise IMPACT REPORT:\n"
                f"1. WHY is '{entry.name}' (or its failed child) unprovable AS STATED "
                f"— what fact/hypothesis is missing?\n"
                f"2. Which ANCESTOR actually HAS that fact (name + file)?\n"
                f"3. Which intermediate lemma SIGNATURES must be strengthened to "
                f"thread it down, and which decomposition files/ledger entries are "
                f"now stale and should be removed?\n"
                f"4. Could the ROOT human theorem itself be wrong? If so, why?\n"
                f"Answer as a numbered report — this is the brief BigSur will act on."
            ))
    except Exception as e:
        await agent._emit("message", f"[PO5] BigSur impact-report consult failed: {e}")

    # 2. Snapshot the immutable root reference so we can detect tampering.
    root_ws = root_entry.workspace if root_entry else entry.workspace
    clean_hash_before = _root_signature_hash(cwd, root_ws)

    # 3+4. Spawn BigSur with the destructive MCPs + the lake-build compile gate and
    # drive it to a consistent state.
    sandbox_root = cwd / state.root_workspace
    bigsur_ledger_mcp = create_bigsur_ledger_mcp_server(ledger)
    bigsur_snapshot_mcp = create_bigsur_snapshot_mcp_server(sandbox_root)
    bigsur_build_mcp = create_bigsur_build_mcp_server(cwd)

    root_name = root_entry.name if root_entry else state.root_theorem_name
    # If a ProofResearcher already investigated this lemma, its report is the ground
    # truth about feasibility — make it authoritative in the briefing so BigSur acts
    # on a proven GIVE_UP verdict instead of re-deriving the stale give-up reason.
    report_hint = _report_hint(entry, cwd)
    briefing = (
        f"A proof give-up has escalated to you.\n\n"
        f"FAILED LEMMA: {entry.name} (id={entry.id})\n"
        f"GIVE-UP REASON: {give_up_reason}\n\n"
        f"ROOT HUMAN THEOREM (DO NOT change its signature): {root_name}\n"
        f"Its pristine signature lives in {root_ws}/Stub.clean.lean — NEVER edit "
        f"that file.\n\n"
        f"GUIDE'S IMPACT REPORT:\n{impact_report or '(none — scan the ancestry yourself)'}\n\n"
        f"{report_hint}\n\n"
        f"IMPORTANT: if a ProofResearcher report above concludes the goal is FALSE / "
        f"unprovable as stated / needs a hypothesis the ROOT lacks, do NOT keep "
        f"'resetting to pending' or re-checking the build — VERIFY the report's "
        f"counterexample and, if it holds, GIVE UP with that epiphany. Re-queuing a "
        f"node whose report says it is false only spins this loop.\n\n"
        f"NOTE: the give-up may be a BUILD / OLEAN-CACHE blocker rather than a contract "
        f"defect — e.g. 'imports are out of date / must be rebuilt', a repeated identical "
        f"build failure (4294967294 / 'no such file'), or a stale-subtree olean gate that "
        f"the writer (which has no build tool) could not clear even on a byte-clean file. "
        f"If so, your FIRST move is to RUN THE BUILD: use `lake_build_check` on the named "
        f"module/subtree (build the dependencies bottom-up — children before parents) to "
        f"rebuild the stale oleans. That alone may clear the blocker with no contract change "
        f"needed; only rewrite contracts if the build then surfaces a real error.\n\n"
        f"Make the whole Sandbox self-consistent: strengthen the contracts that need "
        f"the missing hypotheses threaded down from the right ancestor, update the "
        f"corresponding ledger entries (ledger_update_signature / ledger_reset_to_pending "
        f"/ ledger_reparent), purge stale decomposition subtrees (ledger_purge_subtree) "
        f"and their files, and delete now-stale snapshots. LEAVE sorries in place — "
        f"provers close them later. Every file you touch must COMPILE (sorry warnings "
        f"OK, errors NOT) — verify with the `lake_build_check` tool (pass the file path; "
        f"it rebuilds oleans, so build the child you edited THEN its parent). Do NOT rely "
        f"on lean_diagnostic_messages after a cross-file edit: it will report 'imports "
        f"out of date', which is a rebuild signal, not an error. If the ROOT theorem "
        f"itself is wrong, give up with a clear epiphany instead of hacking around it."
    )

    gave_up = False
    epiphany = ""
    attested_note = ""  # BigSur's "done" reason — surfaced to the next SELECT
    async with swarm_agent(
        "bigsur", swarm=agent.swarm, cwd=agent._cwd,
        can_see=["SearchAgent"],
        extra_mcp_servers={"bigsur_ledger": bigsur_ledger_mcp,
                           "bigsur_snapshots": bigsur_snapshot_mcp,
                           "bigsur_build": bigsur_build_mcp},
        # Auto-compaction ENABLED (disable_compaction=False): a real repair reads
        # many files + runs builds over the BIGSUR_INITIAL_TURNS budget, so BigSur's
        # context fills up. Compaction (fired between turns inside run_ai once usage
        # crosses CONTEXT_COMPACT_THRESHOLD) lets it keep working instead of running
        # out of room. BigSur is non-checkpointable, so this is in-place compaction.
        disable_compaction=False,
    ) as bigsur:
        # Initial free-form repair pass. MUST use run_ai, NOT run(): BigSur is a
        # stateful agent (stateless=False), so run() sets _wait_after_completion
        # and never returns — it parks in the wait-for-messages loop after the
        # briefing, so the decision loop below would be unreachable and the whole
        # run hangs. run_ai drives exactly one bounded turn-budget and returns.
        await bigsur.run_ai(inp=briefing, max_turns=BIGSUR_INITIAL_TURNS)

        # Decision loop: keep asking until BigSur attests consistency or gives up.
        for round_i in range(BIGSUR_DECISION_ROUNDS):
            prompt = (
                "Decision check. Answer EXACTLY:\n"
                "DECISION: <done | not_done | give_up>\n"
                "REASON: <one sentence>\n\n"
                "Choose:\n"
                "- done: the ledger is consistent (no dangling refs, no cycles), all "
                "stale snapshots are deleted, bad decomposition files are removed, and "
                "every file you changed COMPILES (sorry OK, errors NOT). You have "
                "verified this — not merely intend to.\n"
                "- not_done: work remains; you will continue after answering.\n"
                "- give_up: the ROOT human theorem itself is wrong/unprovable — state "
                "the epiphany (counterexample or missing hypothesis) in REASON."
            )
            result = await bigsur.run_ai(inp=prompt, max_turns=60)
            raw = result.raw_result or ""
            m = re.search(r'DECISION:\s*(done|not_done|give_up)', raw, re.IGNORECASE)
            rm = re.search(r'REASON:\s*(.+)', raw)
            decision = m.group(1).lower() if m else "not_done"
            reason = rm.group(1).strip() if rm else raw[:200]
            if decision == "done":
                await agent._emit("message", f"[PO5] BigSur attests consistent: {reason}")
                attested_note = reason
                break
            if decision == "give_up":
                gave_up = True
                epiphany = reason
                await agent._emit("message", f"[PO5] BigSur gave up (epiphany): {reason}")
                break
            await agent._emit("message",
                f"[PO5] BigSur round {round_i+1}/{BIGSUR_DECISION_ROUNDS}: not done — {reason}")
            # Nudge it to keep fixing before the next check.
            await bigsur.run_ai(
                inp="Continue fixing until fully consistent, then I will re-check.",
                max_turns=80)
        else:
            await agent._emit("message",
                f"[PO5] BigSur exhausted {BIGSUR_DECISION_ROUNDS} decision rounds "
                f"without attesting done — proceeding with whatever it changed.")

    # Backstop-persist BigSur's live-ledger mutations to disk + regenerate the DAG
    # views the dashboard reads. BigSur is prompted to call ledger_save itself, but
    # we save here too so its DAG surgery is durable and shown correctly regardless
    # (the main loop's own save() only runs at the next phase boundary).
    ledger.save()

    # 5. Enforce the ONE hard rule: BigSur must not have touched Stub.clean.lean.
    clean_hash_after = _root_signature_hash(cwd, root_ws)
    if clean_hash_before is not None and clean_hash_after != clean_hash_before:
        await agent._emit("message",
            "[PO5] ⛔ BigSur TAMPERED with the root reference (Stub.clean.lean "
            "changed). Rejecting the repair and failing the root.")
        # Restore the reference from the current on-disk root Stub if possible is
        # unsafe (BigSur may have changed it too); simplest correct action is to
        # fail — the run cannot be trusted to preserve the human's theorem.
        _record_give_up(state, root_entry or entry,
                        "BigSur altered the immutable root signature reference "
                        "(Stub.clean.lean); repair rejected.")
        if root_entry:
            ledger.mark_failed(state.root_id,
                               "BigSur tampered with root signature reference")
        return

    # 6. Route the outcome.
    if gave_up:
        # BigSur's epiphany: the root theorem itself is the problem. Record as a
        # user-fix request and fail the root — this is the correct terminal state.
        request = f"'{root_name}': {epiphany}" if epiphany else \
                  f"'{root_name}': BigSur determined the theorem is unprovable as stated."
        if state.user_fix_request:
            state.user_fix_request += f"\n{request}"
        else:
            state.user_fix_request = request
        _record_give_up(state, root_entry or entry,
                        f"BigSur epiphany — root unfixable: {epiphany}")
        if root_entry:
            ledger.mark_failed(state.root_id, f"BigSur epiphany: {epiphany}")
        await agent._emit("message",
            f"[PO5] BigSur propagated failure to root '{root_name}': {epiphany}")
        return

    # BigSur repaired the project: it re-opened work in the ledger (reset_to_pending /
    # update_signature). Any cached guide/writer now holds a STALE contract in its
    # context, so tear them ALL down — the next SELECT rebuilds fresh agents that
    # read the corrected ledger + files (a torn-down instance is recreated by
    # _get_guide/_get_writer regardless of the needs_fresh flags).
    #
    # NOTE: we deliberately do NOT clear state.current_lemma_id here. The give-up
    # call sites return a transition (several go PROVE/EXTRACT/DETECT → UPDATE,
    # which dereferences current_lemma_id) and BigSur may have DELETED that entry.
    # _phase_update tolerates a missing entry (guarded); the subsequent CHECK →
    # SELECT then picks fresh work from the corrected ledger.
    #
    # Record what BigSur just did on this node, keyed to the node, so the NEXT SELECT
    # can tell the guide "BigSur already ran on <lemma> and attested: <note>". Without
    # this the guide re-picks the same node blind to BigSur's work and re-gives-up
    # with the same reason → the repair↔re-fail spin (callElim: same root, ~10×).
    note = attested_note or ("(exhausted decision rounds without attesting done)")
    state.last_bigsur_note = (
        f"BigSur (invocation #{state.bigsur_invocations}) just ran on '{entry.name}' "
        f"and attested: {note}")
    await _cleanup_all_agents(agent)
    await agent._emit("message",
        f"[PO5] BigSur repair complete; resuming proof search against corrected contracts.")


def _existing_report(entry: LemmaEntry, cwd: Path) -> tuple[list[str], str] | None:
    """If any ProofResearcher report exists for this entry, return (report_paths,
    recommendation), else None.

    A report is authored by the researcher (see _run_researcher) into
    <workspace>/reports/ and is the GROUND TRUTH about the lemma's feasibility — it
    may say GIVE_UP with a counterexample. That verdict must be surfaced INTO the
    writer/guide/BigSur prompts, not left sitting on disk: in the callElim run the
    report reached GIVE_UP early, but the give-up→BigSur pipeline kept re-deriving
    the stale build-gate reason and spun BigSur ~10× before the verdict was acted on.

    Robustness: we do NOT gate on the canonical `<name>.md` filename or on a regex
    matching. We return the PATH(S) of every report file in the dir unconditionally
    (the writer/guide/BigSur must be TOLD the path to read even if we can't parse a
    verdict for them). `recommendation` is a best-effort parse of a RECOMMENDATION /
    Verdict line — '' if none matched, which is fine: the path is still surfaced so
    the agent reads the report itself."""
    reports_dir = cwd / f"{entry.workspace}/reports"
    try:
        if not reports_dir.is_dir():
            return None
        files = sorted(p for p in reports_dir.glob("*.md")
                       if p.is_file() and p.stat().st_size > 0)
    except OSError:
        return None
    if not files:
        return None
    # Prefer the canonical <name>.md for verdict parsing, else the first report.
    canonical = reports_dir / f"{entry.name}.md"
    primary = canonical if canonical in files else files[0]
    rec = ""
    try:
        text = primary.read_text()
        m = re.search(r'RECOMMENDATION:\s*([^\n]+)', text, re.IGNORECASE) \
            or re.search(r'Verdict:\s*([^\n]+)', text, re.IGNORECASE)
        if m:
            rec = m.group(1).strip()
    except OSError:
        pass
    # Workspace-relative paths (what the agents' Read tool expects).
    rels = [f"{entry.workspace}/reports/{p.name}" for p in files]
    # Put the canonical/primary first so the strongest signal leads.
    prim_rel = f"{entry.workspace}/reports/{primary.name}"
    rels = [prim_rel] + [r for r in rels if r != prim_rel]
    return rels, rec


def _report_hint(entry: LemmaEntry, cwd: Path) -> str:
    """A prompt fragment pointing writer/guide/BigSur at existing research report(s)
    and their recommendation, or '' if none. The PATH is ALWAYS surfaced (even when
    no verdict could be parsed) so the agent can Read the report itself — the whole
    point is that the report must never sit unread on disk."""
    found = _existing_report(entry, cwd)
    if not found:
        return ""
    report_rels, rec = found
    primary = report_rels[0]
    others = report_rels[1:]
    rec_line = f" Its RECOMMENDATION/verdict: {rec}." if rec else \
        " (Recommendation not auto-parsed — READ the report to get its verdict.)"
    extra = f" Other reports here: {', '.join(others)}." if others else ""
    return (
        f"\n\n📄 A ProofResearcher report ALREADY EXISTS for this lemma at "
        f"{primary}.{rec_line}{extra} READ IT (Read {primary}) and take its findings "
        f"as authoritative — if it proves the goal is FALSE / needs a signature change, "
        f"do NOT re-hunt in-file: act on the report (give_up → BigSur / human), do not "
        f"re-diagnose from scratch."
    )


async def _run_researcher(agent, state: PO5State, ledger: LemmaLedger,
                          entry: LemmaEntry, cwd: Path, stub_rel: str,
                          reason: str) -> str | None:
    """Spawn a ProofResearcher for a stuck lemma. It reads the whole codebase for
    primitives/patterns/counterexamples and writes ONE findings report into
    <workspace>/reports/, which the writer + guide then read. It does NOT prove and
    can Write/Edit ONLY inside that reports dir (asymmetric hook). Returns the
    workspace-relative report path, or None if no report was produced.

    Runs like BigSur: an initial free-form dig (RESEARCHER_TURNS), then a decision
    loop that keeps it working until it attests the report is COMPLETE (done) or we
    exhaust RESEARCHER_DECISION_ROUNDS — so a shallow first pass gets pushed to
    finish (verify a skeleton, reach a clear PROCEED/GIVE_UP recommendation) rather
    than stopping half-done.
    """
    workspace = entry.workspace
    reports_dir_rel = f"{workspace}/reports"
    (cwd / reports_dir_rel).mkdir(parents=True, exist_ok=True)  # create on the fly
    report_name = f"{entry.name}.md"
    report_rel = f"{reports_dir_rel}/{report_name}"

    # Show the guide's live review of the current sorry state so the researcher
    # targets the actual open goals.
    tools = get_lean_tools()
    try:
        goal_note = _format_sorry_map(
            tools.transitive_sorry_map(stub_rel, []), set(), set()) or ""
    except Exception:
        goal_note = ""

    briefing = (
        f"A lemma is STUCK and the guide wants deep research before the writer tries again.\n\n"
        f"TARGET LEMMA: {entry.name}\n"
        f"FILE: {stub_rel}\n"
        f"WHY STUCK (guide): {reason}\n\n"
        f"{goal_note}\n\n"
        f"Investigate across the WHOLE codebase (Read/grep anywhere — do NOT rely on "
        f"SearchAgent alone): find the primitives, the proof pattern / induction shape, "
        f"and check feasibility (look for a counterexample or missing hypothesis). You "
        f"MAY scratch-verify a candidate skeleton with lean_run_code, but do NOT prove "
        f"the lemma and do NOT edit any proof file.\n\n"
        f"Write your findings report to EXACTLY this path (your only writable location): "
        f"{report_rel}\n"
        f"Follow the report structure in your instructions. Be concrete and concise."
    )

    from .hooks import research_workspace_hooks
    research_hooks = research_workspace_hooks(reports_dir_rel)

    await agent._emit("message",
        f"[PO5] 🔬 Spawning ProofResearcher for '{entry.name}' → report at {report_rel}")

    async with swarm_agent(
        "proof_researcher", swarm=agent.swarm, cwd=agent._cwd,
        can_see=["SearchAgent"],
        extra_hooks=research_hooks,
        # Auto-compaction ENABLED: a deep dig reads many library files over the
        # turn budget, so its context fills up; compaction lets it keep going.
        disable_compaction=False,
    ) as researcher:
        # Initial free-form dig.
        await researcher.run_ai(inp=briefing, max_turns=RESEARCHER_TURNS)

        # Decision loop: keep it working until the report is COMPLETE **and the
        # researcher is genuinely CONFIDENT in its PROCEED/GIVE_UP verdict**. The
        # feasibility verdict feeds the guide's give_up decision, so a shaky call is
        # worse than none: a wrong PROCEED sends the writer to grind an unprovable
        # goal; a wrong GIVE_UP escalates a provable one. We therefore do NOT let it
        # exit on a merely-complete report — it must attest CONFIDENCE, or explicitly
        # mark the verdict UNCERTAIN in the report (with what it would take to decide)
        # instead of guessing PROCEED/GIVE_UP. If unsure, it keeps digging.
        for round_i in range(RESEARCHER_DECISION_ROUNDS):
            prompt = (
                "Report check. Answer EXACTLY:\n"
                "DECISION: <done | not_done>\n"
                "CONFIDENCE: <high | medium | low>\n"
                "REASON: <one sentence>\n\n"
                f"- done: REQUIRES BOTH (1) the report at {report_rel} is COMPLETE — "
                "names concrete primitives with locations, the proof shape, any "
                "counterexample/missing-hypothesis, ends with a RECOMMENDATION line; "
                "AND (2) you are genuinely CONFIDENT (high) in the PROCEED/GIVE_UP "
                "verdict, having checked it RIGOROUSLY. For a feasibility claim this "
                "means you traced the ACTUAL definitions, not a plausible-sounding "
                "sketch — e.g. for a well-formedness/footprint goal you enumerated the "
                "FULL footprint (BOTH the modified/written set AND the read set / "
                "getVars, including free vars of every emitted assert/assume), not just "
                "the easy half. If a scratch skeleton is claimed, you actually ran it "
                "through lean_run_code. If you are NOT confident, you are NOT done — "
                "answer not_done and keep digging.\n"
                "- not_done: unresolved uncertainty remains; you will continue.\n\n"
                "If after genuine effort you CANNOT reach a confident PROCEED/GIVE_UP, "
                "that is a legitimate outcome — but you must then make the report's "
                "RECOMMENDATION line say `UNCERTAIN` and state exactly what you could "
                "not resolve and what would settle it. Never dress up an unresolved "
                "question as a confident PROCEED or GIVE_UP."
            )
            result = await researcher.run_ai(inp=prompt, max_turns=40)
            raw = result.raw_result or ""
            m = re.search(r'DECISION:\s*(done|not_done)', raw, re.IGNORECASE)
            rdecision = m.group(1).lower() if m else "not_done"
            cm = re.search(r'CONFIDENCE:\s*(high|medium|low)', raw, re.IGNORECASE)
            confidence = cm.group(1).lower() if cm else "low"
            rm = re.search(r'REASON:\s*(.+)', raw)
            rreason = rm.group(1).strip() if rm else ""
            # Exit ONLY on done + high confidence. A done-but-not-confident answer is
            # treated as not_done UNLESS it is the last round (then we accept whatever
            # it has, but it should already read UNCERTAIN per the instruction).
            if rdecision == "done" and confidence == "high":
                await agent._emit("message",
                    f"[PO5] ProofResearcher attests report complete (confident): {rreason}")
                break
            if rdecision == "done":
                await agent._emit("message",
                    f"[PO5] ProofResearcher says done but confidence={confidence} — "
                    f"NOT accepting; pushing for certainty or an explicit UNCERTAIN verdict.")
            else:
                await agent._emit("message",
                    f"[PO5] ProofResearcher round {round_i+1}/{RESEARCHER_DECISION_ROUNDS}: "
                    f"not done — {rreason}")
            await researcher.run_ai(
                inp=(f"You are not yet CONFIDENT. Keep digging and finish the report at "
                     f"{report_rel}. For any feasibility claim, verify it against the "
                     f"ACTUAL definitions and enumerate the FULL footprint (writes AND "
                     f"reads / getVars of every emitted statement, including assert/assume "
                     f"free vars) before concluding. Reach a HIGH-confidence PROCEED or "
                     f"GIVE_UP with named primitives (and a scratch-verified skeleton if "
                     f"you claim one) — OR, if you genuinely cannot decide, write "
                     f"RECOMMENDATION: UNCERTAIN and state what would settle it. Then I re-check."),
                max_turns=RESEARCHER_TURNS)
        else:
            await agent._emit("message",
                f"[PO5] ProofResearcher exhausted {RESEARCHER_DECISION_ROUNDS} rounds "
                f"without a confident verdict — using whatever report it produced "
                f"(should read UNCERTAIN if it never reached certainty).")

    # Verify a report was actually written.
    if (cwd / report_rel).exists() and (cwd / report_rel).read_text().strip():
        await agent._emit("message",
            f"[PO5] ProofResearcher report ready: {report_rel}")
        return report_rel
    await agent._emit("message",
        f"[PO5] ProofResearcher produced no report; continuing without one.")
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# Main entry point
# ═══════════════════════════════════════════════════════════════════════════════

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    start_time = _time.time()
    await agent._emit("status_change", "running")
    agent._po4_start_time = start_time

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    # Parse input
    if isinstance(inp, dict):
        workspace_rel = inp.get("workspace", "")
        # theorem_names: explicit list of targets. Empty/absent → prove ALL
        # sorry-theorems in the file. `theorem_name` (singular) is accepted for
        # backward compatibility and folded into the list.
        theorem_names = list(inp.get("theorem_names") or [])
        single = inp.get("theorem_name", "")
        if single and single not in theorem_names:
            theorem_names.append(single)
        theorem_file = inp.get("theorem_file", "")
        skip_soundness = inp.get("skip_soundness", False)
        use_cheat_sheet = inp.get("use_cheat_sheet", True)
        cheat_sheet_path = inp.get("cheat_sheet_path", "") or ""
        max_run_minutes = inp.get("max_run_minutes", None)
    else:
        workspace_rel = str(inp) if inp else ""
        theorem_names, theorem_file = [], ""
        skip_soundness = False
        use_cheat_sheet = True
        cheat_sheet_path = ""
        max_run_minutes = None

    if not workspace_rel:
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"phase": "failed", "error": "no workspace"})

    state = _load_state(cwd, workspace_rel)
    if not state:
        state = PO5State(
            root_workspace=workspace_rel,
            requested_theorem_names=theorem_names,
            root_theorem_file=theorem_file,
            skip_soundness=skip_soundness,
            use_cheat_sheet=use_cheat_sheet,
            cheat_sheet_path=cheat_sheet_path,
            max_run_minutes=(float(max_run_minutes) if max_run_minutes else None),
        )

    ledger = LemmaLedger(cwd / workspace_rel / "lemma_ledger.json")
    agent._workflow_state = state

    # Stale state recovery: if state references a lemma not in ledger, reset to init
    if state.stage != "init" and state.current_lemma_id:
        if ledger.get(state.current_lemma_id) is None:
            await agent._emit("message", "[PO5] Stale state (lemma not in ledger) — resetting to init")
            state.stage = "init"
            state.current_lemma_id = ""
            state.root_id = ""

    _target_desc = ", ".join(theorem_names) if theorem_names else "ALL sorry-theorems"
    await agent._emit("message", f"[PO5] Starting: {_target_desc} in {workspace_rel} (phase={state.stage})")

    # ─── INIT ─────────────────────────────────────────────────────────────
    if state.stage == "init":
        await agent._emit("message", "[PO5] Phase: INIT")
        stub_rel = f"{workspace_rel}/Stub.lean"

        # Sweep any leftover decomposed_old_* dirs from prior runs (the retired
        # rotation). New runs never create them, but stale ones on disk confuse
        # list_theorems / oracle scans, so clear them at startup.
        _sweep_decomposed_old(cwd)

        if not (cwd / workspace_rel / "Stub" / "Def.lean").exists():
            split_outcome = await run_splitter(agent, workspace_rel, stub_rel)
            # HARD GATE: a split that does not verify (e.g. a dropped `set_option
            # warningAsError false` so Stub.lean no longer compiles) must NOT flow
            # downstream — every later phase assumes a compiling Stub, and we are
            # about to snapshot Stub.lean into the pristine Stub.clean.lean below.
            # Refuse to proceed on a broken split rather than corrupt the reference.
            if split_outcome is not None and not split_outcome.success:
                err = getattr(split_outcome, "last_error", "") or "split did not verify"
                await agent._emit("message",
                    f"[PO5] ⛔ INIT split FAILED to produce compiling files ({err}). "
                    f"Refusing to proceed — a non-compiling Stub would poison every "
                    f"downstream phase and Stub.clean.lean.")
                state.stage = "failed"
                _save_state(cwd, state)
                return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                                   output={"phase": "failed",
                                           "error": f"splitter produced non-compiling files: {err}"})

        stub_clean = cwd / workspace_rel / "Stub.clean.lean"
        if not stub_clean.exists():
            shutil.copy2(cwd / stub_rel, stub_clean)

        # Copy the cheat sheet into the sandbox so the guide can read it. This is
        # a common silent-failure point: if the configured path doesn't resolve
        # against cwd, copy_cheat_sheet returns None and the guide later reports
        # "cheat sheet inaccessible". Surface the outcome explicitly.
        if state.use_cheat_sheet:
            copied = copy_cheat_sheet(cwd, cwd / workspace_rel,
                                      state.use_cheat_sheet, state.cheat_sheet_path)
            if copied:
                await agent._emit("message",
                    f"[PO5] Cheat sheet ready in sandbox: {copied}")
            else:
                src = cheat_sheet_source(cwd, state.use_cheat_sheet, state.cheat_sheet_path)
                cfg = state.cheat_sheet_path or "(bundled default)"
                await agent._emit("message",
                    f"[PO5] ⚠️ Cheat sheet ENABLED but NOT copied — guide will run "
                    f"WITHOUT it. Configured path: {cfg}; resolved source: "
                    f"{src or 'NOT FOUND'} (cwd: {cwd}).")

        tools = get_lean_tools()
        split = tools.split_theorems(stub_rel)
        if not split.blocks:
            state.stage = "failed"
            _save_state(cwd, state)
            return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                               output={"phase": "failed", "error": "no theorems in Stub.lean"})

        # Collect top-level proof obligations ("targets"): each standalone
        # theorem/def with sorry, or a whole mutual group (collapsed to one
        # representative) containing sorry.
        all_targets = _collect_sorry_targets(split)

        # Narrow to the user's requested theorems if any were named; an empty
        # request means "prove ALL sorry-theorems in the file".
        targets = _filter_requested_targets(
            all_targets, split, state.requested_theorem_names)
        if state.requested_theorem_names:
            matched = {b.name for b, _ in targets}
            unmatched = [n for n in state.requested_theorem_names
                         if n not in matched and not any(
                             b.mutual_group is not None
                             and n in split.mutual_groups.get(b.mutual_group, [])
                             for b, _ in targets)]
            if unmatched:
                await agent._emit("message",
                    f"[PO5] Requested theorems with no sorry / not found (skipped): {unmatched}")
            if not targets:
                await agent._emit("message",
                    "[PO5] None of the requested theorems have sorry — proving all sorry-targets instead")
                targets = all_targets

        # Decide single-root vs. synthetic-file-root.
        # Single root (behavior unchanged) when there is at most one target.
        # Synthetic root when ≥2 targets share the file — each becomes a child
        # obligation under a "whole file proved" root.
        if len(targets) <= 1:
            if targets:
                root_block = targets[0][0]
            else:
                # Nothing has sorry — register the last declaration so CHECK can
                # immediately recognize the file as already proven.
                root_block = split.blocks[-1]
            state.root_theorem_name = root_block.name

            sig_hash = LemmaLedger.compute_signature_hash(root_block.text)
            root_entry = _register_lemma(state, ledger,
                name=state.root_theorem_name, file_path=stub_rel,
                workspace=workspace_rel, signature_hash=sig_hash,
                statement=root_block.text,
            )
            if isinstance(root_entry, str):
                state.stage = "failed"
                _save_state(cwd, state)
                return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                                   output={"phase": "failed", "error": root_entry})
            state.root_id = root_entry.id
        else:
            # Multiple sorry-targets in one file: synthetic "file" root whose
            # completion means "every target in Stub.lean is sorry-free". It is
            # never proven by a writer — _propagate_proved promotes it once its
            # whole subtree (the shared file) is sorry-free.
            file_label = f"<file:{workspace_rel}/Stub.lean>"
            state.root_theorem_name = file_label
            root_entry = _register_lemma(state, ledger,
                name=file_label, file_path=stub_rel,
                workspace=workspace_rel,
                signature_hash=LemmaLedger.compute_signature_hash(file_label),
                statement=f"-- all {len(targets)} top-level theorems in {stub_rel} proved",
            )
            if isinstance(root_entry, str):
                state.stage = "failed"
                _save_state(cwd, state)
                return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                                   output={"phase": "failed", "error": root_entry})
            state.root_id = root_entry.id
            ledger.mark_contingent(root_entry.id)

            registered = 0
            for block, is_mut in targets:
                child = _register_lemma(state, ledger,
                    name=block.name, file_path=stub_rel,
                    workspace=workspace_rel,
                    signature_hash=LemmaLedger.compute_signature_hash(block.text),
                    statement=block.text, is_mutual=is_mut,
                    parent_id=root_entry.id)
                if not isinstance(child, str):
                    registered += 1
            await agent._emit("message",
                f"[PO5] Multi-theorem file: registered {registered} sorry-targets under synthetic root")

        state.stage = "select"
        ledger.save()
        _save_state(cwd, state)
        await agent._emit("state_transition", {"from": "init", "transition": "registered", "to": "select"})

    # Reset any PROVING entries to PENDING (crash recovery)
    for e in ledger.entries():
        if e.status == LemmaStatus.PROVING:
            e.status = LemmaStatus.PENDING

    # ─── State machine loop ───────────────────────────────────────────────
    HANDLERS = {
        Phase.SELECT:     lambda: _phase_select(agent, state, ledger, cwd),
        Phase.PROVE:      lambda: _phase_prove(agent, state, ledger, cwd),
        Phase.EXTRACT:    lambda: _phase_extract(agent, state, ledger, cwd),
        Phase.DETECT:     lambda: _phase_detect(agent, state, ledger, cwd),
        Phase.UPDATE:     lambda: _phase_update(agent, state, ledger, cwd),
        Phase.CHECK:      lambda: _phase_check(agent, state, ledger, cwd),
        Phase.ASSEMBLING: lambda: _phase_assemble(agent, state, ledger, cwd),
    }

    while state.stage not in ("done", "failed") and not agent.cancellation.is_cancelled:
        try:
            phase = Phase(state.stage)
        except ValueError:
            await agent._emit("message", f"[PO5] ERROR: invalid stage '{state.stage}'")
            state.stage = "failed"
            break

        handler = HANDLERS.get(phase)
        if not handler:
            state.stage = "failed"
            break

        transition = await handler()
        next_stage = TRANSITIONS.get((phase, transition))
        if next_stage is None:
            await agent._emit("message", f"[PO5] ERROR: no transition ({state.stage}, {transition.value})")
            state.stage = "failed"
            break

        await agent._emit("state_transition", {
            "from": state.stage, "transition": transition.value, "to": next_stage.value})
        state.stage = next_stage.value
        ledger.save()
        _save_state(cwd, state)

    # ─── Done ─────────────────────────────────────────────────────────────
    # Tear down every persistent writer/guide listen task. Most instances are
    # cached on `agent` per lemma-id and reused (never rotated/cleaned up on the
    # proved path), so their _listen_messages tasks would otherwise outlive the
    # workflow — a 1s-polling coroutine per instance holding a backend. Sweep all
    # of them here so no listener leaks past the run.
    await _stop_all_listeners(agent)

    elapsed = _time.time() - start_time
    total_cost = getattr(agent.swarm, '_total_cost', 0.0) if hasattr(agent, 'swarm') else 0.0
    await agent._emit("message",
        f"[PO5] Finished: stage={state.stage}, proved={state.lemmas_proved}, "
        f"cycles={state.cycles_detected}, time={elapsed/60:.1f}min, cost=${total_cost:.2f}")
    # Final consistent checkpoint (proof state + full swarm). NOTE: the old code
    # here called `_checkpoint_manager.save(...)`, which does not exist (the method
    # is the async `create`/`swarm.checkpoint`) — it silently no-op'd under the bare
    # except. _checkpoint uses the real async path.
    await _checkpoint(agent, ledger, cwd, state, reason="prover_done")

    status = AgentStatus.COMPLETED if state.stage == "done" else AgentStatus.FAILED
    return AgentResult(name=agent.spec.name, status=status,
                       output={"stage": state.stage, "proved": state.lemmas_proved,
                               "cycles": state.cycles_detected,
                               # Full give-up reason(s) + any user-fix request, so
                               # the Task Manager can relay them to the user.
                               "give_up_reason": state.give_up_reason,
                               "user_fix_request": state.user_fix_request})


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: SELECT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_select(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Pick next lemma. Parent's guide chooses among pending children."""
    if not ledger.has_pending():
        return Trans.BLOCKED

    # BigSur nomination wins outright. A boosted-PENDING entry is a deliberate
    # nomination — almost always BigSur having just re-opened THE node that must be
    # proved next (update_signature / reset_to_pending set priority_boost). Pick it
    # directly, BYPASSING the DFS-walk and the guide consultation: the guide lacks
    # BigSur's just-computed repair context and re-litigates ("pick the hardest
    # child") into root/sibling churn — the callElim defUseWF loop, where the one
    # node BigSur re-opened kept losing the guide's vote to the root. mark_proving
    # clears the boost, so the nomination fires exactly once.
    nominated = ledger.pick_boosted()
    if nominated is not None:
        state.current_lemma_id = nominated.id
        ledger.mark_proving(nominated.id)
        await agent._emit("message", f"[PO5] Selected (BigSur nomination): {nominated.name}")
        return Trans.PICKED

    parent_entry, pending_kids = _find_dfs_candidates(ledger, state.current_lemma_id)

    if not pending_kids:
        lemma = ledger.pick_next()
        if lemma is None:
            return Trans.BLOCKED
        state.current_lemma_id = lemma.id
        ledger.mark_proving(lemma.id)
        await agent._emit("message", f"[PO5] Selected (fallback): {lemma.name}")
        return Trans.PICKED

    if len(pending_kids) == 1:
        winner = pending_kids[0]
        state.current_lemma_id = winner.id
        ledger.mark_proving(winner.id)
        await agent._emit("message", f"[PO5] Selected (only child): {winner.name}")
        return Trans.PICKED

    # Multiple candidates — ask parent's guide
    if parent_entry:
        children_desc = "\n".join(
            f"  {i+1}. {c.name} (depth={c.depth}) (#lemmas using this={len(ledger.get_all_parents(c.id))}) — {(c.statement or '')[:80]}"
            for i, c in enumerate(pending_kids))
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, parent_entry, cwd,
            options=[c.id[:8] for c in pending_kids],
            task=(
                f"Your lemma '{parent_entry.name}' has these pending children:\n{children_desc}\n\n"
                f"Which should we prove NEXT? Pick the hardest/most general one."
            ))
        for c in pending_kids:
            if c.id.startswith(decision) or decision in c.name.lower():
                state.current_lemma_id = c.id
                ledger.mark_proving(c.id)
                await agent._emit("message", f"[PO5] Guide selected: {c.name}")
                return Trans.PICKED

    # Fallback
    pending_kids.sort(key=lambda e: (len(ledger.get_all_parents(e.id)), -e.depth, -e.attempts), reverse=True)
    winner = pending_kids[0]
    state.current_lemma_id = winner.id
    ledger.mark_proving(winner.id)
    await agent._emit("message", f"[PO5] Selected (depth fallback): {winner.name}")
    return Trans.PICKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: PROVE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_prove(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Attempt proof of current lemma via guide + writer loop."""
    entry = ledger.get(state.current_lemma_id)
    result = await _attempt_prove(agent, state, ledger, entry, cwd)
    state.total_attempts += 1

    if result == "proved":
        state.lemmas_proved += 1
        # Always FULL-checkpoint when a lemma is proved — this is the single funnel
        # every prove path (main / max-depth / grace) returns through. A proved lemma
        # is durable progress that must never be redone, so we persist BOTH the proof
        # state AND the whole swarm (session ids + workspace snapshot) here, so it
        # survives a prover re-dispatch AND a full dashboard restart.
        await _checkpoint(agent, ledger, cwd, state, reason=f"lemma_proved:{entry.name}")
        return Trans.PROVED
    elif result == "contingent":
        return Trans.CONTINGENT
    elif result == "has_sorry":
        return Trans.HAS_SORRY
    elif result == "retry":
        return Trans.RETRY
    else:
        # result == "failed". EVERY "failed" return from _attempt_prove has ALREADY
        # run its own mark_failed + _propagate_failure_to_parent (→ BigSur) — the
        # give-up / max-depth / grace / user-timeout / post-research paths all do so
        # before returning. So we must NOT re-propagate here.
        #
        # The old `if entry.status != LemmaStatus.FAILED` guard tried to prevent the
        # double-escalation, but it was DEFEATED by BigSur itself: when BigSur runs
        # inside that first propagation and calls reset_to_pending / update_signature,
        # it flips the entry's status FAILED → PENDING. Control then returns here,
        # the guard sees "not FAILED", and fires a SECOND BigSur escalation with the
        # contentless "failed: failed" reason — BigSur #2 for a problem BigSur #1 just
        # handled (observed live: the @[expose] fix was landed by #1, then #2 fired
        # on resume). The failure lifecycle is owned entirely by _attempt_prove; here
        # we only surface the transition so CHECK → SELECT picks up the re-opened work.
        return Trans.CONTRADICTORY


async def _attempt_prove(agent, state: PO5State, ledger: LemmaLedger,
                         entry: LemmaEntry, cwd: Path) -> str:
    """Guide-driven proof loop. Returns: proved | has_sorry | failed | retry"""
    tools = get_lean_tools()
    ctx = state.lemma_ctx.get(entry.id)
    if not ctx:
        ctx = LemmaContext()
        state.lemma_ctx[entry.id] = ctx

    stub_rel = _resolve_stub(entry, cwd, state)

    # Repair inconsistent state: if decomposed/ exists but Stub.lean doesn't import from it,
    # the extraction was lost (e.g. process crash). Re-add imports to make the file slim.
    _repair_orphaned_decomposed(entry, cwd, stub_rel)

    original_content = (cwd / stub_rel).read_text()

    # Ensure the cheat sheet (if any) exists in the workspace
    ws_path = cwd / entry.workspace
    copy_cheat_sheet(cwd, ws_path, state.use_cheat_sheet, state.cheat_sheet_path)

    writer = await _get_writer(agent, entry, state, ledger)
    # Keep the writer live and reactive for the WHOLE lemma. Between chunks (when no
    # run_ai drives it) this lets the guide's decision-phase questions reach the
    # writer immediately; during a chunk the writer's own run_ai owns the session
    # (via _driving_lock) and this listener parks. See _ensure_listening.
    _ensure_listening(agent, writer)
    verify_fn = _make_verifier(entry, stub_rel, original_content, ledger, cwd)
    protected_names = _get_protected_names(tools, stub_rel, entry)

    # In a shared multi-theorem file, tell the writer to touch ONLY its target and
    # leave sibling obligations' sorry in place (they are proved in their own turn).
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    scope_note = ""
    if siblings:
        scope_note = (
            f"\n\n⚠️ SHARED FILE: prove ONLY {sorted(protected_names)}. "
            f"Other theorems here ({sorted(siblings)}) are proved separately — "
            f"leave their `sorry` untouched and do NOT modify or delete them."
        )
    # If a ProofResearcher already investigated this lemma, point the writer at the
    # report so it follows the proven proof-shape / primitives instead of re-hunting.
    scope_note += _report_hint(entry, cwd)

    # ── Step 1: Initial advice ──
    # If BigSur just ran (this lemma was re-opened by a repair), tell the guide up
    # front — so it does NOT immediately re-give-up on a node BigSur already handled.
    # Consumed once (cleared after folding in), so it only colors this fresh start.
    bigsur_note = ""
    if state.last_bigsur_note:
        bigsur_note = (
            f"\n\n🛠 {state.last_bigsur_note}\n"
            f"BigSur is the repair agent of last resort and it has ALREADY acted. Do "
            f"NOT immediately give_up again with the same reason — that just re-invokes "
            f"BigSur on work it already did (a spin loop). Try proving against the "
            f"corrected state FIRST. Only give_up if you hit a GENUINELY NEW blocker, "
            f"and if so state precisely what changed since BigSur's repair.")
        state.last_bigsur_note = ""
        # Fold into failure_context so the directed branch (task=None, which rebuilds
        # from ctx) carries it too — instead of REPLACING the directed context.
        ctx.failure_context = (ctx.failure_context + bigsur_note) if ctx.failure_context \
            else bigsur_note.lstrip()

    if ctx.current_task or ctx.failure_context:
        await agent._emit("message", f"[PO5] Guide: directed task for {entry.name}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd, task=None)
    else:
        ledger_summary = _build_ledger_summary(ledger, entry)
        await agent._emit("message", f"[PO5] Guide: initial strategy for {entry.name}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"CONTEXT:\n{ledger_summary}\n\n"
                f"We are proving '{entry.name}' in {stub_rel}.\n"
                f"Read {_read_hint(state)}, then advise on the best approach.\n"
                f"Also specify TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> for how many turns "
                f"the writer should get for the first attempt."
            ))

    # ── Step 2: Main loop ──
    total_turns = 0
    prev_sorry_count = None
    chunks_this_call = 0
    loop_start = _time.time()
    # Extract initial turns from guide's advice
    turns_match = re.search(r'TURNS:\s*(\d+)', advice)
    chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1)))) if turns_match else CHUNK_TURNS

    while True:
        ledger.increment_attempts(entry.id)
        chunks_this_call += 1
        # NO automatic backstops (no idle-minutes timer, no chunk cap, no time
        # extensions). A lemma is stopped only by a NATURAL give_up (guide → BigSur)
        # or BigSur's global cap — those blunt timeouts killed slow-but-progressing
        # proofs and forced churn.
        #
        # The ONE exception is the USER's explicit run-level ceiling: if the user
        # launched with --max-run-minutes, honor it. This is a user choice, not
        # magic — when the whole run exceeds it we stop and propagate.
        elapsed = _time.time() - getattr(agent, '_po4_start_time', _time.time())
        if state.max_run_minutes is not None and (elapsed / 60.0) > state.max_run_minutes:
            reason = (f"user run-level timeout: {elapsed/60:.0f}min ≥ "
                      f"max_run_minutes={state.max_run_minutes:.0f} (set via "
                      f"--max-run-minutes); stopping on '{entry.name}'")
            await agent._emit("message", f"[PO5] ⛔ {reason}")
            ctx.failure_context = f"User timeout: {reason}"
            ledger.mark_failed(entry.id, f"User timeout: {reason}")
            _record_give_up(state, entry, f"User timeout: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd,
                                               f"Child '{entry.name}' hit user run cap: {reason}")
            return "failed"
        writer_pct = await writer.get_context_percentage()
        # _get_guide handles rotation internally if >= 75%
        guide = await _get_guide(agent, entry, state, ledger)
        # Keep the guide live and reactive for the WHOLE lemma via a persistent
        # listen task (idempotent; re-ensured each iteration in case the guide
        # rotated to a fresh instance). While the writer proves this chunk the guide
        # is not being driven by run_ai, so its listener answers the writer in real
        # time; when the orchestrator later calls run_ai on the guide for its
        # review/decision, run_ai owns the session and the listener parks.
        _ensure_listening(agent, guide)
        # Open the live writer↔guide channel for THIS chunk. Re-established every
        # iteration because either instance may have rotated (new name). Both
        # instances now listen persistently, so a writer→guide message lands in
        # real time and the guide can reply on the same channel.
        guide_name = _link_writer_guide(agent, writer, guide)
        guide_pct = await guide.get_context_percentage()
        await agent._emit("message",
            f"[PO5] Chunk {entry.attempts} ({chunk_budget}t, total={total_turns}) "
            f"[{elapsed/60:.1f}min] | writer: {writer_pct or 0:.0f}% | guide: {guide_pct or 0:.0f}%")

        # Writer works. The guide is already live in its own persistent listen task
        # (_ensure_listening above), so it answers the writer's mid-chunk messages
        # in real time — no per-chunk gather/cancel dance, and the guide is NOT torn
        # down at the chunk boundary. The writer's run_ai holds _driving_lock for
        # the whole chunk; if it messages the guide and waits, the reply is injected
        # at the writer's next turn boundary (run_ai's own between-turn mailbox pull).
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                f"You have {chunk} turns. EDIT FORWARD — transient `error:` states while "
                f"building are fine; do NOT revert to the last green version on every error. "
                f"The file must be error-free (sorry warnings OK) by the END of your turns; "
                f"if you edit into a mess you can't untangle, read_snapshot to restore your "
                f"last banked good state rather than hand-reverting.{scope_note}\n\n"
                f"Your proof guide '{guide_name}' is live RIGHT NOW while you work and "
                f"answers in real time. Keep proving — do NOT block waiting on it. If you "
                f"hit something strategic — the goal looks false or mis-stated, the "
                f"signature seems unprovable as written, a lemma you need is missing, or "
                f"you're stuck in a way tactics alone won't fix — report it with "
                f"send_message(to=\"{guide_name}\", message=\"...\") and KEEP WORKING; its "
                f"reply reaches you at your next turn. Only if you genuinely cannot proceed "
                f"without the answer, follow up with wait_for_reply(sender=\"{guide_name}\", "
                f"timeout=<seconds you expect it to take>) — pick a short timeout for a quick "
                f"check, a longer one for a deep architectural call. Do NOT message for "
                f"routine compile errors — fix those yourself."
            ),
            verify=verify_fn, max_rounds=2, max_turns=chunk, use_run_ai=True,
        )

        total_turns += chunk
        await agent._emit("message", f"[PO5] Writer finished chunk {entry.attempts} ({total_turns} total turns)")

        # CHECKPOINT after every chunk. The PROVE phase runs this whole chunk loop
        # as ONE handler() call, so the main loop's phase-boundary save (which only
        # fires when a lemma finishes) does NOT protect mid-lemma progress. If the
        # TM watchdog restarts a wedged prover mid-lemma, without this the fresh
        # prover would resume from the phase entry and REDO the lemma from scratch.
        # Persisting the ledger + state here means a restart resumes from the last
        # completed chunk against the proved work already on disk. Cheap (a small
        # JSON write) and it's the "resume from checkpoint, don't redo" guarantee.
        #
        # PERIODIC FULL CHECKPOINT: on a long grind with no proved lemma, also take a
        # full swarm checkpoint (session ids + workspace snapshot) once an hour, so a
        # dashboard crash mid-lemma still has a recent full checkpoint. Gated by the
        # swarm's own clock (any full checkpoint resets it), so it's the safety net,
        # not an extra per-chunk cost.
        if _periodic_checkpoint_due(agent):
            await _checkpoint(agent, ledger, cwd, state, reason="periodic")
        else:
            ledger.save()
            _save_state(cwd, state)

        # Build the AUTHORITATIVE dependency+sorry overview ONCE. This single
        # source of truth drives (a) the proved/contingent gate, (b) the guide's
        # progress metric, and (c) the guide-facing overview. It joins in-file
        # dependency edges (comment-stripped, word-boundary, transitively closed)
        # + the module-SAFE `#print axioms` verdict (build + non-module scratch;
        # never run in-place inside a `module`) + sorry positions. The guide no
        # longer reasons from stale memory or snapshot line numbers.
        tsm = tools.transitive_sorry_map(stub_rel, sorted(protected_names))
        cr = tools.check_compiles(stub_rel)

        # Check: proved? (TARGET-SCOPED — a shared file may hold sibling theorems
        # whose sorry is not ours to close, so we gate on the protected targets.)
        if cr.success and tsm.build_ok and protected_names and all(
                tsm.targets[n].done for n in protected_names if n in tsm.targets):
            ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
            await agent._emit("message", f"[PO5] ✓ Proved '{entry.name}'.")
            # Checkpoint happens in _phase_prove on the "proved" result (the single
            # funnel every prove path returns through).
            return "proved"

        # Not (yet) proved. Compute the writer's REMAINING EDITABLE work FIRST, so the
        # contingent gate below can tell "waiting on someone else" from "still my job".
        local_sorry = tools.get_sorries_by_theorem(stub_rel)
        protected_local_sorry = sum(len(local_sorry.get(n, [])) for n in protected_names)

        # Reachable in-file helpers the TARGET depends on that still carry a
        # LITERAL sorry, excluding the protected targets themselves and genuine
        # siblings. These are the writer's real pending obligations even when its
        # own block reads clean (it factored the goal into inline `sorry` helpers).
        # Filter on has_local_sorry (a literal token), NOT the axioms verdict's
        # open_deps: when the build is RED the verdict marks EVERY reachable decl
        # has_transitive_sorry=True, which in the endgame (0 sorries, still fixing
        # compile errors) would falsely flag clean helpers and contradict the
        # positive endgame framing.
        open_deps_all: set[str] = set()
        for t in protected_names:
            if t in tsm.targets:
                open_deps_all |= set(tsm.targets[t].open_deps)
        transitive_inline_sorry_info = {
            n: [tsm.decls[n].start] for n in sorted(open_deps_all)
            if n not in protected_names and n not in siblings and n in tsm.decls
            and tsm.decls[n].has_local_sorry
        }

        # CONTINGENT gate. The target's OWN block is locally sorry-free but it is
        # transitively unproven. Whose job is the residual sorry?
        #   - If there is EDITABLE in-file work (an inline `sorry` helper the writer
        #     factored out and can still prove), it is OURS → fall through and keep
        #     proving. Parking contingent here would freeze a lemma the writer could
        #     finish this very chunk.
        #   - Otherwise the residual lives in something we CANNOT edit from this file
        #     — a sibling obligation proved separately, a registered child, or an
        #     IMPORTED cross-branch dependency. That is a DAG handoff, NOT a writer
        #     stall → park CONTINGENT so _propagate_proved promotes us once the
        #     dependency clears. This stops the callElim_sim_canfail loop (20 give-ups
        #     escalated to BigSur while the real blocker, callElim_call_block_exec,
        #     sat unproven in an imported sibling file). WHICH lemma to drive next is
        #     the guide's job in _phase_select — the blocker is its own registered
        #     pending/proving node, so no manual nomination is needed here.
        if cr.success and tsm.build_ok and protected_local_sorry == 0 \
                and not transitive_inline_sorry_info:
            ledger.mark_contingent(entry.id)
            return "contingent"

        # Progress metric: the number of literal `sorry` TOKENS in OUR obligations
        # (protected targets + the inline helpers they depend on), excluding
        # siblings whose sorries other branches own. This is the LEAF-sorry count —
        # deliberately NOT tsm.open_sorry_count(), which counts distinct reachable
        # decls via the axioms verdict. That decl-count had two failure modes on the
        # critical path, both of which this replaces:
        #   * BUILD RED → the axioms oracle can't confirm anything, so every
        #     reachable decl reads has_transitive_sorry=True and the count freezes
        #     at the reachable-decl total. A proof with 0 real sorries but compile
        #     errors then looked identical to a genuine stall (idle clock never
        #     reset, backstop could kill a nearly-done proof).
        #   * 1:1 FACTORING → moving a sorry from the target into a fresh inline
        #     helper spawns a new reachable decl, so the decl-count SPIKED upward
        #     (4→5) on healthy decomposition — the very signal feeding decompose /
        #     give-up. Leaf-count stays flat when a sorry just moves.
        # For display: literal-sorry positions, partitioned protected vs sibling.
        sorry_info = local_sorry
        protected_sorry_info = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}
        sibling_sorry_info = {n: v for n, v in sorry_info.items()
                              if n not in protected_names and v}
        # Our leaf-sorries = every literal sorry position EXCEPT those in sibling
        # obligations. Covers protected targets + writer-created inline helpers.
        sorry_count = sum(len(v) for n, v in sorry_info.items() if n not in siblings)
        file_compiles_now = cr.success
        # ENDGAME: 0 leaf-sorries but the file does not compile yet. The writer has
        # replaced the last sorry with a real proof and is closing compile errors on
        # the full statement — the single most forward state there is. Treated as
        # progress below (resets the idle clock) and framed positively to the guide,
        # so a proof one tactic from done is never scored as a stall.
        finishing_compile = (sorry_count == 0 and not file_compiles_now)
        progress = _format_progress(prev_sorry_count, sorry_count, compiles=file_compiles_now)
        prior_sorry_count = prev_sorry_count  # snapshot BEFORE overwrite (stuck check)
        prev_sorry_count = sorry_count
        writer_pct = await writer.get_context_percentage()

        # Guide reviews → next advice
        compile_note = ""
        if not outcome.success and outcome.last_error:
            compile_note = f"\n⚠️ COMPILATION FAILED after {outcome.rounds} fix rounds: {outcome.last_error}\n"
        sibling_note = (
            f"\nNOT YOUR TASK — sibling sorries owned by other branches (ignore): {sibling_sorry_info}\n"
            if sibling_sorry_info else "")
        # The writer factored the target into inline `sorry` helpers, so its own
        # protected block reads clean while the target is still TRANSITIVELY
        # unproven. Make this explicit — otherwise the guide sees an empty sorry
        # set, believes the branch is done, and loops `continue` forever. These
        # inline helpers are YOURS: either close them inline or `decompose` to
        # extract them into their own files.
        transitive_note = (
            f"\n⚠️ TARGET NOT DONE — your block has NO literal sorry, but it is "
            f"TRANSITIVELY UNPROVEN: the writer left `sorry` in inline helpers it "
            f"created, which your goal depends on. These ARE your obligation — "
            f"close them inline or `decompose` to extract them: "
            f"{transitive_inline_sorry_info}\n"
            if transitive_inline_sorry_info else "")
        from .._snapshot_mcp import snapshot_summary
        snap_summary = snapshot_summary(cwd, entry.workspace)
        snap_note = f"\n{snap_summary}\n" if snap_summary else ""
        sorry_map = _format_sorry_map(tsm, set(protected_names), siblings)
        # In the endgame (0 sorries, not yet compiling) `progress` already frames the
        # non-compile positively; only tack on the alarming "(NOT COMPILING)" when
        # there is still open work, so a near-done proof doesn't read as a stall.
        _compile_suffix = ' (NOT COMPILING)' if (compile_note and not finishing_compile) else ''
        await agent._emit("message", f"[PO5] Guide reviews: {progress}{_compile_suffix}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk {entry.attempts} ({total_turns} total turns).\n"
                f"{_runway_note(writer_pct)}\n"
                f"{progress}\nFile: {stub_rel}\n"
                f"{sorry_map}"
                f"{transitive_note}"
                f"{sibling_note}"
                f"{snap_note}"
                f"{compile_note}"
                f"Focus on STRATEGY and overall progress. Compilation errors (if any) are "
                f"the writer's to fix — only flag them if you believe the writer cannot fix "
                f"them or they signal a wrong direction. Watch the snapshot trajectory for "
                f"regression. Diagnose and advise what to try next."
            ))

        # Guide decides. We also let the guide independently call for a snapshot
        # of the CURRENT state (a strategic cross-check on the writer's own
        # judgment) — but only when the file compiles, since a snapshot of a
        # non-compiling file would be rejected anyway.
        file_compiles = tools.check_compiles(stub_rel).success

        def _parse_turns(raw: str) -> dict:
            out = {}
            m = re.search(r'TURNS:\s*(\d+)', raw)
            if m:
                out["turns"] = int(m.group(1))
            sm = re.search(r'SNAPSHOT:\s*(yes|no)', raw, re.IGNORECASE)
            if sm and sm.group(1).lower() == "yes":
                out["snapshot"] = True
                tm = re.search(r'SNAPSHOT_TAG:\s*(.+)', raw)
                out["snapshot_tag"] = tm.group(1).strip() if tm else "guide-checkpoint"
            return out

        # Track consecutive no-reduction chunks. Progress = the leaf-sorry count
        # STRICTLY decreased this chunk. A chunk that closes an inline helper counts
        # as progress; a chunk that merely MOVES a sorry into a fresh helper does not
        # inflate the count (leaf-count is flat under 1:1 factoring), so it is
        # neither scored as progress nor as a stall. Compare against the value
        # captured BEFORE we overwrote prev_sorry_count above.
        if not hasattr(entry, '_stuck_count'):
            entry._stuck_count = 0
        made_progress = (
            prior_sorry_count is not None and sorry_count < prior_sorry_count)
        # `finishing_compile` (computed above): 0 leaf-sorries but not yet compiling.
        # It must NOT be scored as a stall — the axioms-verdict count used to read
        # this as "still N open, NOT COMPILING" and let the idle clock run toward a
        # backstop that could kill a proof one tactic from done.
        still_open = sorry_count > 0
        if still_open and not made_progress:
            entry._stuck_count = getattr(entry, '_stuck_count', 0) + 1
        else:
            entry._stuck_count = 0
        # Track endgame chunks (0 sorries but not yet compiling) only to drive the
        # guide-facing stuck_hint below — no longer feeds any idle backstop.
        if finishing_compile:
            entry._endgame_count = getattr(entry, '_endgame_count', 0) + 1
        else:
            entry._endgame_count = 0

        stuck_hint = ""
        if finishing_compile and entry._endgame_count > ENDGAME_GRACE_CHUNKS:
            # 0 sorries but stuck on the SAME broken proof for several chunks — this
            # is NOT a decompose situation (there is nothing left to extract). Steer
            # the guide toward recovering a compiling snapshot or a fresh approach.
            stuck_hint = (
                f"\n⚠️ ENDGAME STALL: {entry._endgame_count} chunks with 0 sorries but the "
                f"proof still does NOT compile. The writer replaced the last sorry with a "
                f"proof it cannot make compile. Do NOT decompose (nothing to extract). "
                f"Consider read_snapshot(<best compiling tag>) to recover the last green "
                f"state, or fresh_start for a different closing tactic.\n"
            )
        elif entry._stuck_count >= 3:
            stuck_hint = (
                f"\n⚠️ STUCK: {entry._stuck_count} consecutive chunks with no sorry reduction. "
                f"Consider decompose even if the writer still has runway — after this many "
                f"idle chunks the writer may simply be unable to close these obligations in "
                f"the current file.\n"
            )
        if transitive_inline_sorry_info:
            stuck_hint += (
                f"\n⚠️ Your block is locally sorry-free but TRANSITIVELY UNPROVEN via inline "
                f"helpers ({sorted(transitive_inline_sorry_info)}). `continue` only helps if the "
                f"writer will close them inline; otherwise choose `decompose` to extract them.\n"
            )
        # Surface an already-authored research report + its verdict so the guide does
        # not re-diagnose from scratch and re-give-up with a stale reason (the callElim
        # loop: the report said GIVE_UP early, but the guide kept citing the fixed
        # @[expose] build gate for 9 give-ups before acting on it).
        stuck_hint += _report_hint(entry, cwd)

        # No idle/extend backstop anymore — the guide decides when to stop (give_up)
        # and BigSur is the only cap. The `stuck_hint` above still nudges strategy.
        extend_prompt = ""

        snapshot_prompt = ""
        if file_compiles:
            snapshot_prompt = (
                "\nSNAPSHOT: <yes|no> (does the CURRENT compiling state deserve to be "
                "banked as a safety net — real progress worth preserving? Judge this "
                "independently of the writer.)\n"
                "SNAPSHOT_TAG: <short label> (only if SNAPSHOT: yes)"
            )

        decision, reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "decompose", "research", "fresh_start", "give_up"],
            task=(
                f"{_runway_note(writer_pct)}\n"
                f"(Runway is a USAGE figure: a LOW % means the writer has LOTS of room "
                f"left — NOT that it is exhausted. Do NOT decompose while runway is HEALTHY.)\n"
                f"- continue: Keep trying in this file (the default while runway is HEALTHY).\n"
                f"- decompose: Split into helper files — ONLY when the writer is genuinely "
                f"stuck AND runway is GETTING FULL/FULL. Never split a mutually-recursive "
                f"goal into separate files (keep it in one `mutual` block).\n"
                f"- research: Spawn a deep ProofResearcher that reads the WHOLE codebase for "
                f"the primitives / proof patterns / counterexamples this lemma needs and writes "
                f"a findings report you and the writer then read. Use CAUTIOUSLY — only when the "
                f"writer is genuinely STUCK on HOW to prove a hard goal (missing the right lemma "
                f"or induction shape), not for routine progress. It costs a research pass, so "
                f"don't spend it on a lemma that's merely slow.\n"
                f"- fresh_start: Current approach exhausted, start over.\n"
                f"- give_up: The goal cannot be closed HERE by the writer. THREE cases, all "
                f"→ give_up (which routes to the BigSur repair agent — the ONLY actor that "
                f"can change contracts OR run a build):\n"
                f"    (a) it is false / unreachable from available context;\n"
                f"    (b) it needs a SIGNATURE CHANGE the writer may not make — a hypothesis "
                f"threaded from an ancestor, a strengthened contract. CHECK YOUR MAILBOX "
                f"(get_messages_by_sender / get_thread / list_recent_messages): if you and "
                f"the writer already AGREED the fix is added hypotheses / a strengthened "
                f"signature, that is NOT `continue`. Put the required signature change in REASON;\n"
                f"    (c) a BUILD / OLEAN-CACHE blocker you and the writer canNOT fix from "
                f"inside the file: e.g. 'imports are out of date / must be rebuilt', repeated "
                f"identical build failures (the 4294967294 / 'no such file' family), a "
                f"whole-subtree stale-olean gate, or an error that reproduces even on a "
                f"byte-clean file with only its one intended sorry. The writer has NO build "
                f"tool and CANNOT rebuild oleans — looping `continue` on this will NEVER "
                f"clear it. give_up and describe the exact build error + which module/subtree "
                f"needs rebuilding in REASON; BigSur has a real `lake build` tool and can "
                f"rebuild/repair the subtree. A byte-clean file that stalls for several "
                f"chunks with an unchanging BUILD error (not a proof error) is case (c) — "
                f"do NOT keep choosing `continue`.\n"
                f"{stuck_hint}"
            ),
            post_prompt=(
                f"TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> (how many turns for writer next, if continue)"
                f"{snapshot_prompt}"
                f"{extend_prompt}"
            ),
            post_prompt_parser=_parse_turns,
        )

        # Guide-driven snapshot: an independent strategic checkpoint, in addition
        # to any the writer took on its own. save_snapshot re-checks compilation
        # and dedups, so a redundant request is a harmless no-op.
        if extras.get("snapshot"):
            from .._snapshot_mcp import save_snapshot
            msg = save_snapshot(stub_rel, entry.workspace, cwd,
                                extras.get("snapshot_tag", "guide-checkpoint"),
                                note=f"guide checkpoint after chunk {entry.attempts}")
            await agent._emit("message", f"[PO5] Guide snapshot: {msg}")

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Guide gives up: {reason}")
            ctx.failure_context = f"Guide gave up: {reason}"
            ledger.mark_failed(entry.id, f"Guide gave up: {reason}")
            _record_give_up(state, entry, f"Guide gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Guide gave up: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd, f"Child '{entry.name}' gave up: {reason}")
            return "failed"
        elif decision == "fresh_start":
            await agent._emit("message", f"[PO5] Fresh start: {reason}")
            ctx.needs_fresh_guide = True
            ctx.needs_fresh_writer = True
            ctx.failure_context = f"Previous approach exhausted: {reason}"
            ctx.current_task = ""
            return "retry"
        elif decision == "decompose":
            await agent._emit("message", f"[PO5] Decompose: {reason}")
            # Pre-extraction validation: ask guide which helpers are actually extractable
            decompose_ok = await _validate_decompose(
                agent, state, ledger, entry, cwd, tools, stub_rel, protected_names)
            if decompose_ok is True:
                break
            # Guide determined nothing is extractable — get revised strategy and continue
            await agent._emit("message", f"[PO5] Decompose blocked — proving inline")
            advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
                task=(
                    f"Extraction was BLOCKED because some helpers recurse back into the parent.\n"
                    f"Details: {decompose_ok}\n\n"
                    f"Give the writer a concrete strategy to prove the recursive helpers INLINE\n"
                    f"(with termination_by / fuel-based induction). Once those are closed,\n"
                    f"any remaining standalone helpers can be extracted in a later pass.\n"
                    f"Specify TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}>."
                ))
            turns_match = re.search(r'TURNS:\s*(\d+)', advice)
            chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1)))) if turns_match else CHUNK_TURNS
            continue
        elif decision == "research":
            await agent._emit("message", f"[PO5] Research requested: {reason}")
            # Deep research pass: reads the whole codebase for primitives/patterns/
            # counterexamples and writes a report ending with a RECOMMENDATION.
            # Best-effort — a research failure must not sink the lemma.
            try:
                report_rel = await _run_researcher(
                    agent, state, ledger, entry, cwd, stub_rel, reason)
            except Exception as e:
                await agent._emit("message",
                    f"[PO5] Researcher failed ({type(e).__name__}: {e}); continuing without report.")
                report_rel = None
            if not report_rel:
                continue  # no report — just re-enter the loop
            # THE GUIDE READS THE REPORT AND DECIDES. The researcher only advises;
            # the guide owns the call. If the report shows the goal is
            # false/unprovable-as-stated or needs a signature change, the guide
            # gives up now (→ BigSur) instead of handing the writer a doomed task.
            r_decision, r_reason, _rx = await _consult_guide_decide(
                agent, state, ledger, entry, cwd,
                options=["proceed", "give_up", "research_more"],
                task=(
                    f"The ProofResearcher wrote its findings to {report_rel}. READ IT "
                    f"(Read {report_rel}) — note its RECOMMENDATION and Confidence — and decide:\n"
                    f"- proceed: the report is CONFIDENT the goal is provable and gives a "
                    f"viable shape / primitives — steer the writer to follow it (put the "
                    f"concrete shape + primitives + report path in REASON).\n"
                    f"- give_up: the report is CONFIDENT the goal is FALSE / unprovable AS "
                    f"STATED, needs a SIGNATURE CHANGE the writer cannot make, or the "
                    f"required substrate is beyond reach — route to BigSur. Put the report's "
                    f"finding (counterexample / missing hypothesis / substrate) in REASON.\n"
                    f"- research_more: the report is UNCERTAIN / low-confidence, or its "
                    f"feasibility verdict is not backed by the actual definitions. Do NOT "
                    f"give_up on an uncertain report (that may escalate a provable goal) and "
                    f"do NOT blindly proceed on a shaky one — send it back for another, "
                    f"deeper research pass. Put in REASON exactly what must be resolved.\n"
                    f"Base this on what the report ACTUALLY concluded AND how confident it "
                    f"is — never treat an UNCERTAIN report as a confident PROCEED or GIVE_UP."
                ))
            if r_decision == "research_more":
                await agent._emit("message",
                    f"[PO5] Guide: research inconclusive, requesting a deeper pass: {r_reason}")
                # Re-run the researcher with the guide's specific unresolved question.
                report_rel = await _run_researcher(
                    agent, state, ledger, entry, cwd, stub_rel,
                    reason=f"PRIOR REPORT WAS UNCERTAIN. Resolve specifically: {r_reason}") \
                    or report_rel
                continue
            if r_decision == "give_up":
                await agent._emit("message", f"[PO5] Guide gives up after research: {r_reason}")
                ctx.failure_context = f"Guide gave up (post-research): {r_reason}"
                ledger.mark_failed(entry.id, f"Guide gave up (post-research): {r_reason}")
                _record_give_up(state, entry, f"Post-research give-up: {r_reason}")
                await _ask_guide_user_fix(agent, state, ledger, entry, cwd,
                                          f"Post-research give-up: {r_reason}")
                await _propagate_failure_to_parent(agent, state, ledger, entry, cwd,
                                                   f"Child '{entry.name}' gave up after research: {r_reason}")
                return "failed"
            # proceed: fold the guide's report-informed steer into the writer's next task.
            ctx.failure_context = (
                (ctx.failure_context + "\n" if ctx.failure_context else "")
                + f"ProofResearcher report at {report_rel}. Guide's directive: {r_reason}\n"
                f"READ the report and follow its recommended proof shape / primitives.")
            continue
        else:
            if "turns" in extras:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, extras["turns"]))

    # ── Max depth: no extraction ──
    if entry.depth >= MAX_DEPTH:
        return await _prove_at_max_depth(agent, state, ledger, entry, cwd,
                                          tools, stub_rel)

    # ── Grace phase: factor sorry into external helpers ──
    return await _grace_phase(agent, state, ledger, entry, cwd,
                               writer, verify_fn, tools, stub_rel, protected_names)


async def _validate_decompose(agent, state, ledger, entry, cwd, tools, stub_rel, protected_names):
    """Ask guide to verify which sorry helpers are truly extractable before committing.

    Returns True if decomposition should proceed, or a string with revised
    instructions for the writer if nothing is extractable.
    """
    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return True  # can't analyze, let extraction try

    # Sibling obligations sharing this file are NOT extractable helpers.
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    sorry_helpers = [b for b in split.blocks
                     if b.has_sorry and b.name not in protected_names
                     and b.name not in siblings]
    if not sorry_helpers:
        return True  # nothing to check

    helper_list = "\n".join(
        f"  - {b.name} (lines {b.start}-{b.end})" for b in sorry_helpers)

    decision, reason, _extras = await _consult_guide_decide(
        agent, state, ledger, entry, cwd,
        options=["proceed_extract", "continue_inline"],
        task=(
            f"BEFORE EXTRACTING — verify each sorry helper is truly standalone.\n\n"
            f"Sorry helpers that would be extracted:\n{helper_list}\n\n"
            f"For EACH helper, answer: does its proof need to:\n"
            f"  - Recurse back into '{entry.name}' (tail re-entry on shorter trace)?\n"
            f"  - Use `ih` applied to the FULL statement (not just the body)?\n"
            f"  - Call any theorem in the same mutual block?\n\n"
            f"If YES for ANY helper → choose 'continue_inline' and explain what the\n"
            f"writer must prove inline (with termination_by) vs what can be extracted later.\n\n"
            f"If ALL helpers are genuinely standalone (no callbacks) → choose 'proceed_extract'."
        ))

    if decision == "proceed_extract":
        return True
    else:
        return (
            f"Guide reviewed helpers before extraction and determined they cannot be extracted:\n"
            f"{reason}\n"
            f"Prove the recursive/inline helpers first, then extract standalone ones."
        )



async def _prove_at_max_depth(agent, state, ledger, entry, cwd,
                               tools, stub_rel) -> str:
    """At max depth: fresh guide + proof_closer that know nothing about decomposition.
    Pure prove loop — guide advises, closer works, guide decides continue/give_up."""
    ctx = state.lemma_ctx[entry.id]
    await agent._emit("message", "[PO5] MAX DEPTH — spawning proof_closer (no decomposition).")

    # Kill existing guide+writer — they carry decomposition context we don't want
    await _cleanup_agents(agent, entry)

    # Spawn proof_closer (different agent spec — no sorry allowed)
    deep_writer = await _get_proof_closer(agent, entry, state, ledger)
    original_content = (cwd / stub_rel).read_text()
    verify_fn = _make_verifier(entry, stub_rel, original_content, ledger, cwd)

    # Fresh guide — initial task is pure "prove this, no decomposition exists"
    ledger_summary = _build_ledger_summary(ledger, entry)
    advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
        task=(
            f"You must prove '{entry.name}' in {stub_rel} with ZERO sorry.\n"
            f"There is NO decomposition available — everything must be proved in this one file.\n"
            f"You CAN create helper theorems within the same file.\n"
            f"Use mutual recursion, induction, structural recursion — any technique.\n\n"
            f"CONTEXT:\n{ledger_summary}\n\n"
            f"Read {_read_hint(state)}. Advise on the best approach."
        ))

    # Same loop pattern as _attempt_prove but only continue/fresh_start/give_up
    total_turns = 0
    prev_sorry_count = None
    chunk_budget = CHUNK_TURNS

    while True:
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        await agent._emit("message", f"[PO5] Deep chunk ({chunk}t, total={total_turns})")

        await verified_loop(
            agent_ctx=deep_writer,
            initial_input=(
                f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                f"You have {chunk} turns. Close ALL sorry. File MUST compile."
            ),
            verify=verify_fn, max_rounds=5, max_turns=chunk, use_run_ai=True,
        )
        total_turns += chunk

        # Check: proved? Uses the authoritative transitive oracle (#print axioms),
        # not the text/warning-based cr.has_sorry which misses sorry reached
        # through imported/assembled dependencies. _proved_or_contingent also
        # parks the entry as CONTINGENT when it is locally clean but still waiting
        # on an unproven SIBLING obligation (not just a child), matching the
        # per-target gate — otherwise a finished target gets needlessly re-driven.
        _compiles_now = tools.check_compiles(stub_rel).success
        if _compiles_now:
            verdict = _proved_or_contingent(tools, ledger, entry, cwd, stub_rel)
            if verdict is not None:
                return verdict
            # None: transitive sorry from untracked imports / fresh inline
            # helper — continue proving.

        # Gather state
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        progress = _format_progress(prev_sorry_count, sorry_count, compiles=_compiles_now)
        prev_sorry_count = sorry_count
        writer_pct = await deep_writer.get_context_percentage()

        # Guide reviews → next advice
        await agent._emit("message", f"[PO5] Deep guide reviews: {progress}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk ({total_turns} total turns).\n"
                f"{_runway_note(writer_pct)}\n"
                f"{progress}\nFile: {stub_rel}\nSorries: {sorry_info}\n"
                f"Remember: NO decomposition. Everything in one file.\n"
                f"Diagnose and advise what to try next."
            ))

        # Guide decides — only continue/fresh_start/give_up (NO decompose)
        def _parse_turns_deep(raw: str) -> dict:
            m = re.search(r'TURNS:\s*(\d+)', raw)
            return {"turns": int(m.group(1))} if m else {}

        decision, reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "fresh_start", "give_up"],
            task=(
                f"{_runway_note(writer_pct)}\n"
                f"(Runway is a USAGE figure: a LOW % means the writer has LOTS of room "
                f"left — NOT that it is exhausted. Prefer continue while runway is HEALTHY.)\n"
                f"- continue: Keep trying.\n"
                f"- fresh_start: Current approach exhausted, try new strategy.\n"
                f"- give_up: Cannot be closed HERE by the writer. You are at MAX DEPTH — "
                f"there is NO decompose escape, so anything the writer can't fix in-file "
                f"MUST be given up (it routes to BigSur, the only actor that can change "
                f"contracts or run a build). THREE cases: (a) false / unreachable; (b) needs "
                f"a SIGNATURE CHANGE the writer may not make (a hypothesis from an ancestor, "
                f"a strengthened contract) — CHECK YOUR MAILBOX (get_messages_by_sender / "
                f"get_thread): if you both agreed it needs added hypotheses / a strengthened "
                f"signature, give_up with the change in REASON; (c) a BUILD / OLEAN-CACHE "
                f"blocker the writer cannot fix — 'imports out of date / must be rebuilt', "
                f"repeated identical build failures (4294967294 / 'no such file' family), a "
                f"stale-subtree olean gate, or an error reproducing on a byte-clean file with "
                f"only its intended sorry. The writer has NO build tool; `continue` will "
                f"NEVER clear it. give_up and put the exact build error + the module/subtree "
                f"needing a rebuild in REASON — BigSur has a real `lake build` tool. Do NOT "
                f"loop `continue` on an unchanging BUILD error (as opposed to a proof error)."
            ),
            post_prompt=f"TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> (how many turns for writer next, if continue)",
            post_prompt_parser=_parse_turns_deep,
        )

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Deep guide gives up: {reason}")
            ctx.failure_context = f"Max depth, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Max depth, gave up: {reason}")
            _record_give_up(state, entry, f"Max depth, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Max depth, gave up: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd, f"Child '{entry.name}' failed at max depth: {reason}")
            return "failed"
        elif decision == "fresh_start":
            await agent._emit("message", f"[PO5] Deep fresh start: {reason}")
            ctx.needs_fresh_guide = True
            ctx.failure_context = f"Max depth, fresh start: {reason}"
            return "retry"
        else:
            if "turns" in extras:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, extras["turns"]))



async def _grace_phase(agent, state, ledger, entry, cwd,
                        writer, verify_fn, tools, stub_rel, protected_names) -> str:
    """Decompose-time wrap-up: factor the protected block's remaining sorry into
    NAMED helpers so the extraction pipeline can move them out.

    This is NOT a "close ALL sorry" grind — the writer is not asked to finish the
    hard sub-lemmas here, only to (a) prove what it easily can and (b) push each
    remaining hard goal into a named helper theorem declared above, closing the
    protected block with `exact helper ...`. The helpers keep their `sorry` and
    become child obligations after extraction. No writer↔guide back-and-forth.
    """
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    protected_sorry = sum(len(sorry_info.get(n, [])) for n in protected_names)

    if protected_sorry == 0:
        await agent._emit("message", "[PO5] Protected block sorry-free → extract")
        return "has_sorry"

    is_mutual = len(protected_names) > 1
    mutual_note = ""
    if is_mutual:
        mutual_note = (
            f"\nMUTUAL BLOCK RULE: {sorted(protected_names)} must ALL be sorry-free.\n"
            f"Helpers go OUTSIDE and ABOVE the mutual...end block.\n"
        )

    await agent._emit("message", f"[PO5] Grace (factor & wrap up): {protected_sorry} sorry in protected block")

    # Bounded — this is a wrap-up, not a solve. A couple of passes is enough to
    # lift the remaining goals into named helpers; if it stalls we stop and let
    # extraction take whatever is factored.
    prev_count = protected_sorry
    for grace in range(2):
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        positions = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}

        await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"WRAP UP for extraction — grace {grace+1}.\n"
                f"Sorry still in the protected block: {positions}\n\n"
                f"GOAL: make the protected block ({sorted(protected_names)}) sorry-free by "
                f"FACTORING, not by finishing every hard proof now. For each remaining sorry:\n"
                f"  1. If you can close it quickly, do so.\n"
                f"  2. Otherwise, declare a NEW named helper theorem ABOVE it (with its own "
                f"`sorry`) capturing exactly that obligation, and close the goal with "
                f"`exact helper ...` / `apply helper ...`.\n"
                f"The helpers keep their `sorry` — the extraction pipeline moves them into "
                f"their own files and they become separate obligations. You cannot create "
                f"files yourself; declare helpers IN THIS SAME FILE.\n"
                f"The protected block itself must end up sorry-free (all its sorry pushed "
                f"into named helpers)."
                f"{mutual_note}\nYou have {GRACE_TURNS} turns."
            ),
            verify=verify_fn, max_rounds=2, max_turns=GRACE_TURNS, use_run_ai=True,
        )

        if tools.check_compiles(stub_rel).success:
            # Same proved/contingent/fall-through decision as the per-target gate:
            # PROVED (transitively sorry-free), CONTINGENT (locally clean but
            # waiting on an unproven sibling/child), or None (fall through to keep
            # factoring out helpers in the grace phase).
            verdict = _proved_or_contingent(tools, ledger, entry, cwd, stub_rel)
            if verdict is not None:
                return verdict

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        cur = sum(len(sorry_info.get(n, [])) for n in protected_names)
        if cur == 0:
            await agent._emit("message", "[PO5] Protected block sorry-free → extract")
            return "has_sorry"
        if cur >= prev_count:
            break
        prev_count = cur

    if tools.check_compiles(stub_rel).success:
        split = tools.split_theorems(stub_rel)
        extractable = [b for b in split.blocks
                       if b.name not in protected_names and b.mutual_group is None]
        if extractable:
            return "has_sorry"

    ctx = state.lemma_ctx.get(entry.id, LemmaContext())
    ctx.failure_context = "Could not make the protected block sorry-free despite multiple attempts"
    ledger.mark_failed(entry.id, "Protected block still has sorry after grace phase")
    await _propagate_failure_to_parent(agent, state, ledger, entry, cwd,
        f"Child '{entry.name}' failed: could not eliminate sorry from the main proof body")
    return "failed"


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: EXTRACT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_extract(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Extract helpers into files. Guide reviews before committing."""
    entry = ledger.get(state.current_lemma_id)
    ctx = state.lemma_ctx.get(entry.id, LemmaContext())
    tools = get_lean_tools()
    stub_rel = _resolve_stub(entry, cwd, state)

    # Save predecomp snapshot
    shutil.copy2(cwd / stub_rel, cwd / entry.workspace / "Stub.predecomp.lean")

    # Worker: decl_extractor
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if new_decomp_dir.exists():
        shutil.rmtree(new_decomp_dir)

    split = tools.split_theorems(stub_rel)
    protected_names = _get_protected_names(tools, stub_rel, entry)
    # Sibling obligations sharing this file must not be extracted as helpers.
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    extractable = [b for b in split.blocks
                   if b.name not in protected_names and b.mutual_group is None
                   and b.name not in siblings]

    # Fix A: nothing to extract — every declaration is a protected/sibling
    # obligation. Spawning an extractor is pointless — it can only no-op or, worse,
    # move protected siblings (the IMO2026 corruption). Skip the extractor entirely
    # and let the guide decide (retry with a different tack, or give up) instead of
    # spinning.
    if not extractable:
        await agent._emit("message",
            f"[PO5] Nothing extractable from {stub_rel} "
            f"(all {len(split.blocks)} decls protected/sibling) — skipping extractor")
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["retry", "give_up"],
            task=(
                f"Cannot decompose: every declaration in {stub_rel} is a protected "
                f"target or sibling obligation ({sorted(protected_names | siblings)}), "
                f"so there is nothing to extract into a helper.\n"
                f"The remaining difficulty is in the protected block(s) themselves or "
                f"in already-extracted children.\n"
                f"Options: retry proving inline (different tactic/approach), or give up."
            ))
        if decision == "give_up":
            ctx.failure_context = f"Nothing extractable, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Nothing extractable, gave up: {reason}")
            _record_give_up(state, entry, f"Nothing extractable, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd,
                                      f"Nothing extractable, gave up: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd,
                                         f"Child '{entry.name}' cannot be decomposed: {reason}")
            return Trans.CONTRADICTORY
        ctx.failure_context = "Nothing extractable — must prove inline."
        ctx.current_task = (
            f"Decomposition is not possible (all declarations are protected/sibling "
            f"obligations). Guide decided: {reason}\n"
            f"Prove the remaining sorry inline.")
        return Trans.RETRY

    session = MoveSession(tools, stub_rel, entry.name, entry.workspace,
                          output_subdir="new_decomposition",
                          protected_names=(protected_names | siblings))
    # Proof-DAG ancestors (dotted workspace paths) so add_import_safely can refuse
    # cycle-forming imports — same source as the writer's import server.
    ancestor_modules = []
    for anc_id in ledger.get_ancestry(entry.id):
        anc = ledger.get(anc_id)
        if anc:
            ancestor_modules.append(anc.workspace.replace("/", "."))
    extractor_mcp = create_extractor_mcp_server(session, ancestor_modules=ancestor_modules)

    do_not_move_names = sorted(protected_names | siblings)
    do_not_move = ""
    if len(do_not_move_names) > 1:
        do_not_move = f"\nDo NOT move: {do_not_move_names} (protected/sibling obligations).\n"

    await agent._emit("message", f"[PO5] Extracting {len(extractable)} helpers from {stub_rel}")

    async with swarm_agent("decl_extractor", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=entry.workspace,
                           extra_mcp_servers={"extractor_tools": extractor_mcp}) as extractor:
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input=(
                f"Extract standalone helpers from {stub_rel} into separate files.\n"
                f"Main theorem: '{entry.name}' (do NOT move this).{do_not_move}\n"
                f"Call get_declarations, then move_decl for each, then commit."
            ),
            verify=lambda: _verify_extraction(tools, stub_rel, entry, new_decomp_dir),
            max_rounds=2, max_turns=50, use_run_ai=False,
        )

    if not outcome.success:
        extract_error = outcome.last_error or "unknown error"
        session.revert()
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["retry", "give_up"],
            task=(
                f"Extraction FAILED. The extractor could not produce compilable output.\n"
                f"Error: {extract_error}\n"
                f"The file has been reverted to pre-extraction state.\n"
                f"Options: retry proving (different factoring), or give up."
            ))
        if decision == "give_up":
            ctx.failure_context = f"Extraction failed ({extract_error}), gave up: {reason}"
            ledger.mark_failed(entry.id, f"Extraction failed, gave up: {reason}")
            _record_give_up(state, entry, f"Extraction failed ({extract_error}), gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd,
                                      f"Extraction failed ({extract_error}), gave up: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd, f"Child '{entry.name}' extraction failed: {reason}")
            return Trans.CONTRADICTORY
        ctx.failure_context = f"Extraction failed: {extract_error}"
        ctx.current_task = (
            f"Extraction failed: {extract_error}\n"
            f"Guide decided: {reason}\n"
            f"Restructure the file so helpers can be extracted, or prove inline."
        )
        return Trans.RETRY

    finalize_result = session.finalize()
    if finalize_result and "Error" in finalize_result:
        await agent._emit("message", f"[PO5] finalize warning: {finalize_result}")
    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean")) if new_decomp_dir.exists() else []
    await agent._emit("message", f"[PO5] Extraction done: {len(new_files)} files staged")

    # Post-extraction compilation check — catch any issues the extractor missed
    if new_files:
        import subprocess
        stub_module = stub_rel.replace("/", ".").removesuffix(".lean")
        build_result = subprocess.run(["lake", "build", stub_module],
                                       cwd=str(cwd), capture_output=True, text=True, timeout=300)
        build_errors = [l for l in (build_result.stdout + "\n" + build_result.stderr).splitlines()
                        if ": error:" in l]
        if build_errors:
            error_summary = "\n".join(build_errors[:5])
            session.revert()
            ctx.failure_context = f"Post-extraction build failed:\n{error_summary}"
            ctx.current_task = "Extraction produced files but they don't compile together. The guide should review the errors and advise the writer how to restructure."
            await agent._emit("message", f"[PO5] Post-extraction build FAILED — reverting")
            return Trans.RETRY

    if not new_files:
        # Extractor ran but produced nothing — diagnose why
        tools_check = get_lean_tools()
        split = tools_check.split_theorems(stub_rel)
        blocked_reasons = []
        if split and not split.error:
            for b in split.blocks:
                if b.name == entry.name:
                    continue
                if not b.has_sorry:
                    continue
                if b.mutual_group is not None:
                    group_names = split.mutual_groups.get(b.mutual_group, [])
                    if entry.name in group_names:
                        blocked_reasons.append(f"'{b.name}' — in mutual block with main theorem")
                    else:
                        blocked_reasons.append(f"'{b.name}' — in mutual group {group_names}")
                elif "private " in b.text[:50]:
                    blocked_reasons.append(f"'{b.name}' — private (cannot be imported)")

        # Include extractor's last output if available (may explain why commit failed)
        extractor_msg = ""
        if outcome and outcome.output:
            extractor_msg = f"\nExtractor reported: {str(outcome.output)[:300]}"

        blocked_str = "\n".join(f"  - {r}" for r in blocked_reasons) if blocked_reasons else f"no structural blockers detected{extractor_msg}"
        ctx.failure_context = (
            f"Extraction produced 0 files. Blocked helpers:\n{blocked_str}"
        )
        ctx.current_task = (
            f"Extraction produced 0 files despite the extractor reporting success.\n"
            f"Diagnosis: {blocked_str}\n"
            f"If helpers are in a mutual block with main, move them out as standalone theorems above.\n"
            f"If private, remove 'private'. Otherwise prove inline."
        )
        await agent._emit("message", f"[PO5] 0 files extracted — blocked: {blocked_str[:100]}")
        return Trans.RETRY

    # Guide reviews decomposition
    file_list = "\n".join(f"  - {f.stem}" for f in new_files)
    decision, reason, _extras = await _consult_guide_decide(
        agent, state, ledger, entry, cwd,
        options=["proceed", "revert"],
        task=(
            f"Extracted {len(new_files)} helpers:\n{file_list}\n\n"
            f"Review each helper: does its proof need to call a theorem defined in the\n"
            f"current mutual block (i.e., call back into the parent)? If yes → revert.\n\n"
            f"If reverting: explain WHICH helpers must stay in the mutual block, HOW the\n"
            f"proof writer should reorganize them (e.g., add them into the mutual...end with\n"
            f"shared termination_by), and what existing helpers should be altered or removed\n"
            f"to accommodate the change. Be specific — the writer will use your instructions."
        ))

    if decision == "revert":
        _revert_extraction(entry, cwd)
        ctx.current_task = f"Guide reverted extraction: {reason}. Prove inline."
        ctx.failure_context = f"Decomposition invalid: {reason}"
        await agent._emit("message", f"[PO5] Guide reverted: {reason}")
        return Trans.RETRY

    return Trans.EXTRACTED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: DETECT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_detect(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Cycle detection. Guide decides on issues."""
    entry = ledger.get(state.current_lemma_id)
    ctx = state.lemma_ctx.get(entry.id, LemmaContext())

    result, verdicts = await _run_detection(agent, state, ledger, entry, cwd)

    if result == "rejected":
        _revert_extraction(entry, cwd)
        ctx.failure_context = "Decomposition rejected: identical to previously failed attempt."
        ctx.current_task = "Try a completely different decomposition."
        await agent._emit("message", "[PO5] Rejected — guide will retry.")
        return Trans.RETRY

    if result == "cycle_found":
        cycle_info = [v for v in verdicts if v.match_type == "cycle"]
        cycle_desc = "\n".join(f"  - {v.name} needs {v.matched_name} (ancestor)" for v in cycle_info)

        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["expand_mutual", "different_decomposition", "fresh_start", "give_up"],
            task=(
                f"CYCLE DETECTED:\n{cycle_desc}\n\n"
                f"- expand_mutual: Add into mutual block with shared termination_by\n"
                f"- different_decomposition: Revert, try different factoring\n"
                f"- fresh_start: New guide from scratch\n"
                f"- give_up: Cannot be proved"
            ))

        _revert_extraction(entry, cwd)
        state.cycles_detected += 1

        if decision == "give_up":
            ctx.failure_context = f"Cycle, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Cycle, gave up: {reason}")
            _record_give_up(state, entry, f"Cycle, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Cycle, gave up: {reason}")
            await _propagate_failure_to_parent(agent, state, ledger, entry, cwd, f"Child '{entry.name}' has unresolvable cycle: {reason}")
            return Trans.CONTRADICTORY
        elif decision == "expand_mutual":
            ctx.current_task = (
                "The extracted helpers have mutual recursion with the parent block. "
                "Add them INTO the mutual...end with shared termination_by. "
                "Do NOT create external sorry stubs.")
            ctx.failure_context = f"CYCLE: {cycle_desc}"
            await agent._emit("message", f"[PO5] Expand mutual: {reason}")
            return Trans.RETRY
        elif decision == "fresh_start":
            ctx.needs_fresh_guide = True
            ctx.needs_fresh_writer = True
            ctx.failure_context = f"Cycle, fresh start: {cycle_desc}"
            return Trans.RETRY
        else:
            ctx.current_task = "Try completely different decomposition."
            ctx.failure_context = f"Cycle: {cycle_desc}"
            return Trans.RETRY

    # Check duplicates
    existing_names = {e.name for e in ledger.entries()}
    duplicates = [v for v in verdicts if v.name in existing_names]
    if duplicates:
        dup_names = [v.name for v in duplicates]
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["revert", "proceed"],
            task=f"Duplicate names: {dup_names}. Revert and import existing, or proceed?")
        if decision == "revert":
            _revert_extraction(entry, cwd)
            ctx.failure_context = f"Duplicates: {dup_names}. Use imports."
            return Trans.RETRY

    # All clean — register
    _register_all_helpers(state, ledger, entry, cwd)
    state._detect_verdicts = verdicts
    return Trans.NO_CYCLE


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: UPDATE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_update(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Apply verdicts to ledger. Mechanical — no guide needed."""
    entry = ledger.get(state.current_lemma_id)
    if entry is None:
        # The current lemma no longer exists — BigSur may have deleted/reshaped it
        # during a give-up repair (see _run_bigsur). There is nothing to apply
        # verdicts against; drop any stale verdicts and let CHECK → SELECT pick
        # fresh work from the corrected ledger.
        state._detect_verdicts = None
        _resolve_import_dependencies(ledger, cwd)
        _propagate_proved(ledger, cwd)
        return Trans.CHECKED
    _apply_verdicts(state, ledger, entry, cwd)
    _resolve_import_dependencies(ledger, cwd)

    from .cycle_detection import prune_siblings_of_dead
    prune_siblings_of_dead(ledger, cwd)
    _propagate_proved(ledger, cwd)

    return Trans.CHECKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: CHECK
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_check(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Status inspection. On stuck: consult root's guide."""
    root = ledger.get(state.root_id)
    if root and root.status == LemmaStatus.PROVED:
        return Trans.ALL_PROVED
    if root and root.status == LemmaStatus.FAILED:
        return Trans.BLOCKED
    if ledger.all_proved():
        return Trans.ALL_PROVED
    if ledger.has_pending():
        return Trans.HAS_PENDING

    # Stuck
    stuck = [e for e in ledger.entries()
             if e.status in (LemmaStatus.CONTINGENT, LemmaStatus.PROVING)]
    stuck_desc = "\n".join(f"  - {e.name} [{e.status}]" for e in stuck)

    root_entry = ledger.get(state.root_id)
    if root_entry:
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, root_entry, cwd,
            options=["unblock", "give_up"],
            task=f"STUCK: No pending work.\nStuck:\n{stuck_desc}\nCan we unblock or give up?")
        if decision == "unblock":
            for e in stuck:
                if e.status == LemmaStatus.CONTINGENT:
                    e.status = LemmaStatus.PENDING
                    ctx = state.lemma_ctx.get(e.id)
                    if ctx:
                        ctx.current_task = f"Re-attempting: {reason}"
                    ledger.save()
                    await agent._emit("message", f"[PO5] Unblocked: {e.name}")
                    break
            return Trans.HAS_PENDING
        else:
            ledger.mark_failed(state.root_id, f"Stuck, gave up: {reason}")
            _record_give_up(state, root_entry, f"Stuck, gave up: {reason}")
            # Root give-up: ask the guide whether the user must fix something.
            await _ask_guide_user_fix(agent, state, ledger, root_entry, cwd,
                                      f"Stuck, gave up: {reason}")

    return Trans.BLOCKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: ASSEMBLE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_assemble(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Assembly: copy proved files, build, guide + fixer on errors."""
    tools = get_lean_tools()
    root_entry = ledger.get(state.root_id)

    # Copy proved Stub.lean → .lean
    topo = _topo_sort(ledger)
    for eid in topo:
        e = ledger.get(eid)
        if not e or e.status != LemmaStatus.PROVED:
            continue
        stub = cwd / e.workspace / "Stub.lean"
        target = cwd / f"{e.workspace}.lean"
        if stub.exists() and target.exists():
            shutil.copy2(stub, target)

    # Build + fix loop (guide + fixer pairs). Uses the shared lake_build helper —
    # the SAME authoritative build path BigSur uses for its compile gate.
    root_module = f"{state.root_workspace}.Stub".replace("/", ".")
    for attempt in range(3):
        ok, errors = lake_build(root_module, cwd, timeout=180)
        if ok:
            break

        error_text = "\n".join(errors[:20])
        await agent._emit("message", f"[PO5] Build errors (attempt {attempt+1}/3)")

        # Guide reviews
        advice = await _consult_guide_raw(agent, state, ledger, root_entry, cwd,
            task=f"Assembly build failed:\n{error_text}\nDiagnose and advise the fixer.")

        # Fixer works
        fixed = await _run_fixer(agent, state, cwd, error_text, advice)
        if not fixed:
            decision, reason, _extras = await _consult_guide_decide(
                agent, state, ledger, root_entry, cwd,
                options=["retry", "give_up"],
                task=f"Fixer failed (attempt {attempt+1}/3). Retry or give up?")
            if decision == "give_up":
                _record_give_up(state, root_entry, f"Assembly build failed, gave up: {reason}")
                await _ask_guide_user_fix(agent, state, ledger, root_entry, cwd,
                                          f"Assembly build failed, gave up: {reason}")
                return Trans.ASSEMBLY_FAILED
    else:
        return Trans.ASSEMBLY_FAILED

    # Verify the requested proof obligations are sorry-free. This must use the
    # SAME authoritative transitive oracle as the per-target gate
    # (`axioms_by_theorem` / `#print axioms`), not just the text/warning-based
    # `cr.has_sorry`: a theorem can be textually clean yet still bottom out in a
    # `sorryAx` through an assembled dependency.
    #
    # SCOPE: only the obligations the TM asked us to prove — i.e. the ones
    # registered in the ledger (INIT narrows these to the requested subset via
    # `_filter_requested_targets`). Un-requested sibling theorems in the same
    # file may legitimately still carry `sorry`; they are NOT our task, so we
    # must not gate assembly on them (neither the whole-file `has_sorry` nor the
    # transitive check).
    root_stub = f"{state.root_workspace}/Stub.lean"
    cr = tools.check_compiles(root_stub)
    if not cr.success:
        await agent._emit("message", "[PO5] Assembly: root does not compile")
        return Trans.ASSEMBLY_FAILED

    obligation_names = _requested_obligation_names(ledger, state, root_stub)

    if obligation_names:
        # Literal-sorry check scoped to our obligations (not the whole file).
        local_sorry = tools.get_sorries_by_theorem(root_stub)
        with_sorry = [n for n in obligation_names if local_sorry.get(n)]
        if with_sorry:
            await agent._emit("message",
                f"[PO5] Assembly: requested obligations still have literal sorry: {with_sorry}")
            return Trans.ASSEMBLY_FAILED
        # Transitive check: none of our obligations may depend on sorryAx.
        ax = tools.axioms_by_theorem(root_stub, obligation_names)
        unproven = [n for n in obligation_names if not ax.is_proven(n)]
        if unproven:
            await agent._emit("message",
                f"[PO5] Assembly: requested obligations transitively depend on sorry: {unproven}")
            return Trans.ASSEMBLY_FAILED
    elif cr.has_sorry:
        # No registered obligation names to scope to (single-root fallback):
        # keep the whole-file guard.
        await agent._emit("message", "[PO5] Assembly: root still has sorry")
        return Trans.ASSEMBLY_FAILED

    ledger.mark_proved(state.root_id, root_stub.replace("/", ".").removesuffix(".lean"))
    await agent._emit("message", "[PO5] Assembly complete: requested obligations sorry-free (transitively verified) ✅")

    return Trans.ASSEMBLED


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — agent management
# ═══════════════════════════════════════════════════════════════════════════════

async def _get_guide(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger) -> SwarmAgent:
    """Get or create persistent guide. Rotates automatically at 75% context or when needs_fresh_guide is set."""
    from .._ledger_mcp import create_ledger_mcp_server
    attr = f"_guide_{entry.id}"
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    ctx = state.lemma_ctx.get(entry.id)

    # Check if existing guide needs rotation (context exhausted or fresh_start requested)
    existing = getattr(agent, attr, None)
    if existing is not None:
        force_rotate = ctx and ctx.needs_fresh_guide
        try:
            pct = await existing.get_context_percentage()
        except Exception:
            pct = None
        # Rotate if: fresh_start requested, context exhausted, or process died
        if force_rotate or pct is None or pct >= CONTEXT_ROTATION_THRESHOLD:
            await _rotate_agent(agent, entry, cwd, role="guide", instance=existing)
            if ctx:
                ctx.needs_fresh_guide = False
            # Fall through to create fresh

    if getattr(agent, attr, None) is None:
        cheat_file = cheat_sheet_name(state.use_cheat_sheet, state.cheat_sheet_path)
        cheat_rel = f"{entry.workspace}/{cheat_file}" if cheat_file else ""
        ledger_mcp = create_ledger_mcp_server(ledger)
        from .._snapshot_mcp import create_snapshot_server
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        snapshot_mcp = create_snapshot_server(stub_rel, entry.workspace, cwd, can_write=False)
        ctx = swarm_agent(
            "proof_guide", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            template_vars={"cheat_sheet_path": cheat_rel},
            can_see=["SearchAgent"],
            extra_mcp_servers={"ledger": ledger_mcp, "snapshots": snapshot_mcp},
            disable_compaction=True,
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["guide"] = internal.spec.name

        # Inject prior state if exists — enough turns to read cheat sheet + file
        state_path = cwd / entry.workspace / "guide_state" / f"{entry.name}.md"
        _read_cheat = (f"1. Read the cheat sheet ({cheat_file} in your workspace)\n"
                       if cheat_file else "")
        init_prompt = (
            "You are starting a new session. Before receiving any task:\n"
            f"{_read_cheat}"
            "2. Read the current Stub.lean to see the proof state\n"
            "3. Use any tools you need to understand the current situation\n"
        )
        if state_path.exists():
            prior = state_path.read_text()
            init_prompt += f"\nPRIOR SESSION STATE:\n\n{prior}\n"
        init_prompt += "\nOnce you have full context, acknowledge. Do NOT start proving yet."
        await internal.run_ai(inp=init_prompt, max_turns=15)

    return getattr(agent, attr)


async def _get_writer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create persistent writer. Rotates automatically at 75% context
    or when needs_fresh_writer is set (e.g. after a fresh_start)."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_writer_{entry.id}"
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    ctx = state.lemma_ctx.get(entry.id)

    # Check if existing writer needs rotation
    existing = getattr(agent, attr, None)
    if existing is not None:
        force_rotate = ctx and ctx.needs_fresh_writer
        try:
            pct = await existing.get_context_percentage()
        except Exception:
            pct = None
        # Rotate if: fresh_start requested, context exhausted, or process died
        if force_rotate or pct is None or pct >= CONTEXT_ROTATION_THRESHOLD:
            await _rotate_agent(agent, entry, cwd, role="writer", instance=existing)
            if ctx:
                ctx.needs_fresh_writer = False
            # Fall through to create fresh

    if getattr(agent, attr, None) is None:
        ancestor_modules = []
        for anc_id in ledger.get_ancestry(entry.id):
            anc = ledger.get(anc_id)
            if anc:
                ancestor_modules.append(anc.workspace.replace("/", "."))
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        import_mcp = create_writer_import_server(stub_rel, ancestor_modules, ledger, current_entry_id=entry.id)
        from .._snapshot_mcp import create_snapshot_server
        from .hooks import writer_nudge_hooks
        snapshot_mcp = create_snapshot_server(stub_rel, entry.workspace, cwd, can_write=True)
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            can_see=["SearchAgent"],
            extra_mcp_servers={"writer_imports": import_mcp, "snapshots": snapshot_mcp},
            # Snapshot tip + run_code-without-edit nudge (keeps the writer editing
            # the FILE instead of iterating in scratch run_code, the main cost sink).
            extra_hooks=writer_nudge_hooks(agent_ref=agent),
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["writer"] = internal.spec.name
        _remove_guide_from_visibility(agent, entry, internal)

        # Inject prior state if exists — enough turns to read file + orient
        state_path = cwd / entry.workspace / "guide_state" / f"writer_{entry.name}.md"
        init_prompt = (
            "You are starting a new session. Before receiving any task:\n"
            "1. Read your assigned Stub.lean file to see the current proof state\n"
            "2. Check sorry positions and goal state at those positions\n"
            "3. Use any tools you need to understand the context\n"
        )
        if state_path.exists():
            prior = state_path.read_text()
            init_prompt += f"\nPRIOR SESSION STATE:\n\n{prior}\n"
        init_prompt += "\nOnce oriented, acknowledge. Then wait for strategy advice."
        await internal.run_ai(inp=init_prompt, max_turns=15)

    return getattr(agent, attr)


async def _get_proof_closer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create proof_closer for this lemma. Used at max depth — no sorry allowed."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_closer_{entry.id}"
    if getattr(agent, attr, None) is None:
        ancestor_modules = []
        for anc_id in ledger.get_ancestry(entry.id):
            anc = ledger.get(anc_id)
            if anc:
                ancestor_modules.append(anc.workspace.replace("/", "."))
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        import_mcp = create_writer_import_server(stub_rel, ancestor_modules, ledger, current_entry_id=entry.id)
        ctx = swarm_agent(
            "proof_closer", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            can_see=["SearchAgent"],
            extra_mcp_servers={"writer_imports": import_mcp},
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["closer"] = internal.spec.name
        _remove_guide_from_visibility(agent, entry, internal)
    return getattr(agent, attr)


def _remove_guide_from_visibility(agent, entry: LemmaEntry, writer_agent):
    """Remove any guide agent from the writer's visibility set."""
    writer_name = writer_agent.spec.name
    registry = agent.swarm._registry
    visible = registry.visibility_graph.get(writer_name)
    if visible is None:
        return
    guide_names = [n for n in visible if "guide" in n]
    for g in guide_names:
        visible.discard(g)


def _ensure_listening(agent, instance) -> None:
    """Attach a persistent background _listen_messages task to a writer/guide
    instance, so it stays live and reactive for the WHOLE lemma — not just during
    one chunk's gather.

    The task parks on the instance's message channel and, when a message arrives,
    injects it into that instance's backend session. It coordinates with any
    orchestrator-driven run_ai() on the SAME instance via _driving_lock (held by
    run_ai for its whole run; only try-acquired by the listener) — so the listener
    yields the session whenever run_ai is driving and resumes when it finishes.
    That is what lets the guide answer the writer mid-chunk while the writer proves,
    and lets the writer answer the guide during the decision phase, with no torn
    turns and no split results.

    Idempotent: a no-op if the instance already has a live listen task. The task's
    lifetime is bound to the instance — _stop_listening is called wherever the
    instance is destroyed (_rotate_agent, _cleanup_agents).
    """
    if instance is None:
        return
    existing = getattr(instance, "_po5_listen_task", None)
    if existing is not None and not existing.done():
        return
    token = CancellationToken()
    task = asyncio.ensure_future(instance._listen_messages(token))
    instance._po5_listen_token = token
    instance._po5_listen_task = task


async def _stop_listening(instance) -> None:
    """Cancel and await the instance's persistent listen task (see _ensure_listening).

    Graceful first: signal the CancellationToken so the loop stops at its next
    boundary (never truncating an in-flight reply). Then hard-cancel the task as a
    backstop and await it so the coroutine is fully torn down before the instance's
    backend is disconnected.
    """
    if instance is None:
        return
    token = getattr(instance, "_po5_listen_token", None)
    task = getattr(instance, "_po5_listen_task", None)
    if token is not None:
        token.cancel()
    if task is not None and not task.done():
        task.cancel()
        try:
            await task
        except (asyncio.CancelledError, Exception):
            pass
    instance._po5_listen_token = None
    instance._po5_listen_task = None


async def _stop_all_listeners(agent) -> None:
    """Run-level sweep: cancel EVERY persistent listen task still attached to a
    cached guide/writer/closer instance on the orchestrator.

    Instances are cached on `agent` keyed by lemma id (`_guide_<id>`,
    `_writer_<id>`, …) and reused across chunks. They are torn down on rotation
    (_rotate_agent) and on the decompose path (_cleanup_agents), but a lemma that
    finishes proved/contingent/failed WITHOUT rotating leaves its instance — and
    its 1s-polling _listen_messages coroutine — cached for the rest of the run.
    Call this once at workflow completion so no listener outlives its usefulness.
    Identify instances by the marker attribute _ensure_listening sets, so we do
    not depend on which lemma ids are still live at the end.
    """
    seen = set()
    for value in list(vars(agent).values()):
        if id(value) in seen:
            continue
        seen.add(id(value))
        if getattr(value, "_po5_listen_task", None) is not None:
            await _stop_listening(value)


def _link_writer_guide(agent, writer_agent, guide_agent) -> str:
    """Open a live, bidirectional message channel between THIS writer and THIS
    guide instance and return the guide's current name.

    The writer proves a chunk while the guide is parked in its persistent
    ``_listen_messages`` task (see _ensure_listening), so a writer→guide message
    lands in real time and the guide can reply on the same channel. Likewise a
    guide→writer question between chunks reaches the writer's own live listener.
    `send_message` enforces a
    DIRECTED visibility check (recipient ∈ visibility_graph[sender]), so BOTH
    directions need an edge: writer→guide (to report) and guide→writer (to
    reply). Instance names change on rotation, so we (re)establish the edge each
    chunk with the current names rather than relying on spawn-time wiring.
    Idempotent — adding to a set is a no-op if the edge already exists.
    """
    registry = agent.swarm._registry
    graph = registry.visibility_graph
    writer_name = writer_agent.spec.name
    guide_name = guide_agent.spec.name
    graph.setdefault(writer_name, set()).add(guide_name)
    graph.setdefault(guide_name, set()).add(writer_name)
    return guide_name


async def _rotate_agent(agent, entry: LemmaEntry, cwd: Path, role: str, instance):
    """Dump agent state to disk and destroy the instance so a fresh one is created."""
    # Stop the persistent listen task BEFORE dumping state / disconnecting: the
    # state-dump below is itself a run_ai() call on this instance, and we must not
    # leave a listener racing it (or holding the session) as the backend goes away.
    await _stop_listening(instance)
    # Ask agent to dump its state
    try:
        result = await instance.run_ai(
            inp=(
                "DUMP YOUR STATE: Summarize everything you know about this proof.\n"
                "Include: strategies tried + outcomes, key insights, what to try next.\n"
                "Be concise but complete. This will be your memory for next session."
            ),
            max_turns=3,
        )
        state_text = result.raw_result or ""
    except Exception:
        state_text = ""

    # Write state to disk
    if state_text.strip():
        guide_dir = cwd / entry.workspace / "guide_state"
        guide_dir.mkdir(parents=True, exist_ok=True)
        filename = f"{entry.name}.md" if role == "guide" else f"writer_{entry.name}.md"
        (guide_dir / filename).write_text(state_text)

    # Destroy the instance
    attr = f"_{role}_{entry.id}"
    ctx_attr = f"{attr}_ctx"
    ctx = getattr(agent, ctx_attr, None)
    if ctx:
        try:
            await ctx.__aexit__(None, None, None)
        except Exception:
            pass
    setattr(agent, ctx_attr, None)
    setattr(agent, attr, None)


async def _cleanup_agents(agent, entry: LemmaEntry):
    """Destroy guide + writer + closer for this lemma (no state dump)."""
    for role in ("guide", "writer", "closer"):
        attr = f"_{role}_{entry.id}"
        ctx_attr = f"{attr}_ctx"
        instance = getattr(agent, attr, None)
        # Tear down the persistent listen task before disconnecting the backend.
        await _stop_listening(instance)
        ctx = getattr(agent, ctx_attr, None)
        if ctx:
            try:
                await ctx.__aexit__(None, None, None)
            except Exception:
                pass
            setattr(agent, ctx_attr, None)
            setattr(agent, attr, None)


async def _cleanup_all_agents(agent) -> None:
    """Destroy EVERY cached guide/writer/closer instance on the orchestrator (no
    state dump). Used after a BigSur repair: BigSur may have rewritten signatures
    and re-shaped the DAG for arbitrarily many entries, so any cached agent's
    conversation context now holds a STALE contract. Tearing them all down forces
    the next SELECT to rebuild a fresh guide/writer that reads the corrected ledger
    and files (via _get_guide's init prompt) instead of trusting stale beliefs.

    Instances are keyed `_guide_<id>` / `_writer_<id>` / `_closer_<id>`; discover
    them by attribute-name prefix so we don't depend on which ids are live.
    """
    prefixes = ("_guide_", "_writer_", "_closer_")
    attrs = [a for a in list(vars(agent).keys())
             if any(a.startswith(p) for p in prefixes) and not a.endswith("_ctx")]
    for attr in attrs:
        instance = getattr(agent, attr, None)
        ctx_attr = f"{attr}_ctx"
        await _stop_listening(instance)
        ctx = getattr(agent, ctx_attr, None)
        if ctx:
            try:
                await ctx.__aexit__(None, None, None)
            except Exception:
                pass
        setattr(agent, ctx_attr, None)
        setattr(agent, attr, None)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — detection worker
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DetectVerdict:
    file_path: str
    name: str
    signature_hash: str
    statement: str
    match_type: str  # "cycle" | "reuse" | "none"
    matched_id: str = ""
    matched_name: str = ""
    import_path: str = ""
    reason: str = ""


async def _run_detection(agent, state, ledger, entry, cwd) -> tuple[str, list[DetectVerdict]]:
    """Run cycle detection on staged files. Returns (result, verdicts)."""
    tools = get_lean_tools()
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if not new_decomp_dir.exists():
        return "no_cycle", []

    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean"))
    if not new_files:
        return "no_cycle", []

    await agent._emit("message", f"[PO5] Detecting cycles on {len(new_files)} helpers...")

    pruned_hashes = set()
    for child_id in entry.children:
        child = ledger.get(child_id)
        if child and child.status in (LemmaStatus.PRUNED, LemmaStatus.CYCLE, LemmaStatus.FAILED):
            pruned_hashes.add(child.signature_hash)

    verdicts = []
    cycles_found = False
    matched_pruned = 0

    for f in new_files:
        rel = str(f.relative_to(cwd))
        split = tools.split_theorems(rel)
        if not split or not split.blocks:
            continue
        for block in split.blocks:
            if block.decl_type not in ("theorem", "def"):
                continue
            if "private " in block.text[:50]:
                continue
            if not block.has_sorry:
                verdicts.append(DetectVerdict(
                    file_path=rel, name=block.name,
                    signature_hash=LemmaLedger.compute_signature_hash(block.text),
                    statement=block.text, match_type="none"))
                continue

            sig_hash = LemmaLedger.compute_signature_hash(block.text)
            if sig_hash in pruned_hashes:
                matched_pruned += 1

            det_result = await detect(
                agent=agent, ledger=ledger, name=block.name,
                file_path=rel, signature_hash=sig_hash,
                parent_id=entry.id, cwd=cwd,
            )
            verdicts.append(DetectVerdict(
                file_path=rel, name=block.name, signature_hash=sig_hash,
                statement=block.text,
                match_type=det_result.match_type.value,
                matched_id=det_result.matched_id,
                matched_name=det_result.matched_name,
                import_path=det_result.import_path,
                reason=det_result.reason,
            ))
            if det_result.match_type == MatchType.CYCLE:
                cycles_found = True

    if matched_pruned > 0 and matched_pruned >= len(new_files):
        shutil.rmtree(new_decomp_dir)
        return "rejected", []

    # Commit: UNION-MERGE new_decomposition/ into decomposed/.
    #
    # We do NOT rotate the old decomposed/ aside to decomposed_old_N (the legacy
    # behavior). That rotation ORPHANED IMPORTS: a re-extraction on this file
    # rebuilds new_decomposition/ from the CURRENT blocks only, so any already-
    # proved helper that a sibling still imports (e.g. bd_shape.lean importing the
    # bd_* leaves) was shoved into decomposed_old_N and its import path
    # (.../decomposed/lemma_helper_bd_*) went dangling → "bad import" build gate
    # that neither writer nor guide can fix. Nothing ever read decomposed_old_N.
    #
    # Union-merge instead: copy every new file into the existing decomposed/,
    # OVERWRITING same-named files with the fresh version and KEEPING all others.
    # Referenced-but-not-regenerated helpers stay in place, so imports keep
    # resolving. Genuinely-dead files that linger are BigSur's to prune later —
    # decomposition repair is BigSur's job, not a blind directory swap's.
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if decomposed_dir.exists():
        shutil.copytree(new_decomp_dir, decomposed_dir, dirs_exist_ok=True)
        shutil.rmtree(new_decomp_dir)
    else:
        new_decomp_dir.rename(decomposed_dir)
    # Rewrite new_decomposition→decomposed module refs in the merged-in files
    # (and Stub.lean). rglob over decomposed/ covers both old and just-copied files.
    _rewrite_imports(cwd, entry.workspace, "new_decomposition", "decomposed")

    # Guard the exact failure the rotation used to cause: after committing, no file
    # in decomposed/ should import a module that doesn't exist on disk. A dangling
    # import is a DAG inconsistency only BigSur can repair — surface it loudly here
    # instead of letting it become a silent, unfixable build gate the writer loops on.
    dangling = _find_dangling_imports(cwd, entry.workspace)
    if dangling:
        await agent._emit("message",
            f"[PO5] ⚠️ Decomposition has {len(dangling)} DANGLING import(s) after commit "
            f"(module imported but file missing) — a build gate the writer cannot fix; "
            f"BigSur repair territory: {dangling[:5]}")

    for v in verdicts:
        v.file_path = v.file_path.replace("/new_decomposition/", "/decomposed/")

    await agent._emit("message",
        f"[PO5] Detection: {len(verdicts)} verdicts, cycles={'yes' if cycles_found else 'no'}")
    return ("cycle_found" if cycles_found else "no_cycle"), verdicts


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — ledger mutations (UPDATE phase internals)
# ═══════════════════════════════════════════════════════════════════════════════

def _apply_verdicts(state: PO5State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Register detect verdicts into ledger."""
    verdicts = getattr(state, '_detect_verdicts', None)
    if not verdicts:
        return
    tools = get_lean_tools()

    for v in verdicts:
        if v.match_type == "cycle":
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str):
                ledger.mark_cycle(new.id, v.matched_id)
            state.cycles_detected += 1
        elif v.match_type == "reuse":
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str):
                ledger.add_parent(new.id, v.matched_id)
                matched = ledger.get(v.matched_id)
                if matched and matched.status == LemmaStatus.PROVED:
                    ledger.mark_proved(new.id, v.import_path, proved_by="shortcut")
                else:
                    ledger.mark_contingent(new.id)
        else:
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str) and not tools.has_sorry(v.file_path):
                cr = tools.check_compiles(v.file_path)
                # Transitive oracle, not text/warning has_sorry: a locally clean
                # file can still depend on sorryAx through an import.
                if cr.success and _entry_transitively_proven(tools, new):
                    ledger.mark_proved(new.id, v.file_path.replace("/", ".").removesuffix(".lean"),
                                       proved_by="direct")
                elif cr.success:
                    ledger.mark_contingent(new.id)

    state._detect_verdicts = None
    if entry.status == LemmaStatus.PROVING:
        ledger.mark_contingent(entry.id)


def _entry_transitively_proven(tools, entry: LemmaEntry) -> bool:
    """AUTHORITATIVE per-entry proof check: the entry's obligation (its own
    theorem + any mutual-group peers) compiles, has no LOCAL sorry, and — via
    `#print axioms` — depends on NO `sorryAx`.

    This is the same oracle the per-target gate uses (`_attempt_prove`). It must
    be used everywhere an entry is promoted to PROVED, because the text/warning
    based `check_compiles.has_sorry` misses sorry reached transitively through
    imported/assembled dependencies (and is suppressed by `set_option
    warn.sorry false`). A synthetic `<file:...>` root has no theorem of its own,
    so it is verified by its children, not here — callers skip it.
    """
    stub_rel = entry.file_path
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return False
    protected = _get_protected_names(tools, stub_rel, entry)
    if not protected:
        return False
    local_sorry = tools.get_sorries_by_theorem(stub_rel)
    if any(local_sorry.get(n) for n in protected):
        return False
    ax = tools.axioms_by_theorem(stub_rel, sorted(protected))
    return all(ax.is_proven(n) for n in protected)


def _proved_or_contingent(tools, ledger, entry, cwd, stub_rel) -> str | None:
    """Shared PROVED/CONTINGENT/fall-through decision for the prove loops.

    Assumes the file already compiles. Returns:
      - "proved":     protected block is transitively sorry-free (marks PROVED).
      - "contingent": block is locally clean on its OWN target(s) but transitively
                      unproven — the residual sorry lives in something it cannot
                      edit from this file (a same-file sibling, a registered child,
                      OR an imported cross-branch dependency). We are WAITING on a
                      proof in flight (marks CONTINGENT); _propagate_proved promotes
                      it once that dependency clears.
      - None:         the entry has its OWN local sorry still to prove (real editable
                      work) → caller falls through to continue proving / extraction.

    Centralizes the logic the per-target gate uses so the deep and grace loops
    stay consistent. The verdict is scope-symmetric: own sorry → keep proving;
    locally clean but transitively unproven → contingent, regardless of WHERE the
    residual sorry lives (sibling / child / imported cousin).
    """
    if _entry_transitively_proven(tools, entry):
        ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
        return "proved"
    local_sorry = tools.get_sorries_by_theorem(stub_rel)
    # CONTINGENT means "locally clean, only waiting on a sibling/child proof in
    # flight". If THIS entry's OWN target(s) still carry sorry, it has real work
    # to do and must NOT be parked contingent — doing so hides it from SELECT
    # (which only picks PENDING), so no prover is ever dispatched and BigSur gets
    # re-escalated with "nothing to do here" while the goals sit open. This was
    # the callElim defUseWF_fold trap: BigSur reset it to PENDING after threading
    # a hypothesis, a prover re-entered, `entry.children` was truthy, and it got
    # flipped straight back to contingent (which also clears priority_boost),
    # burying the one node that actually needed proving.
    protected = _get_protected_names(tools, stub_rel, entry)
    has_own_sorry = any(n in protected and positions
                        for n, positions in local_sorry.items())
    if has_own_sorry:
        return None  # real local work remains → keep proving THIS node
    # We are here iff: transitively UNPROVEN (oracle sees a sorry somewhere) AND
    # locally clean on our own target(s). So the residual sorry lives in something
    # we cannot edit from this file — a same-file sibling, a registered child, OR
    # an IMPORTED cross-branch dependency. All three are "waiting on a proof in
    # flight", NOT a local stall → park CONTINGENT (the old code checked only
    # sibling_sorry/entry.children and missed the imported-dependency case, which
    # then fell through to give_up → BigSur: the callElim_sim_canfail loop).
    # _propagate_proved promotes us once the dependency clears.
    ledger.mark_contingent(entry.id)
    return "contingent"


def _propagate_proved(ledger: LemmaLedger, cwd: Path):
    """Re-check contingent entries — mark proved only if TRANSITIVELY proven.

    A CONTINGENT entry is one that was locally sorry-free but waiting on a
    sibling/child. It is promoted to PROVED only when the authoritative
    transitive oracle confirms it depends on no `sorryAx` — NOT merely when the
    file is textually sorry-free. Entries that never clear stay CONTINGENT and
    are surfaced by the CHECK stuck-handler (re-picked → PENDING, or escalated
    to the guide) instead of being silently promoted.
    """
    tools = get_lean_tools()
    changed = True
    while changed:
        changed = False
        for e in ledger.entries():
            if e.status != LemmaStatus.CONTINGENT:
                continue
            if e.name.startswith("<"):
                # Synthetic file-root: proven when all its real children are.
                kids = ledger.get_children(e.id)
                real_kids = [k for k in kids if not k.name.startswith("<")]
                if real_kids and all(k.status == LemmaStatus.PROVED for k in real_kids):
                    ledger.mark_proved(e.id, e.file_path.replace("/", ".").removesuffix(".lean"),
                                       proved_by="assembly")
                    changed = True
                continue
            if not (cwd / e.file_path).exists():
                continue
            if _entry_transitively_proven(tools, e):
                ledger.mark_proved(e.id, e.file_path.replace("/", ".").removesuffix(".lean"),
                                   proved_by="assembly")
                changed = True


def _register_all_helpers(state: PO5State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Register public theorems/defs from Stub.lean into ledger."""
    if entry.status == LemmaStatus.FAILED:
        return
    tools = get_lean_tools()
    stub_rel = _resolve_stub_simple(entry)
    if not (cwd / stub_rel).exists():
        return

    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return

    current_names = {b.name for b in split.blocks
                     if b.decl_type in ("theorem", "def") and "private " not in b.text[:50]}

    existing_names = {e.name for e in ledger.entries()}
    for block in split.blocks:
        if block.name in existing_names or block.name == entry.name:
            continue
        if block.decl_type not in ("theorem", "def") or "private " in block.text[:50]:
            continue
        sig_hash = LemmaLedger.compute_signature_hash(block.text)
        new = _register_lemma(state, ledger,
            name=block.name, file_path=stub_rel,
            workspace=entry.workspace, signature_hash=sig_hash,
            statement=block.text, parent_id=entry.id)
        if not isinstance(new, str) and not block.has_sorry:
            cr = tools.check_compiles(stub_rel)
            # Promote to PROVED only when the transitive oracle confirms it — a
            # locally sorry-free helper can still depend on sorryAx. Otherwise
            # leave it CONTINGENT so _propagate_proved re-checks it later.
            if cr.success and _entry_transitively_proven(tools, new):
                ledger.mark_proved(new.id, stub_rel.replace("/", ".").removesuffix(".lean"),
                                   proved_by="direct")
            elif cr.success:
                ledger.mark_contingent(new.id)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — compilation fixer
# ═══════════════════════════════════════════════════════════════════════════════

async def _run_fixer(agent, state: PO5State, cwd: Path, error_text: str, advice: str) -> bool:
    """Spawn compilation fixer with guide's advice."""
    async with swarm_agent("compilation_fixer", swarm=agent.swarm, cwd=agent._cwd) as fixer:
        outcome = await verified_loop(
            agent_ctx=fixer,
            initial_input=(
                f"Fix these compilation errors:\n{error_text}\n\n"
                f"Guide's diagnosis:\n{advice}"
            ),
            verify=lambda: None,
            max_rounds=2, max_turns=30, use_run_ai=False,
        )
    return outcome.success if outcome else False


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — pure utilities
# ═══════════════════════════════════════════════════════════════════════════════

def _resolve_stub(entry: LemmaEntry, cwd: Path, state: PO5State) -> str:
    stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
    if not (cwd / stub_rel).exists():
        setup_child_workspace(cwd, entry.file_path, state.root_workspace,
                              state.use_cheat_sheet, state.cheat_sheet_path)
        stub_rel = f"{entry.workspace}/Stub.lean"
        if not (cwd / stub_rel).exists():
            stub_rel = entry.file_path
    return stub_rel


def _resolve_stub_simple(entry: LemmaEntry) -> str:
    return f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path


def _make_verifier(entry, stub_rel, original_content, ledger, cwd):
    ancestor_modules = []
    for anc_id in ledger.get_ancestry(entry.id):
        anc = ledger.get(anc_id)
        if anc:
            ancestor_modules.append(anc.workspace.replace("/", "."))
    return make_proof_writer_verifier(
        stub_rel, original_content, entry.workspace, entry.name,
        ancestor_modules=ancestor_modules, ledger=ledger)


def _sibling_target_names(ledger, entry, cwd: Path | None = None,
                          stub_rel: str | None = None) -> set[str]:
    """Names of OTHER top-level declarations in this entry's file that must NOT be
    extracted as helpers.

    Two sources, unioned:
    1. Other registered obligations sharing this file_path (the ledger view). Covers
       the multi-target synthetic-root case where every target is registered.
    2. Every OTHER top-level theorem/def present in the ORIGINAL file snapshot
       (Stub.clean.lean). This covers the case where the user targeted only a SUBSET
       of the file's sorry-theorems — the un-targeted ones aren't in the ledger, but
       they are still original obligations, not helpers. Genuine writer-created helpers
       are absent from the snapshot (created later), so they stay extractable.

    The entry's own name (and mutual-group peers, handled by protected_names) are the
    caller's concern; here we just exclude the entry itself and the synthetic root.
    """
    names = {
        e.name for e in ledger.entries()
        if e.id != entry.id and e.file_path == entry.file_path
        and not e.name.startswith("<")  # exclude the synthetic file-root marker
    }
    if cwd is not None:
        clean = cwd / entry.workspace / "Stub.clean.lean"
        if clean.exists():
            tools = get_lean_tools()
            snap = tools.split_theorems(str(clean.relative_to(cwd)))
            if snap and not snap.error:
                for b in snap.blocks:
                    if b.name != entry.name and b.decl_type in ("theorem", "def"):
                        names.add(b.name)
    names.discard(entry.name)
    return names


def _filter_requested_targets(targets, split, requested_names):
    """Narrow sorry-targets to the user's requested theorem names.

    Empty requested_names → return all targets (prove everything with sorry).
    A requested name matches a target if it IS the target's representative name,
    or (for mutual groups) if it is any member of that group. Requested names that
    are already proven or don't exist simply don't match (reported by the caller).
    """
    if not requested_names:
        return targets
    wanted = set(requested_names)
    selected = []
    for block, is_mut in targets:
        names_for_target = {block.name}
        if block.mutual_group is not None:
            names_for_target |= set(split.mutual_groups.get(block.mutual_group, []))
        if wanted & names_for_target:
            selected.append((block, is_mut))
    return selected


def _collect_sorry_targets(split):
    """Top-level proof obligations in a freshly-split file.

    Returns a list of (representative_block, is_mutual) tuples — one per standalone
    theorem/def that has sorry, and one per mutual group that contains any sorry
    (represented by its first member, matching how _get_protected_names expands a
    mutual group). Definitions and already-proven blocks are skipped.
    """
    targets = []
    seen_groups: set[int] = set()
    for block in split.blocks:
        if block.mutual_group is not None:
            gid = block.mutual_group
            if gid in seen_groups:
                continue
            members = [b for b in split.blocks if b.mutual_group == gid]
            if any(b.has_sorry for b in members):
                seen_groups.add(gid)
                # Representative = first member (lowest start line)
                rep = min(members, key=lambda b: b.start)
                targets.append((rep, True))
            continue
        if block.decl_type not in ("theorem", "def"):
            continue
        if not block.has_sorry:
            continue
        targets.append((block, False))
    return targets


def _requested_obligation_names(ledger, state, root_stub: str) -> list[str]:
    """The real theorem names the TM asked us to prove, for the root file.

    These are the entries registered at INIT (already narrowed to the requested
    subset by `_filter_requested_targets`): either the single real root, or the
    children of the synthetic `<file:...>` root. Synthetic `<...>` labels are
    excluded. Mutual-group members are expanded so the whole group is verified.
    """
    root = ledger.get(state.root_id)
    if not root:
        return []
    if root.name.startswith("<"):
        entries = ledger.get_children(state.root_id)
    else:
        entries = [root]

    names: set[str] = set()
    split = get_lean_tools().split_theorems(root_stub)
    blocks = split.blocks if split and not split.error else []
    groups = split.mutual_groups if split and not split.error else {}
    for e in entries:
        if e.name.startswith("<"):
            continue
        names.add(e.name)
        # Expand mutual groups: every member must be sorry-free, not just the rep.
        for b in blocks:
            if b.name == e.name and b.mutual_group is not None:
                names.update(groups.get(b.mutual_group, []))
                break
    return sorted(names)


def _is_top_level(ledger, state, entry) -> bool:
    """True iff `entry` is one of the TOP-LEVEL requested obligations.

    A top-level obligation is either the single real root, or a DIRECT child of
    the synthetic `<file:...>` root (one of the theorems the TM asked us to prove
    — see `_requested_obligation_names`). Decomposed helpers (grandchildren) are
    NOT top-level: the user never asked for them, so we don't burden the user
    with a fix request about a lemma the prover invented.
    """
    if entry.id == state.root_id:
        return True
    root = ledger.get(state.root_id)
    if root and root.name.startswith("<"):
        parent = ledger.get_parent(entry.id)
        return parent is not None and parent.id == state.root_id
    return False


def _record_give_up(state, entry, reason: str):
    """Accumulate a give-up reason on state so it propagates to the TM → user.

    De-duplicates: the same lemma re-deriving the same give-up must not append the
    identical line hundreds of times (Bug #3 symptom)."""
    line = f"'{entry.name}': {reason}"
    existing = state.give_up_reason.split("\n") if state.give_up_reason else []
    if line in existing:
        return
    if state.give_up_reason:
        state.give_up_reason += f"\n{line}"
    else:
        state.give_up_reason = line


async def _ask_guide_user_fix(agent, state, ledger, entry, cwd, give_up_reason: str):
    """Ask the guide whether the USER must fix something before this can be proved.

    Only meaningful for TOP-LEVEL requested theorems (the user owns the goal
    statement and its definitions/dependencies; they did not write the prover's
    internal helpers). Records the request on `state.user_fix_request` so the
    Task Manager can relay it verbatim to the user. Best-effort: any failure
    leaves user_fix_request untouched (the give_up_reason still propagates).
    """
    if not _is_top_level(ledger, state, entry):
        return
    try:
        decision, _reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["user_fix", "no_user_fix"],
            task=(
                f"You are giving up on the top-level theorem '{entry.name}'.\n"
                f"Give-up reason: {give_up_reason}\n\n"
                f"Does the USER need to fix something before this can be proved?\n"
                f"- user_fix: the goal statement is false/mis-stated, a definition "
                f"is wrong, a needed hypothesis is missing, or a required "
                f"dependency/lemma is unavailable — something ONLY the user can change.\n"
                f"- no_user_fix: it's provable as stated; we just couldn't find the proof."
            ),
            post_prompt=(
                "FIX: <if user_fix, one or two concrete sentences telling the user "
                "EXACTLY what to change (file/def/statement); else 'none'>"),
            post_prompt_parser=lambda raw: {
                "fix": (m.group(1).strip()
                        if (m := re.search(r'FIX:\s*(.+)', raw, re.DOTALL)) else "")},
        )
    except Exception as e:
        await agent._emit("message", f"[PO5] user-fix consult failed: {e}")
        return
    if decision == "user_fix":
        fix = extras.get("fix", "").strip()
        if fix and fix.lower() != "none":
            request = f"'{entry.name}': {fix}"
            if state.user_fix_request:
                state.user_fix_request += f"\n{request}"
            else:
                state.user_fix_request = request
            await agent._emit("message", f"[PO5] Guide requests user fix for '{entry.name}': {fix}")


def _get_protected_names(tools, stub_rel, entry) -> set[str]:
    split = tools.split_theorems(stub_rel)
    protected = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break
    return protected


def _format_progress(prev: int | None, current: int, *, compiles: bool = True) -> str:
    """Render the chunk-over-chunk progress line from the LEAF-sorry count.

    `current`/`prev` are counts of literal `sorry` tokens in our obligations
    (build-INDEPENDENT), not the axioms-verdict decl count. The one special case
    is the ENDGAME: 0 sorries left but the file does not yet compile — the writer
    has replaced the last sorry with a real (still-buggy) proof and is closing
    compile errors. That is forward motion on the critical path, NOT a stall, so
    it gets its own positive message (and the caller keeps the idle clock alive)."""
    if current == 0 and not compiles:
        if prev is not None and prev > 0:
            return (f"PROGRESS: last sorry closed ({prev} → 0). SKETCH COMPLETE — "
                    f"0 sorries remaining; writer is closing compile errors on the "
                    f"full proof (endgame, not a stall).")
        return ("SKETCH COMPLETE — 0 sorries remaining; writer is closing compile "
                "errors on the full proof (endgame, not a stall).")
    if prev is None:
        return f"Open leaf-sorries: {current}."
    if current < prev:
        return f"PROGRESS: leaf-sorries {prev} → {current}."
    elif current == prev:
        return f"NO REDUCTION: still {current} leaf-sorries."
    return f"Leaf-sorry count: {current} (was {prev})."


def _format_sorry_map(tsm, protected_names: set, siblings: set) -> str:
    """Render the AUTHORITATIVE dependency+sorry overview for the guide.

    ONE consolidated picture, recomputed this chunk from ground truth — it
    supersedes anything the guide remembers or reads from snapshot notes. For each
    protected target: is it done, and exactly which in-file lemmas it transitively
    depends on that still carry a `sorry` (with fresh line numbers)."""
    if tsm.error:
        return f"AUTHORITATIVE SORRY MAP: unavailable (parse error: {tsm.error})\n"
    if not tsm.build_ok:
        return (
            "AUTHORITATIVE SORRY MAP: build FAILED — cannot confirm anything "
            f"(treat all as unproven): {tsm.build_error}\n")

    def _line(n: str) -> str:
        d = tsm.decls.get(n)
        if not d:
            return f"    • {n}  (not found in file)"
        pos = ""
        if d.sorry_positions:
            ls = ", ".join(str(p.get("line", "?") + 1) for p in d.sorry_positions)
            pos = f"  sorry @ line {ls}"
        elif d.start:
            pos = f"  (decl @ line {d.start}, transitive sorry via a dep)"
        return f"    • {n}{pos}"

    out = [
        "AUTHORITATIVE SORRY MAP (recomputed NOW from ground truth — this "
        "SUPERSEDES any line numbers you remember or that appear in snapshot notes):"
    ]
    for t in sorted(protected_names):
        info = tsm.targets.get(t)
        if info is None:
            out.append(f"  TARGET {t}: (not found in file)")
            continue
        if info.done:
            out.append(f"  TARGET {t}: ✅ DONE (transitively sorry-free)")
            continue
        # open deps that are OURS (not the target itself, not siblings)
        ours = [n for n in info.open_deps
                if n != t and n not in siblings]
        out.append(f"  TARGET {t}: ❌ NOT DONE (transitively depends on sorry)")
        if t in info.open_deps and (tsm.decls.get(t) and tsm.decls[t].sorry_positions):
            out.append("    (its own body still has a literal sorry)")
            out.append(_line(t))
        if ours:
            out.append("    In-file lemmas it uses that are still UNPROVEN (yours to close):")
            for n in ours:
                out.append(_line(n))
        sib_open = [n for n in info.open_deps if n in siblings]
        if sib_open:
            out.append(f"    (NOT yours — sibling obligations still open: {sib_open})")
    out.append(f"  Transitive OPEN-sorry count reachable from your targets: "
               f"{tsm.open_sorry_count()}")
    return "\n".join(out) + "\n"


def _verify_extraction(tools, stub_rel: str, entry: LemmaEntry, output_dir: Path) -> str | None:
    # Check that files were actually created — if the extractor reverted, this catches it
    if not output_dir.exists() or not list(output_dir.glob("lemma_helper_*.lean")):
        return "No helper files created (extractor may have reverted)"
    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return f"Cannot parse Stub.lean: {split.error if split else 'unknown'}"
    protected = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    bad = [n for n in protected if n in sorry_info]
    if bad:
        return f"Protected block has sorry: {bad}"
    return None


def _repair_orphaned_decomposed(entry: LemmaEntry, cwd: Path, stub_rel: str):
    """Detect and fix: decomposed/ dir exists but Stub.lean doesn't import from it.

    This happens after a process crash between extraction and state persistence,
    or when a child failure brings the parent back to PROVE without proper restoration.
    Fix: re-add the missing imports so Stub.lean uses the precompiled helpers.
    """
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if not decomposed_dir.exists():
        return
    helper_files = sorted(decomposed_dir.glob("lemma_helper_*.lean"))
    if not helper_files:
        return

    stub_path = cwd / stub_rel
    content = stub_path.read_text()

    # Check if Stub.lean already imports from decomposed/
    ws_module = entry.workspace.replace("/", ".")
    decomposed_import_prefix = f"import {ws_module}.decomposed."
    if decomposed_import_prefix in content:
        return

    # Stub.lean doesn't import the helpers — add them
    lines = content.splitlines()
    import_end = 0
    for i, l in enumerate(lines):
        if l.strip().startswith("import "):
            import_end = i + 1

    new_imports = []
    for hf in helper_files:
        module = f"{ws_module}.decomposed.{hf.stem}"
        imp_line = f"import {module}"
        if imp_line not in content:
            new_imports.append(imp_line)

    if not new_imports:
        return

    # Insert imports and remove inlined helper blocks (they're now in separate files)
    # Strategy: keep only the main theorem + any block not in decomposed/
    # Simple approach: just add imports — the duplicate definitions will cause errors
    # Better: use split_theorems to identify and remove inlined blocks that exist in decomposed/
    tools = get_lean_tools()
    helper_names = {hf.stem.removeprefix("lemma_helper_") for hf in helper_files}

    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        # Can't parse — just add imports and hope for the best
        lines = lines[:import_end] + new_imports + lines[import_end:]
        stub_path.write_text("\n".join(lines))
        return

    # Remove blocks whose names match extracted helpers
    lines_to_remove: set[int] = set()
    for block in split.blocks:
        if block.name in helper_names and block.name != entry.name:
            for i in range(block.start - 1, block.end):
                lines_to_remove.add(i)

    new_lines = lines[:import_end] + new_imports
    for i in range(import_end, len(lines)):
        if i not in lines_to_remove:
            new_lines.append(lines[i])

    # Clean up multiple blank lines
    cleaned = []
    prev_blank = False
    for l in new_lines:
        if l.strip() == "":
            if not prev_blank:
                cleaned.append(l)
            prev_blank = True
        else:
            cleaned.append(l)
            prev_blank = False

    stub_path.write_text("\n".join(cleaned))


def _revert_extraction(entry: LemmaEntry, cwd: Path):
    predecomp = cwd / entry.workspace / "Stub.predecomp.lean"
    stub = cwd / entry.workspace / "Stub.lean"
    if predecomp.exists():
        shutil.copy2(predecomp, stub)
    for subdir in ("new_decomposition", "decomposed"):
        d = cwd / entry.workspace / subdir
        if d.exists():
            shutil.rmtree(d)


def _rewrite_imports(cwd: Path, workspace: str, old_name: str, new_name: str):
    old_mod = old_name.replace("/", ".")
    new_mod = new_name.replace("/", ".")
    stub = cwd / workspace / "Stub.lean"
    if stub.exists():
        content = stub.read_text()
        if old_mod in content:
            stub.write_text(content.replace(old_mod, new_mod))
    renamed = cwd / workspace / new_name
    if renamed.exists():
        for f in renamed.rglob("*.lean"):
            content = f.read_text()
            if old_mod in content:
                f.write_text(content.replace(old_mod, new_mod))


def _sweep_decomposed_old(cwd: Path) -> int:
    """Remove any leftover `decomposed_old_*` dirs anywhere under the workspace.

    These are artifacts of the RETIRED decomposition-commit rotation (which
    orphaned imports); nothing reads them. New runs never create them, but a dir
    left by an older run would still be picked up by list_theorems / oracle scans,
    so we clear them once at startup. Returns the count removed."""
    removed = 0
    for d in cwd.rglob("decomposed_old_*"):
        if d.is_dir():
            try:
                shutil.rmtree(d)
                removed += 1
            except OSError:
                pass
    return removed


def _find_dangling_imports(cwd: Path, workspace: str) -> list[str]:
    """Return `import` statements in decomposed/**/*.lean that reference a
    WORKSPACE-LOCAL module whose .lean file does not exist on disk.

    A workspace-local module is one whose dotted name maps to a path under
    `cwd/<workspace>` (i.e. a Sandbox decomposition module) — we only check those,
    so external library imports (Strata.*, Mathlib, …) are never false-flagged.
    A dangling local import is the orphaned-import signature the old
    decomposed_old rotation produced: the module is imported but its file was
    moved/removed, giving a "bad import" / "no such file" build gate. Each result
    is 'file.lean → missing.module' for a human-readable log."""
    decomposed = cwd / workspace / "decomposed"
    if not decomposed.exists():
        return []
    ws_prefix = workspace.replace("/", ".") + "."  # e.g. "StrataAgent.Sandbox."
    dangling: list[str] = []
    for f in decomposed.rglob("*.lean"):
        try:
            lines = f.read_text().splitlines()
        except OSError:
            continue
        for line in lines:
            s = line.strip()
            if not (s.startswith("import ") or s.startswith("public import ")):
                continue
            mod = s.split("import", 1)[1].strip().split()[0] if s.split("import", 1)[1].strip() else ""
            if not mod.startswith(ws_prefix):
                continue  # external / non-local import — not ours to check
            target = cwd / (mod.replace(".", "/") + ".lean")
            if not target.exists():
                try:
                    rel = f.relative_to(cwd)
                except ValueError:
                    rel = f
                dangling.append(f"{rel} → {mod}")
    return dangling


def _resolve_import_dependencies(ledger: LemmaLedger, cwd: Path):
    """Add cross-branch dependency edges inferred from Lean imports.

    This is meaningful ONLY for the separate-workspace model where each lemma
    lives in its own file (module ↔ entry is 1:1). In a SHARED multi-theorem
    file, every target and the synthetic root have the same file_path/module, so
    (a) a module→id map would collapse them and (b) reading the shared file's
    imports for every entry would attribute a single helper-import to all of
    them — corrupting the DAG. The correct parent→child edges for shared-file
    targets are already set at registration/extraction time, so we simply skip
    any entry whose file_path is not unique to it (both as import source and as
    resolvable target).
    """
    tools = get_lean_tools()

    file_path_counts: dict[str, int] = {}
    for e in ledger.entries():
        file_path_counts[e.file_path] = file_path_counts.get(e.file_path, 0) + 1

    module_to_id = {}
    for e in ledger.entries():
        if file_path_counts[e.file_path] != 1:
            continue  # ambiguous shared-file module — not a resolvable target
        module = e.file_path.replace("/", ".").removesuffix(".lean")
        module_to_id[module] = e.id

    existing_edges = set()
    for e in ledger.entries():
        for cid in e.children:
            existing_edges.add((e.id, cid))

    for e in ledger.entries():
        if file_path_counts[e.file_path] != 1:
            continue  # shared file — imports can't be attributed to one entry
        if not (cwd / e.file_path).exists():
            continue
        imports = tools.check_imports(e.file_path)
        if imports.error:
            continue
        for imp in imports.imports:
            if imp in module_to_id:
                dep_id = module_to_id[imp]
                if dep_id == e.id:
                    continue
                if (e.id, dep_id) in existing_edges or (dep_id, e.id) in existing_edges:
                    continue
                ancestry = ledger.get_ancestry(e.id)
                if dep_id in ancestry:
                    continue
                ledger.add_parent(e.id, dep_id)


def _find_dfs_candidates(ledger, start_id):
    if not start_id:
        pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
        return (None, pending)
    current = ledger.get(start_id)
    visited = set()
    while current:
        if current.id in visited:
            break
        visited.add(current.id)
        pending_kids = ledger.pending_children(current.id)
        if pending_kids:
            return (current, pending_kids)
        current = ledger.get_parent(current.id)
    pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
    return (None, pending)


def _topo_sort(ledger: LemmaLedger) -> list[str]:
    result = []
    visited = set()
    def visit(eid):
        if eid in visited:
            return
        visited.add(eid)
        e = ledger.get(eid)
        if e:
            for cid in e.children:
                visit(cid)
        result.append(eid)
    for e in ledger.entries():
        visit(e.id)
    return result


def _build_ledger_summary(ledger: LemmaLedger, entry: LemmaEntry) -> str:
    lines = [f"Lemma DAG ({len(list(ledger.entries()))} entries):"]
    for e in ledger.entries():
        marker = {"proved": "✓", "contingent": "◇", "proving": "⟳",
                  "pending": "○", "failed": "✗", "cycle": "⊘"}.get(e.status, "?")
        suffix = ""
        if e.failure_reason:
            suffix = f" FAIL: {e.failure_reason[:40]}"
        lines.append(f"  {marker} {e.name} [{e.status}] d={e.depth}{suffix}")
    return "\n".join(lines)


def _periodic_checkpoint_due(agent) -> bool:
    """True if no full swarm checkpoint has happened in CHECKPOINT_INTERVAL_SECONDS.
    Uses the CheckpointManager's own clock, which every full checkpoint resets — so
    a proved-lemma / run-done checkpoint also postpones the periodic one."""
    mgr = getattr(getattr(agent, "swarm", None), "_checkpoint_manager", None)
    if mgr is None:
        return False
    try:
        return mgr.should_checkpoint_periodic(CHECKPOINT_INTERVAL_SECONDS)
    except Exception:
        return False


async def _checkpoint(agent, ledger: LemmaLedger, cwd: Path, state: PO5State, reason: str):
    """The ONE checkpoint used everywhere — proof state AND full swarm state.

    Two layers, always together so there is a single consistent checkpoint:
      1. Proof state: ledger.save() (lemma_ledger.json) + _save_state (po5_state.yaml)
         — the proof DAG + phase, so a re-dispatched prover resumes the proof.
      2. Swarm state: swarm.checkpoint(reason) — session IDs, visibility, handoffs,
         and a workspace snapshot — so a full dashboard/process restart can revive
         the whole swarm and the proved work on disk.
    Best-effort on the swarm layer (never let a checkpoint failure sink the run)."""
    ledger.save()
    _save_state(cwd, state)
    swarm = getattr(agent, "swarm", None)
    cp = getattr(swarm, "checkpoint", None)
    if callable(cp):
        try:
            await cp(reason=reason)
        except Exception as e:
            await agent._emit("message", f"[PO5] swarm checkpoint ({reason}) failed: {e}")


def _save_state(cwd: Path, state: PO5State):
    import yaml
    state_dir = cwd / "StrataAgent" / "strataswarm" / "temp"
    state_dir.mkdir(parents=True, exist_ok=True)
    data = {
        "root_workspace": state.root_workspace,
        "root_theorem_name": state.root_theorem_name,
        "requested_theorem_names": list(state.requested_theorem_names),
        "use_cheat_sheet": state.use_cheat_sheet,
        "cheat_sheet_path": state.cheat_sheet_path,
        "root_id": state.root_id,
        "stage": state.stage,
        "current_lemma_id": state.current_lemma_id,
        "total_attempts": state.total_attempts,
        "lemmas_proved": state.lemmas_proved,
        "cycles_detected": state.cycles_detected,
        "give_up_reason": state.give_up_reason,
        "user_fix_request": state.user_fix_request,
    }
    (state_dir / "po5_state.yaml").write_text(
        yaml.dump(data, default_flow_style=False))


def _load_state(cwd: Path, workspace_rel: str) -> PO5State | None:
    import yaml
    state_file = cwd / "StrataAgent" / "strataswarm" / "temp" / "po5_state.yaml"
    if not state_file.exists():
        return None
    try:
        data = yaml.safe_load(state_file.read_text())
        if data.get("root_workspace") != workspace_rel:
            return None
        s = PO5State()
        for k, v in data.items():
            if hasattr(s, k):
                setattr(s, k, v)
        return s
    except Exception:
        return None
