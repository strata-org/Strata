"""Domain-specific hook policies for StrataSwarm agents.

Defines what each agent type can and cannot access. Loaded at runtime by
the swarm and swarm_agent helper.

Uses framework utilities from _workspace_hooks (path matching, extraction).
"""

from __future__ import annotations

import logging
import random
from typing import Any

from claude_agent_sdk.types import HookMatcher

from .._workspace_hooks import matches_any, deny, allow, make_hook

logger = logging.getLogger("strataswarm.hooks")




# ─── Live per-run tool block ─────────────────────────────────────────────────

def blocked_tools_hooks(agent_ref) -> dict:
    """Deny any tool listed in agent_ref._blocked_tools, checked LIVE per call.

    The set is populated by run_ai(block_tools=[...]) for the duration of one run
    (inside _driving_lock) and cleared on exit — so a persistent _listen_messages
    consume, which never overlaps a run_ai, always sees it empty. Matches on the
    bare tool name and, for MCP tools, the final `__`-segment, so a caller can
    pass either "send_message" or the full "mcp__agent_messaging__send_message".

    The caller passing block_tools is responsible for telling the agent WHY in the
    prompt (so it never attempts the call). This deny is the generic failsafe.
    """
    async def _block(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PreToolUse":
            return {}
        blocked = getattr(agent_ref, "_blocked_tools", None)
        if not blocked:
            return {}
        tool_name = input_data.get("tool_name", "")
        short = tool_name.rsplit("__", 1)[-1]
        if tool_name in blocked or short in blocked:
            return deny(tool_name, (
                f"'{short}' is temporarily disabled for this call. Do NOT use it "
                f"now — complete your response using your other tools, or just "
                f"answer inline."
            ))
        return {}

    return {
        "PreToolUse": [HookMatcher(matcher=".*", hooks=[_block])]
    }


# ─── Budget warning: fires on PreToolUse when turns running low ──────────────

def budget_warning_hooks(agent_ref) -> dict:
    """Warn the agent when it's running low on turns.

    Uses PreToolUse to inject additionalContext before the next tool call
    when <10% turns remain. agent_ref is a reference to the SwarmAgent
    so we can read _current_turns and max_turns.
    """
    warned = {"sent": False}

    async def _check_budget(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PreToolUse":
            return {}
        if warned["sent"]:
            return {}

        max_turns = agent_ref.spec.max_turns
        current = getattr(agent_ref, '_current_turns', 0)
        if not max_turns or not current:
            return {}

        remaining = max_turns - current
        threshold = max(1, int(max_turns * 0.1))
        if remaining <= threshold and remaining > 0:
            warned["sent"] = True
            return {
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "additionalContext": (
                        f"⚠️ BUDGET WARNING: You have ~{remaining} turns remaining "
                        f"out of {max_turns}. Wrap up NOW. Do not start new explorations."
                    ),
                }
            }

        return {}

    return {
        "PreToolUse": [HookMatcher(matcher=".*", hooks=[_check_budget])]
    }


# ─── Snapshot tip: nudge the writer to bank progress on a clean compile ──────

# Lean verify/build tools whose success means "the file compiles right now".
_VERIFY_TOOLS = {
    "mcp__lean_lsp__lean_verify",
    "mcp__lean_lsp__lean_diagnostic_messages",
    "mcp__lean_tools__verify_no_sorry",
    "mcp__lean_tools__show_file_state",
}

# Error signatures that mean the verify did NOT come back clean. Kept loose:
# a false negative just skips one tip, which is harmless.
_ERROR_MARKERS = ("error:", "❌", "failed", "does not compile", "unsolved goals")


def _response_text(tool_response: Any) -> str:
    """Best-effort flatten of a tool_response into searchable text."""
    if isinstance(tool_response, str):
        return tool_response
    if isinstance(tool_response, dict):
        content = tool_response.get("content")
        if isinstance(content, list):
            return "\n".join(
                str(c.get("text", "")) for c in content if isinstance(c, dict))
        return str(tool_response)
    if isinstance(tool_response, list):
        return "\n".join(
            str(c.get("text", "")) if isinstance(c, dict) else str(c)
            for c in tool_response)
    return str(tool_response)


def snapshot_tip_hooks(agent_ref=None, probability: float = 0.85) -> dict:
    """After a successful Lean verify, occasionally remind the writer to snapshot.

    Passive: emits `additionalContext` (no interrupt, no permission gate) so the
    tip enters the writer's context. Fires on PostToolUse for a verify/build tool
    when the response shows the file compiles, with the given probability on EACH
    such call (no cooldown state — matches _nudge.py's use of `random`). Only
    attached to agents that have the snapshots MCP server, so the tip always
    references an available tool.

    If `agent_ref` (the SwarmAgent) is provided, the tip is also surfaced as a
    visible "message" event so it shows up in the dashboard/transcript rather
    than only living inside the model's context.
    """

    _TIP = (
        "✓ Compiles. If this is a real high-water mark (a goal just closed, a "
        "key lemma landed, or the structure improved), bank it: "
        "snapshot_progress(tag=\"...\"). It's your safety net against a later "
        "regression. Skip it for routine intermediate states."
    )

    async def _tip(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PostToolUse":
            return {}
        tool_name = input_data.get("tool_name", "")
        if tool_name not in _VERIFY_TOOLS:
            return {}

        text = _response_text(input_data.get("tool_response")).lower()
        if any(m in text for m in _ERROR_MARKERS):
            return {}  # not a clean compile — nothing to bank

        if random.random() > probability:
            return {}

        logger.info("snapshot tip fired after %s", tool_name)
        if agent_ref is not None:
            try:
                await agent_ref._emit("message", f"[snapshot tip] {_TIP}")
            except Exception:
                pass
        return {
            "hookSpecificOutput": {
                "hookEventName": "PostToolUse",
                "additionalContext": _TIP,
            }
        }

    return {
        "PostToolUse": [HookMatcher(matcher=".*", hooks=[_tip])]
    }


# ─── run_code-without-edit nudge: keep the writer editing the FILE ────────────

# Tools that PROBE in a scratch/standalone context (do not change the real file).
_PROBE_TOOLS = {
    "mcp__lean_lsp__lean_run_code",
    "mcp__lean_lsp__lean_multi_attempt",
}
# Tools that actually MUTATE the file under proof.
_EDIT_TOOLS = {"Edit", "Write", "MultiEdit", "NotebookEdit"}


def run_code_nudge_hooks(agent_ref=None, threshold: int = 6) -> dict:
    """Nudge the writer back to the FILE when it probes with lean_run_code /
    lean_multi_attempt many times WITHOUT editing the file.

    WHY: lean_run_code runs a STANDALONE snippet (reconstructed imports/opens/
    elaboration order) and ships the whole snippet + full compiler output into the
    transcript, which is then re-billed as input tokens on every later turn — so a
    probe-heavy loop with no Edits inflates cost super-linearly AND risks divergence
    (a proof that "works" in run_code may not compile in place). The system prompt
    says to prefer editing; this is the RUNTIME reminder that fires when the behavior
    actually drifts, because a one-time prompt line is easy to forget mid-proof.

    Counts consecutive probe calls since the last file edit on `agent_ref`; once the
    count crosses `threshold`, emits `additionalContext` (passive, no interrupt)
    reminding the writer to commit to the file, then resets the counter so the nudge
    fires again only after another `threshold` probes-without-edit. An Edit/Write at
    any point resets the counter to 0."""

    ATTR = "_probe_since_edit"

    def _get() -> int:
        return getattr(agent_ref, ATTR, 0) if agent_ref is not None else 0

    def _set(n: int) -> None:
        if agent_ref is not None:
            setattr(agent_ref, ATTR, n)

    _NUDGE = (
        "⚠️ You've run several lean_run_code/lean_multi_attempt probes WITHOUT editing "
        "the file. run_code runs a STANDALONE snippet — its imports/opens/elaboration "
        "can differ from the real file, so a snippet that checks out may still not "
        "compile in place, and every probe bloats your context (re-billed each turn). "
        "STOP probing: apply your best current attempt to the file with Edit, then "
        "verify in place with lean_diagnostic_messages. Use run_code only for a quick "
        "single-tactic/lemma check, not to iterate the whole proof."
    )

    async def _nudge(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PostToolUse":
            return {}
        tool_name = input_data.get("tool_name", "")
        short = tool_name.rsplit("__", 1)[-1]
        # An edit resets the streak.
        if tool_name in _EDIT_TOOLS or short in _EDIT_TOOLS:
            _set(0)
            return {}
        if tool_name not in _PROBE_TOOLS:
            return {}
        n = _get() + 1
        if n < threshold:
            _set(n)
            return {}
        # Threshold crossed — nudge and reset so it re-arms for the next streak.
        _set(0)
        logger.info("run_code-without-edit nudge fired after %d probes", n)
        if agent_ref is not None:
            try:
                await agent_ref._emit("message", f"[edit-the-file nudge] {_NUDGE}")
            except Exception:
                pass
        return {
            "hookSpecificOutput": {
                "hookEventName": "PostToolUse",
                "additionalContext": _NUDGE,
            }
        }

    return {
        "PostToolUse": [HookMatcher(matcher=".*", hooks=[_nudge])]
    }


def writer_nudge_hooks(agent_ref=None) -> dict:
    """Combined PostToolUse hooks for the proof writer: the snapshot tip + the
    run_code-without-edit nudge, merged into one dict (both are PostToolUse, so
    their matcher lists are concatenated)."""
    combined: dict = {}
    for h in (snapshot_tip_hooks(agent_ref=agent_ref, probability=1.0),
              run_code_nudge_hooks(agent_ref=agent_ref)):
        for event, matchers in h.items():
            combined.setdefault(event, []).extend(matchers)
    return combined


# ─── SearchAgent: source-only, no Sandbox ────────────────────────────────────

SEARCH_AGENT_DENIED = ["StrataAgent/"]


def search_agent_hooks() -> dict:
    """SearchAgent can only access Strata/ and StrataTest/.

    Denies any tool call touching StrataAgent/ (which contains Sandbox,
    agent code, working files). This prevents cross-contamination where
    proof_writers at recursion level N see level N-1's decomposed files
    via SearchAgent.
    """

    async def enforce(tool_name, tool_input, rel_paths, cwd):
        for path in rel_paths:
            for prefix in SEARCH_AGENT_DENIED:
                if path.startswith(prefix):
                    return deny(path,
                        f"Access denied: '{path}' is in a restricted area. "
                        f"You can only search in Strata/ and StrataTest/.")
        return None

    return make_hook(enforce)


# ─── ProofResearcher: read anywhere, WRITE only into the reports dir ──────────

_RESEARCH_WRITE_TOOLS = ("Write", "Edit", "MultiEdit", "NotebookEdit")


def research_workspace_hooks(reports_dir: str) -> dict:
    """Asymmetric scope for the ProofResearcher.

    The researcher READS freely across the whole codebase (that is the point — it
    hunts proof patterns and counterexamples wherever they live). But it must NOT
    modify any proof file: its ONLY writable surface is the reports directory it
    dumps its findings into. So we deny Write/Edit/MultiEdit whose path is outside
    `reports_dir`, and leave every read/grep/glob untouched.

    Args:
        reports_dir: relative path (under the Sandbox) of the per-lemma reports
                     folder, e.g. "StrataAgent/Sandbox/decomposed/lemma_x/reports".
    """
    allowed_write = [f"{reports_dir}/**", reports_dir]

    async def enforce(tool_name, tool_input, rel_paths, cwd):
        if tool_name not in _RESEARCH_WRITE_TOOLS:
            return None  # reads / greps / globs / lean eval — unrestricted
        for path in rel_paths:
            if not matches_any(path, allowed_write):
                return deny(path,
                    f"'{path}' is outside your reports directory. You are a "
                    f"RESEARCHER — you do NOT edit proof files. Write your findings "
                    f"only under: {reports_dir}/")
        return None

    return make_hook(enforce)


# ─── Decomposer: redirect Write/Edit to write_decomposed_lemma ───────────────

def decomposer_hooks() -> dict:
    """Decomposer hint hook: if it tries Write or Edit, tell it to use
    write_decomposed_lemma instead.

    The CLI already blocks Write/Edit via disallowed_tools, but gives a
    generic error. This hook fires first and provides a helpful redirect.
    """

    async def _enforce(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PreToolUse":
            return {}

        tool_name = input_data.get("tool_name", "")

        if tool_name in ("Write", "Edit", "MultiEdit"):
            return {
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": (
                        "You cannot use Write/Edit directly. "
                        "To create decomposed lemma files, use the write_decomposed_lemma tool:\n"
                        "  write_decomposed_lemma(file_content=\"import ...\\n\\ntheorem name ... := by\\n  sorry\", "
                        "theorem_name=\"name\")\n"
                        "This tool validates your file (one theorem, name matches, compiles) "
                        "and creates it with the correct naming convention."
                    ),
                }
            }

        return {}

    return {
        "PreToolUse": [HookMatcher(matcher="Write|Edit|MultiEdit", hooks=[_enforce])]
    }


# ─── Workspace-scoped agents: can only access their workspace ────────────────

def workspace_hooks(workspace: str) -> dict:
    """Restrict an agent to only access files within its workspace.

    Used by proof_writer, decomposer, sketcher, refactoring_agent when
    spawned via swarm_agent(workspace=...).

    Args:
        workspace: Relative path to the workspace root.
                   e.g. "StrataAgent/Sandbox/decomposed/lemma_1"
    """
    allowed = [f"{workspace}/**"]

    async def enforce(tool_name, tool_input, rel_paths, cwd):
        for path in rel_paths:
            if not matches_any(path, allowed):
                return deny(path,
                    f"Path '{path}' is outside your workspace. "
                    f"You can only access files in: {workspace}/")
        return None

    return make_hook(enforce)


# ─── Recursive PO isolation: deny parent/sibling workspaces ──────────────────

def recursive_po_hooks(workspace: str, parent_workspaces: list[str] | None = None) -> dict:
    """Restrict a child PO to its own workspace, explicitly deny parent paths.

    Stronger than workspace_hooks: even if a parent path somehow appears
    in the allowed list, this denies it. Prevents DAG violations from
    child POs importing parent decomposed files.

    Args:
        workspace: This PO's workspace path.
        parent_workspaces: Parent workspace paths to explicitly deny.
    """
    allowed = [f"{workspace}/**"]
    denied = [f"{p}/**" for p in (parent_workspaces or [])]

    async def enforce(tool_name, tool_input, rel_paths, cwd):
        for path in rel_paths:
            if denied and matches_any(path, denied):
                return deny(path,
                    f"Path '{path}' belongs to a parent workspace. "
                    f"You can only access: {workspace}/")
            if not matches_any(path, allowed):
                return deny(path,
                    f"Path '{path}' is outside your workspace. "
                    f"You can only access: {workspace}/")
        return None

    return make_hook(enforce)
