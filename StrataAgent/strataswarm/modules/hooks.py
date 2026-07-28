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
