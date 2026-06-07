"""Framework-level hook utilities for workspace permission enforcement.

Provides building blocks for domain modules to construct PreToolUse hooks.
Domain-specific policies live in modules/hooks.py, not here.

Key insight: the CLI resolves paths to ABSOLUTE before calling hooks, so we
strip the cwd prefix before matching against workspace-relative patterns.
"""

from __future__ import annotations

import re
from typing import Any

from claude_agent_sdk.types import HookMatcher

# Tools that never touch the filesystem — always allowed
_PASSTHROUGH_TOOLS = frozenset([
    "StructuredOutput",
    "mcp__agent_messaging__send_message",
    "mcp__agent_messaging__check_messages",
    "mcp__agent_messaging__get_time",
    "mcp__agent_directory__list_agents",
    "mcp__agent_spawn__sleep",
    "mcp__agent_spawn__my_workspace",
    "mcp__agent_spawn__done",
])


def matches_any(path: str, patterns: list[str]) -> bool:
    """Check if a path matches any glob-like pattern.

    Supports:
    - 'prefix/**' — matches prefix and all descendants
    - '*' within a segment — single-segment wildcard
    - Exact prefix matching (no glob)
    """
    path = path.strip("/")

    for pattern in patterns:
        pattern = pattern.strip("/")

        if pattern.endswith("/**"):
            prefix = pattern[:-3]
            if path == prefix or path.startswith(prefix + "/"):
                return True
        elif "*" in pattern:
            regex = re.escape(pattern).replace(r"\*\*", ".*").replace(r"\*", "[^/]*")
            if re.match(regex + "$", path):
                return True
        else:
            if path == pattern or path.startswith(pattern + "/"):
                return True

    return False


def to_relative(path: str, cwd: str) -> str:
    """Convert absolute path to cwd-relative."""
    path = path.rstrip("/")
    cwd = cwd.rstrip("/")
    if path.startswith(cwd + "/"):
        return path[len(cwd) + 1:]
    return path


def extract_paths(tool_name: str, tool_input: dict[str, Any]) -> list[str]:
    """Extract file/directory paths from a tool call's input."""
    paths = []

    if tool_name in ("Read", "Write", "Edit", "MultiEdit"):
        fp = tool_input.get("file_path", "")
        if fp:
            paths.append(fp)

    elif tool_name == "Grep":
        p = tool_input.get("path", "")
        if p:
            paths.append(p)
        inc = tool_input.get("include", "")
        if inc and "/" in inc:
            paths.append(inc)

    elif tool_name == "Glob":
        p = tool_input.get("pattern", "")
        if p:
            paths.append(p)

    elif tool_name == "Bash":
        cmd = tool_input.get("command", "")
        if cmd:
            paths.extend(_extract_paths_from_bash(cmd))

    elif tool_name.startswith("mcp__lean_lsp__"):
        for key in ("file_path", "filePath", "path", "file"):
            v = tool_input.get(key, "")
            if v:
                paths.append(v)

    return paths


def deny(path: str, reason: str) -> dict[str, Any]:
    """Build a PreToolUse deny response."""
    return {
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }
    }


def allow() -> dict[str, Any]:
    """Build an allow (pass-through) response."""
    return {}


def is_passthrough(tool_name: str) -> bool:
    """True if tool never touches filesystem and should always be allowed."""
    return tool_name in _PASSTHROUGH_TOOLS


def make_hook(enforce_fn) -> dict[str, list[HookMatcher]]:
    """Wrap an enforcement function into a hooks dict for ClaudeAgentOptions.

    The enforce_fn signature must be:
        async def enforce(tool_name, tool_input, rel_paths, cwd) -> dict | None
    Return a deny() dict to block, or None/allow() to pass.
    """

    async def _hook(input_data, tool_use_id, context):
        if not isinstance(input_data, dict):
            return {}
        if input_data.get("hook_event_name") != "PreToolUse":
            return {}

        tool_name = input_data.get("tool_name", "")
        if is_passthrough(tool_name):
            return {}

        tool_input = input_data.get("tool_input", {})
        cwd = input_data.get("cwd", "")

        raw_paths = extract_paths(tool_name, tool_input)
        rel_paths = [to_relative(p, cwd) for p in raw_paths]

        result = await enforce_fn(tool_name, tool_input, rel_paths, cwd)
        return result if result else {}

    return {
        "PreToolUse": [HookMatcher(matcher=None, hooks=[_hook])]
    }


def _extract_paths_from_bash(command: str) -> list[str]:
    """Extract path-like tokens from a bash command."""
    paths = []
    tokens = command.split()
    for token in tokens:
        if token.startswith("-"):
            continue
        if token in ("|", "&&", "||", ";", ">", ">>", "<", "2>&1"):
            continue
        if "/" in token or token.startswith("."):
            clean = token.strip("'\"")
            paths.append(clean)
    return paths
