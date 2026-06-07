"""Domain-specific hook policies for StrataSwarm agents.

Defines what each agent type can and cannot access. Loaded at runtime by
the swarm and swarm_agent helper.

Uses framework utilities from _workspace_hooks (path matching, extraction).
"""

from __future__ import annotations

from .._workspace_hooks import matches_any, deny, allow, make_hook


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
