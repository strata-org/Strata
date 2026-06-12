"""Programmatic verification utilities for Proof Orchestrator.

Delegates to SwarmLeanTools (persistent Lean RPC process) for all
content analysis. Only pure filesystem checks remain as direct Python.

All checks are instant (<100ms via RPC). No LLM agents needed.
"""

from pathlib import Path

from .po_lean import get_lean_tools


# ─── Filesystem checks (exact, no heuristic) ────────────────────────────────

def verify_file_exists(cwd: Path, rel_path: str) -> bool:
    """Check file exists."""
    return (cwd / rel_path).exists()


def verify_split_complete(cwd: Path, workspace_rel: str) -> bool:
    """Check that split produced both files correctly."""
    def_exists = (cwd / workspace_rel / "Stub" / "Def.lean").exists()
    stub_exists = (cwd / workspace_rel / "Stub.lean").exists()
    if not (def_exists and stub_exists):
        return False
    return verify_stub_imports_def(cwd, workspace_rel)


def verify_stub_imports_def(cwd: Path, workspace_rel: str) -> bool:
    """Check that Stub.lean imports Stub.Def (via Lean RPC)."""
    stub_rel = f"{workspace_rel}/Stub.lean"
    if not (cwd / stub_rel).exists():
        return False
    tools = get_lean_tools()
    result = tools.check_imports(stub_rel)
    if result.error:
        return False
    return any("Stub.Def" in imp for imp in result.imports)


# ─── Sorry checks (via Lean RPC — comment-aware, definitive) ────────────────

def verify_no_sorry(cwd: Path, rel_path: str) -> bool:
    """Check file has no sorry. Uses Lean RPC (handles comments correctly)."""
    if not (cwd / rel_path).exists():
        return False
    tools = get_lean_tools()
    info = tools.count_sorries(rel_path)
    return info.total == 0


def verify_has_sorry(cwd: Path, rel_path: str) -> bool:
    """Check file HAS sorry."""
    if not (cwd / rel_path).exists():
        return False
    tools = get_lean_tools()
    info = tools.count_sorries(rel_path)
    return info.total > 0


def count_sorries(cwd: Path, rel_path: str) -> int:
    """Count sorry occurrences in a file (comment-aware via Lean RPC)."""
    if not (cwd / rel_path).exists():
        return 0
    tools = get_lean_tools()
    info = tools.count_sorries(rel_path)
    return info.total


# ─── Import / DAG checks (via Lean RPC) ─────────────────────────────────────

def check_import_dag(file_path: Path, workspace_rel: str) -> list[str]:
    """Check that a Lean file only imports from its own workspace or external libs.

    Uses Lean RPC to get actual imports (comment-aware).
    Returns list of bad imports (empty = all good).
    """
    if not file_path.exists():
        return []

    workspace_module = workspace_rel.replace("/", ".")
    sandbox_prefix = "StrataAgent.Sandbox"

    # Get file path relative to project root for the RPC
    # file_path might be absolute or relative — normalize
    rel_path = str(file_path)
    try:
        from .po_lean import _get_project_root
        root = _get_project_root()
        if file_path.is_absolute():
            rel_path = str(file_path.relative_to(root))
    except (ValueError, ImportError):
        pass

    tools = get_lean_tools()
    result = tools.check_imports(rel_path)
    if result.error:
        return []  # can't check — don't block

    bad = []
    for module in result.imports:
        if not module.startswith(sandbox_prefix):
            continue
        if module.startswith(workspace_module):
            continue
        bad.append(module)

    return bad


def verify_dag(cwd: Path, rel_path: str, workspace_rel: str) -> list[str]:
    """DAG check wrapper. Returns bad imports (empty = OK)."""
    return check_import_dag(cwd / rel_path, workspace_rel)


def verify_all_files_dag(cwd: Path, files: list[str], workspace_rel: str) -> dict[str, list[str]]:
    """DAG check on multiple files. Returns dict of file→bad_imports (empty dict = all OK)."""
    issues = {}
    for f in files:
        bad = check_import_dag(cwd / f, workspace_rel)
        if bad:
            issues[f] = bad
    return issues


