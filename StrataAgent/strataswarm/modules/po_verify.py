"""Programmatic verification utilities for Proof Orchestrator.

All checks are instant (no LLM agents needed). Used to validate
file state at every stage transition.
"""

from pathlib import Path


def check_import_dag(file_path: Path, workspace_rel: str) -> list[str]:
    """Check that a Lean file only imports from:
    - Its own workspace subtree (e.g. StrataAgent.Sandbox.decomposed.lemma_2.*)
    - External project libraries (Strata.*, Mathlib.*, Init.*, etc.)

    With import isolation, each workspace is self-contained. A file should
    NEVER import from a parent or sibling workspace. The workspace's own
    Stub.Def is at `<workspace_module>.Stub.Def` — not any parent's.

    Returns list of bad imports (empty = all good).
    """
    if not file_path.exists():
        return []

    workspace_module = workspace_rel.replace("/", ".")
    sandbox_prefix = "StrataAgent.Sandbox"

    bad = []
    for line in file_path.read_text().splitlines():
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        module = stripped.removeprefix("import ").strip()

        # External imports (Strata.*, Mathlib.*, Init.*, etc.) — always OK
        if not module.startswith(sandbox_prefix):
            continue

        # Imports within our own workspace module — OK
        if module.startswith(workspace_module):
            continue

        # Anything else from Sandbox is a DAG violation
        bad.append(module)

    return bad


def verify_file_exists(cwd: Path, rel_path: str) -> bool:
    """Check file exists."""
    return (cwd / rel_path).exists()


def verify_no_sorry(cwd: Path, rel_path: str) -> bool:
    """Check file has no sorry (grep-based, instant)."""
    path = cwd / rel_path
    if not path.exists():
        return False
    return "sorry" not in path.read_text()


def verify_has_sorry(cwd: Path, rel_path: str) -> bool:
    """Check file HAS sorry (expected for stubs)."""
    path = cwd / rel_path
    if not path.exists():
        return False
    return "sorry" in path.read_text()


def count_sorries(cwd: Path, rel_path: str) -> int:
    """Count occurrences of sorry in a file (skips comments)."""
    path = cwd / rel_path
    if not path.exists():
        return 0
    content = path.read_text()
    count = 0
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("--"):
            continue
        count += stripped.split("--")[0].count("sorry")
    return count


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


def is_bare_sorry(cwd: Path, rel_path: str) -> bool:
    """Check if a file has no structural proof progress — just sorry.

    A file is "bare" if:
    - The only non-import, non-variable, non-comment content ends with := sorry or by sorry
    - OR the file has a very high sorry density (>5 sorries with <20 tactic lines)

    This means decomposition is needed — proof_writer can't make progress
    without a structural starting point.
    """
    path = cwd / rel_path
    if not path.exists():
        return True
    content = path.read_text()
    lines = content.splitlines()

    # Check for simple bare sorry patterns
    stripped = content.strip()
    if (stripped.endswith(":= by\n  sorry") or
            stripped.endswith("by\n  sorry") or
            stripped.endswith(":= sorry") or
            stripped.endswith("by sorry")):
        return True

    # Check sorry density: many sorries with very few tactic lines = no progress
    sorry_count = count_sorries(cwd, rel_path)
    tactic_lines = sum(1 for l in lines if l.strip().startswith((
        "cases", "induction", "apply", "exact", "simp", "rw",
        "have", "obtain", "intro", "match", "refine", "constructor",
        "unfold", "ext", "funext", "calc")))

    if sorry_count > 5 and tactic_lines < 5:
        return True

    return False


def verify_stub_imports_def(cwd: Path, workspace_rel: str) -> bool:
    """Check that Stub.lean imports Stub.Def."""
    stub = cwd / workspace_rel / "Stub.lean"
    if not stub.exists():
        return False
    content = stub.read_text()
    return any("Stub.Def" in line for line in content.splitlines() if line.strip().startswith("import"))


def verify_split_complete(cwd: Path, workspace_rel: str) -> bool:
    """Check that split produced both files correctly."""
    def_exists = (cwd / workspace_rel / "Stub" / "Def.lean").exists()
    stub_exists = (cwd / workspace_rel / "Stub.lean").exists()
    if not (def_exists and stub_exists):
        return False
    return verify_stub_imports_def(cwd, workspace_rel)
