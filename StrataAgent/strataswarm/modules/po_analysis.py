"""PO Analysis: difficulty assessment + refactoring logic.

Uses SwarmLeanTools for definitive file analysis (theorem listing,
sorry counting, dependency tracking). Falls back to text heuristics
only for patterns the RPC doesn't cover (branch analysis, tactic counting).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .po_verify import verify_no_sorry, count_sorries
from .po_lean import get_lean_tools

WRITER_MAX_TURNS = 50
WRITER_EXTENDED_TURNS = 80


@dataclass
class DifficultyAssessment:
    """Per-file difficulty classification."""
    file: str = ""
    difficulty: str = "direct"  # "direct" | "recursive" | "proved"
    reason: str = ""
    estimated_turns: int = 50


def analyze_files(files: list[str], cwd: Path) -> list[DifficultyAssessment]:
    """Classify each file as direct/recursive/proved.

    Uses Lean RPC for:
    - Sorry count (definitive)
    - Theorem block listing (split_theorems_)
    - Dependency analysis (thm_depends_on_)

    Falls back to text heuristics for:
    - Branch analysis (single sorry in case branch)
    - Tactic line counting
    """
    tools = get_lean_tools()
    results = []

    for f in files:
        if verify_no_sorry(cwd, f):
            results.append(DifficultyAssessment(file=f, difficulty="proved"))
            continue

        path = cwd / f
        if not path.exists():
            continue

        sorry_count = count_sorries(cwd, f)
        content = path.read_text()
        lines = content.splitlines()
        line_count = len(lines)

        # ── Use Lean RPC: get theorem blocks ──
        split = tools.split_theorems(f)
        sorry_blocks = [b for b in split.blocks if b.has_sorry] if not split.error else []
        total_blocks = len(split.blocks) if not split.error else 0

        # Very short file with single sorry → needs decomposition
        if sorry_count == 1 and line_count <= 10:
            results.append(DifficultyAssessment(
                file=f, difficulty="recursive",
                reason="single sorry, very short file — needs decomposition"))
            continue

        # Multiple sorry theorems in one file → needs refactoring (recursive)
        if len(sorry_blocks) > 1:
            if line_count <= 80 and sorry_count <= 3:
                results.append(DifficultyAssessment(
                    file=f, difficulty="direct",
                    reason=f"{len(sorry_blocks)} sorry theorems but small file — direct attempt",
                    estimated_turns=WRITER_EXTENDED_TURNS))
            else:
                results.append(DifficultyAssessment(
                    file=f, difficulty="recursive",
                    reason=f"{len(sorry_blocks)} sorry theorems in {line_count} lines — needs refactoring"))
            continue

        # ── Use Lean RPC: check mutual dependencies ──
        if total_blocks >= 2 and sorry_count >= 2:
            # Check if theorems reference each other (mutual induction)
            has_mutual = _check_mutual_deps(f, split.blocks, tools)
            if has_mutual:
                results.append(DifficultyAssessment(
                    file=f, difficulty="recursive",
                    reason="mutual induction pattern — needs specialized decomposition"))
                continue

        # ── Text heuristic: single branch sorry ──
        if _is_single_branch_sorry(content):
            results.append(DifficultyAssessment(
                file=f, difficulty="direct",
                reason="single sorry in one case branch — proof mostly complete",
                estimated_turns=WRITER_EXTENDED_TURNS))
            continue

        # ── Text heuristic: tactic line count ──
        tactic_lines = _count_tactic_lines(lines)
        has_structure = tactic_lines >= 3

        if sorry_count <= 2 and has_structure:
            results.append(DifficultyAssessment(
                file=f, difficulty="direct",
                reason=f"{sorry_count} sorries with structural proof ({tactic_lines} tactic lines)",
                estimated_turns=WRITER_EXTENDED_TURNS))
        elif sorry_count <= 3:
            results.append(DifficultyAssessment(
                file=f, difficulty="direct",
                reason=f"{sorry_count} sorries — attempt feasible",
                estimated_turns=WRITER_MAX_TURNS))
        elif sorry_count <= 5 and has_structure:
            results.append(DifficultyAssessment(
                file=f, difficulty="direct",
                reason=f"{sorry_count} sorries but structural proof — one direct shot",
                estimated_turns=WRITER_MAX_TURNS))
        else:
            results.append(DifficultyAssessment(
                file=f, difficulty="recursive",
                reason=f"{sorry_count} sorries, {line_count} lines — needs decomposition"))

    return results


def refactor_multi_theorem_files(decomposed_dir: Path, workspace: str,
                                  proved_files: list[str]) -> list[str]:
    """Extract sorry theorems from multi-theorem files into individual files.

    Uses SwarmLeanTools.extract_sorry_theorems (which internally uses
    split_theorems_ RPC for precise block boundaries).

    Returns list of newly created file paths (relative to cwd).
    """
    tools = get_lean_tools()
    new_files = []

    for lean_file in list(decomposed_dir.glob("*.lean")):
        rel_path = f"{workspace}/decomposed/{lean_file.name}"
        if rel_path in proved_files:
            continue
        if tools.is_proved(rel_path):
            continue

        result = tools.extract_sorry_theorems(rel_path,
            output_dir=f"{workspace}/decomposed")
        if result.created_files:
            new_files.extend(result.created_files)

    return new_files


# ─── Internal helpers ────────────────────────────────────────────────────────

def _check_mutual_deps(file: str, blocks, tools) -> bool:
    """Check if theorems in a file reference each other (mutual induction)."""
    names = [b.name for b in blocks]
    if len(names) < 2:
        return False

    for name in names:
        result = tools._send("thm_depends_on_", f"{file}:{name}")
        if "error" in result:
            continue
        uses = result.get("uses", [])
        # If this theorem uses another theorem from the same file → mutual
        for used in uses:
            if used in names and used != name:
                return True
    return False


def _is_single_branch_sorry(content: str) -> bool:
    """Detect: case analysis with one sorry branch, rest filled."""
    lines = content.splitlines()
    sorry_branches = 0
    total_branches = 0
    in_cases = False

    for line in lines:
        stripped = line.strip()
        if stripped.startswith(("| ", "case ")):
            total_branches += 1
            in_cases = True
            if "sorry" in stripped:
                sorry_branches += 1
        elif stripped == "sorry" and in_cases:
            sorry_branches += 1

    return total_branches >= 3 and sorry_branches == 1


def _count_tactic_lines(lines: list[str]) -> int:
    """Count lines that start with known tactic keywords."""
    tactic_keywords = (
        "cases", "induction", "apply", "exact", "simp", "rw",
        "have", "obtain", "intro", "match", "refine", "constructor",
        "unfold", "ext", "funext", "calc", "· ", "omega", "decide",
    )
    return sum(1 for l in lines if l.strip().startswith(tactic_keywords))
