"""PO Analysis: difficulty assessment + refactoring logic.

Determines which files need direct attempts vs recursive decomposition,
and handles extracting sorry theorems into individual files.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from .po_verify import verify_no_sorry, count_sorries, is_bare_sorry
from .po_util import find_sorry_theorems, extract_imports

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

    Heuristics:
    1. No sorry → "proved"
    2. Bare sorry (no structure) → "recursive"
    3. Multiple sorry theorems in large file → "recursive" (needs refactoring)
    4. Mutual induction pattern → "recursive"
    5. Single sorry in case branch of complete proof → "direct" (extended)
    6. ≤2 sorries with structural proof → "direct" (extended)
    7. ≤3 sorries → "direct" (normal turns)
    8. ≤5 sorries with structure → "direct" (one shot)
    9. >5 sorries → "recursive"
    """
    results = []

    for f in files:
        if verify_no_sorry(cwd, f):
            results.append(DifficultyAssessment(file=f, difficulty="proved"))
            continue

        path = cwd / f
        if not path.exists():
            continue

        content = path.read_text()
        lines = content.splitlines()
        sorry_count = count_sorries(cwd, f)
        line_count = len(lines)

        if is_bare_sorry(cwd, f):
            results.append(DifficultyAssessment(
                file=f, difficulty="recursive",
                reason="bare sorry — no structure, needs decomposition"))
            continue

        sorry_theorems = find_sorry_theorems(path)
        if len(sorry_theorems) > 1:
            if line_count <= 80 and sorry_count <= 3:
                results.append(DifficultyAssessment(
                    file=f, difficulty="direct",
                    reason=f"{len(sorry_theorems)} sorry theorems but small file — direct attempt",
                    estimated_turns=WRITER_EXTENDED_TURNS))
            else:
                results.append(DifficultyAssessment(
                    file=f, difficulty="recursive",
                    reason=f"{len(sorry_theorems)} sorry theorems in {line_count} lines — needs refactoring"))
            continue

        # Single sorry theorem
        if _has_mutual_references(content) and sorry_count >= 2:
            results.append(DifficultyAssessment(
                file=f, difficulty="recursive",
                reason="mutual induction pattern — needs specialized decomposition"))
            continue

        if _is_single_branch_sorry(content):
            results.append(DifficultyAssessment(
                file=f, difficulty="direct",
                reason="single sorry in one case branch — proof mostly complete",
                estimated_turns=WRITER_EXTENDED_TURNS))
            continue

        tactic_lines = sum(1 for l in lines if l.strip().startswith((
            "cases", "induction", "apply", "exact", "simp", "rw",
            "have", "obtain", "intro", "match", "refine")))
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

    Returns list of newly created file paths (relative to cwd).
    """
    new_files = []

    for lean_file in list(decomposed_dir.glob("*.lean")):
        rel_path = f"{workspace}/decomposed/{lean_file.name}"
        if rel_path in proved_files:
            continue
        if verify_no_sorry(decomposed_dir.parent.parent, rel_path):
            continue

        sorry_theorems = find_sorry_theorems(lean_file)
        if len(sorry_theorems) <= 1:
            continue

        content = lean_file.read_text()
        parent_stem = lean_file.stem
        imports_section = extract_imports(content)

        # Extract all but the last sorry theorem (keep one in the original)
        for i, (thm_name, thm_block) in enumerate(sorry_theorems[:-1]):
            new_name = f"helper_{parent_stem}_{i}_{thm_name[:30]}.lean"
            new_path = decomposed_dir / new_name
            new_rel = f"{workspace}/decomposed/{new_name}"

            new_content = imports_section + "\n\n" + thm_block + "\n"
            new_path.write_text(new_content)
            new_files.append(new_rel)

            content = content.replace(thm_block,
                f"-- Extracted to {new_name}")

        lean_file.write_text(content)

    return new_files


# ─── Internal heuristics ─────────────────────────────────────────────────────

def _has_mutual_references(content: str) -> bool:
    """Detect mutual induction: theorem A references theorem B and vice versa."""
    theorem_names = re.findall(r'(?:private\s+)?theorem\s+(\w+)', content)
    if len(theorem_names) < 2:
        return False

    cross_refs = 0
    for name in theorem_names:
        uses = content.count(name) - 1
        if uses > 0:
            cross_refs += 1
    return cross_refs >= 2


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
