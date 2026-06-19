"""Cycle detection library for the Lemma Ledger.

Three layers:
- Fast: signature hash comparison against ancestry (mechanical)
- Soft: agent with ledger MCP searches for similar lemmas (returns matches with status)
- Hard: Lean verification (different strategy depending on match status + ancestry)

Hard verification cases:
- Match is PROVED → try to close our lemma using it (import + apply/exact, 4 attempts)
- Match is PENDING/PROVING (not ancestor) → try to prove IT using OUR lemma, then add_parent
- Match is ANCESTOR → can't import (would be circular), create temp file with both
  statements and prove child from ancestor → confirms cycle → prune
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any


class MatchType(str, Enum):
    NO_MATCH = "no_match"
    REUSE = "reuse"       # proved match → close our lemma with import
    SHARED = "shared"     # pending match → prove it from us, add parent-child edge
    CYCLE = "cycle"       # ancestor match → prune


@dataclass
class DetectionResult:
    match_type: MatchType
    matched_id: str = ""
    matched_name: str = ""
    reason: str = ""
    import_path: str = ""


@dataclass
class SoftResult:
    """Structured output from the cycle_checker agent."""
    matches: list[dict] = field(default_factory=list)
    # Each dict: {entry_id, name, file_path, status, reason}


# ─── Fast: Hash-based ancestry check ────────────────────────────────────────

def check_fast(ledger, signature_hash: str, parent_id: str) -> DetectionResult | None:
    """Hash match against ancestors. Returns CYCLE result or None."""
    if ledger.check_cycle(signature_hash, parent_id):
        ancestor = ledger.get_cycle_ancestor(signature_hash, parent_id)
        if ancestor:
            return DetectionResult(
                match_type=MatchType.CYCLE,
                matched_id=ancestor.id,
                matched_name=ancestor.name,
                reason=f"Exact signature hash match with ancestor '{ancestor.name}'",
            )
    return None


# ─── Soft: Agent searches the ledger ────────────────────────────────────────

async def check_soft(agent, file_path: str, ledger) -> list[dict]:
    """Spawn a stateless agent to search the ledger for similar lemmas.

    Returns list of dicts: {entry_id, name, file_path, status, reason}
    """
    from .._helpers import swarm_agent
    from .._ledger_mcp import create_ledger_mcp_server

    ledger_mcp = create_ledger_mcp_server(ledger)

    async with swarm_agent(
        "cycle_checker",
        swarm=agent.swarm,
        cwd=agent._cwd,
        mcp_servers_override={"ledger": ledger_mcp},
    ) as checker:
        result = await checker.run_ai(
            inp=(
                f"Find lemmas in the ledger that are equivalent to the theorem in: {file_path}\n"
                f"Read the file, then search the ledger. "
                f"For each match, include its entry_id, name, file_path, status, and why you think it's equivalent."
            ),
            result_type=SoftResult,
            max_turns=30,
        )

    if not result.output or not result.output.matches:
        return []

    # Validate entries exist
    valid = []
    for m in result.output.matches:
        entry = ledger.get(m.get("entry_id", ""))
        if entry:
            m["file_path"] = entry.file_path
            m["status"] = entry.status.value
            valid.append(m)
    return valid


# ─── Hard: Lean verification (depends on match status + ancestry) ────────────

async def verify_proved_match(agent, cwd: Path, our_file: str, proved_file: str, proved_name: str) -> bool:
    """Match is PROVED: give a proof_writer 5 turns to close our sorry using it."""
    from .po_lean import get_lean_tools
    tools = get_lean_tools()

    original = (cwd / our_file).read_text()
    if "sorry" not in original:
        return False

    try:
        # Add the import if not already there
        proved_import = proved_file.replace("/", ".").removesuffix(".lean")
        if f"import {proved_import}" not in original:
            (cwd / our_file).write_text(f"import {proved_import}\n{original}")

        success = await _run_short_writer(
            agent, our_file,
            f"Prove this theorem using `{proved_name}` (already imported). "
            f"Try: exact {proved_name}, apply {proved_name}, or simple rewrites + exact. "
            f"You have 5 turns. Just close the sorry."
        )
        if success and tools.check_compiles(our_file).success and not tools.has_sorry(our_file):
            return True
        return False
    finally:
        if not (tools.check_compiles(our_file).success and not tools.has_sorry(our_file)):
            (cwd / our_file).write_text(original)


async def verify_pending_match(agent, cwd: Path, their_file: str, our_file: str, our_name: str) -> bool:
    """Match is PENDING: give a proof_writer 5 turns to prove THEIR sorry using our lemma."""
    from .po_lean import get_lean_tools
    tools = get_lean_tools()

    original = (cwd / their_file).read_text()
    if "sorry" not in original:
        return False

    try:
        our_import = our_file.replace("/", ".").removesuffix(".lean")
        if f"import {our_import}" not in original:
            (cwd / their_file).write_text(f"import {our_import}\n{original}")

        success = await _run_short_writer(
            agent, their_file,
            f"Prove this theorem using `{our_name}` (already imported). "
            f"Try: exact {our_name}, apply {our_name}, or simple rewrites + exact. "
            f"You have 5 turns. Just close the sorry."
        )
        if success and tools.check_compiles(their_file).success and not tools.has_sorry(their_file):
            return True
        return False
    finally:
        if not (tools.check_compiles(their_file).success and not tools.has_sorry(their_file)):
            (cwd / their_file).write_text(original)


async def verify_ancestor_match(
    agent, cwd: Path, our_file: str, our_statement: str,
    ancestor_file: str, ancestor_statement: str, ancestor_name: str,
) -> bool:
    """Match is ANCESTOR: can't import (circular). Create temp file with both
    statements and give a proof_writer 5 turns to prove ours from ancestor.
    """
    from .po_lean import get_lean_tools
    tools = get_lean_tools()

    if not our_statement or not ancestor_statement:
        return False

    imports = _merge_imports(our_file, ancestor_file)
    temp_content = "\n".join(f"import {imp}" for imp in imports) + "\n\n"
    temp_content += ancestor_statement + "\n\n"
    temp_content += our_statement

    temp_path = str(Path(our_file).parent / "_cycle_check_temp.lean")
    (cwd / temp_path).parent.mkdir(parents=True, exist_ok=True)

    try:
        (cwd / temp_path).write_text(temp_content)

        # Extract the variant theorem name from its statement
        import re as _re
        variant_name_match = _re.match(
            r'(?:private\s+)?(?:noncomputable\s+)?(?:theorem|def|lemma)\s+(\S+)', our_statement.strip())
        variant_name = variant_name_match.group(1) if variant_name_match else ""

        success = await _run_short_writer(
            agent, temp_path,
            f"This file has two theorems. The first (`{ancestor_name}`) has sorry. "
            f"Prove the SECOND theorem (`{variant_name}`) using the first. "
            f"Try: exact {ancestor_name}, apply {ancestor_name}, or simple rewrites. "
            f"You have 5 turns. Just close the second sorry."
        )

        # Check: file compiles AND the variant theorem specifically has no sorry
        # (ancestor is allowed to keep sorry — it's the "given")
        if not success or not tools.check_compiles(temp_path).success:
            return False
        sorry_by_thm = tools.get_sorries_by_theorem(temp_path)
        return variant_name not in sorry_by_thm
    finally:
        (cwd / temp_path).unlink(missing_ok=True)


async def _run_short_writer(agent, file_path: str, instruction: str) -> bool:
    """Spawn a stateless proof_writer with 5 turns to close a sorry."""
    from .._helpers import swarm_agent

    async with swarm_agent(
        "proof_writer_v2",
        swarm=agent.swarm,
        cwd=agent._cwd,
        workspace=str(Path(file_path).parent),
        can_see=["SearchAgent"],
    ) as writer:
        await writer.run_ai(
            inp=f"FILE: {file_path}\n\n{instruction}",
            max_turns=10,
        )

    return True  # caller checks compilation


def _get_statement(file_path: str) -> str:
    """Get the theorem statement from a file using split_theorems (precise, itp-interface)."""
    from .po_lean import get_lean_tools
    tools = get_lean_tools()
    split = tools.split_theorems(file_path)
    if split.blocks:
        return split.blocks[0].text
    return ""


def _get_imports(file_path: str) -> list[str]:
    """Get all import statements from a file using check_imports."""
    from .po_lean import get_lean_tools
    tools = get_lean_tools()
    result = tools.check_imports(file_path)
    return result.imports if not result.error else []


def _merge_imports(*file_paths: str) -> list[str]:
    """Get deduplicated, sorted union of imports from multiple files."""
    all_imports = set()
    for fp in file_paths:
        all_imports.update(_get_imports(fp))
    return sorted(all_imports)




# ─── Full pipeline ───────────────────────────────────────────────────────────

async def detect(
    agent, ledger, name: str, file_path: str,
    signature_hash: str, parent_id: str, cwd: Path,
) -> DetectionResult:
    """Run detection: fast → soft → hard (strategy depends on match status).

    Returns:
    - NO_MATCH: nothing found, register as pending
    - REUSE: proved match can close our lemma → add import
    - SHARED: pending match proved from us → add parent-child edge
    - CYCLE: ancestor match confirmed → prune
    """

    # 1. Fast hash check
    fast = check_fast(ledger, signature_hash, parent_id)
    if fast:
        return fast

    # 2. Soft: agent searches ledger
    matches = await check_soft(agent, file_path, ledger)
    if not matches:
        return DetectionResult(match_type=MatchType.NO_MATCH)

    # 3. Hard: verify each match (strategy depends on status + ancestry)
    ancestry_ids = set(ledger.get_ancestry(parent_id))
    ancestry_ids.add(parent_id)

    for m in matches:
        entry_id = m["entry_id"]
        match_entry = ledger.get(entry_id)
        if not match_entry:
            continue
        match_name = match_entry.name
        match_file = match_entry.file_path
        match_status = match_entry.status.value
        is_ancestor = entry_id in ancestry_ids

        if is_ancestor:
            # Can't import ancestor (circular). Use temp file with both statements.
            our_statement = _get_statement(file_path)
            if await verify_ancestor_match(agent, cwd, file_path, our_statement, match_file, match_entry.statement, match_name):
                return DetectionResult(
                    match_type=MatchType.CYCLE,
                    matched_id=entry_id,
                    matched_name=match_name,
                    reason=f"Lean confirms: '{name}' provable from ancestor '{match_name}' (cycle)",
                )

        elif match_status == "proved":
            # Already proved: give writer 5 turns to close our sorry using it
            if await verify_proved_match(agent, cwd, file_path, match_file, match_name):
                import_path = match_file.replace("/", ".").removesuffix(".lean")
                return DetectionResult(
                    match_type=MatchType.REUSE,
                    matched_id=entry_id,
                    matched_name=match_name,
                    reason=f"Proved lemma '{match_name}' closes our sorry",
                    import_path=import_path,
                )

        else:
            # Pending/proving: give writer 5 turns to prove THEIR sorry using our lemma
            if await verify_pending_match(agent, cwd, match_file, file_path, name):
                return DetectionResult(
                    match_type=MatchType.SHARED,
                    matched_id=entry_id,
                    matched_name=match_name,
                    reason=f"Our '{name}' can prove pending '{match_name}' → shared dependency",
                    import_path=file_path.replace("/", ".").removesuffix(".lean"),
                )

    return DetectionResult(match_type=MatchType.NO_MATCH)
