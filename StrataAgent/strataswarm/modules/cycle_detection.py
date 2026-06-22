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
        extra_mcp_servers={"ledger": ledger_mcp},
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
    statements and give a proof_writer 10 turns to prove ours from ancestor.

    Uses verified_loop for the file_merger: merge → check compile → if error,
    feed error back to merger for retry.
    """
    from .po_lean import get_lean_tools
    from .po_agents import verified_loop
    import logging
    _vlog = logging.getLogger("strataswarm.cycle")
    tools = get_lean_tools()

    if not our_statement or not ancestor_statement:
        return False

    temp_path = str(Path(our_file).parent / "_cycle_check_temp.lean")
    (cwd / temp_path).parent.mkdir(parents=True, exist_ok=True)

    try:
        # Step 1: Build a compilable equivalence file via verified_loop on file_merger
        from .._helpers import swarm_agent

        def _verify_merge() -> str | None:
            """Check that the merged file compiles (sorry is OK)."""
            if not (cwd / temp_path).exists():
                return "File not written yet"
            cr = tools.check_compiles(temp_path)
            if not cr.success:
                return f"Merged file doesn't compile: check imports for conflicts"
            return None

        async with swarm_agent(
            "file_merger", swarm=agent.swarm, cwd=agent._cwd,
        ) as merger:
            outcome = await verified_loop(
                agent_ctx=merger,
                initial_input=(
                    f"Merge these two Lean 4 files into ONE compilable file.\n\n"
                    f"File A: {our_file}\n"
                    f"File B: {ancestor_file}\n\n"
                    f"Read both files. Produce ONE file at: {temp_path}\n"
                    f"It must contain:\n"
                    f"1. Merged imports (deduplicated — avoid importing both Stub.Def files if they conflict)\n"
                    f"2. Merged open/variable/namespace declarations\n"
                    f"3. These two theorem statements exactly:\n\n"
                    f"-- Theorem 1:\n{ancestor_statement}\n\n"
                    f"-- Theorem 2:\n{our_statement}\n\n"
                    f"Write the file. It must compile (sorry is fine)."
                ),
                verify=_verify_merge,
                max_rounds=3,
                max_turns=15,
                use_run_ai=False,
            )

        if not outcome.success:
            _vlog.info(f"  verify_ancestor: FAILED — merger couldn't produce compilable file")
            return False

        # Step 2: Extract variant name
        import re as _re
        variant_name_match = _re.match(
            r'(?:private\s+)?(?:noncomputable\s+)?(?:theorem|def|lemma)\s+(\S+)', our_statement.strip())
        variant_name = variant_name_match.group(1) if variant_name_match else ""

        # Step 3: Prove BOTH directions — true cycle means they're equivalent
        # Direction 1: prove variant from ancestor (ancestor has sorry, variant uses it)
        await _run_short_writer(
            agent, temp_path,
            f"This file has two theorems. The first (`{ancestor_name}`) has sorry. "
            f"Prove the SECOND theorem (`{variant_name}`) using the first. "
            f"Try: exact {ancestor_name}, apply {ancestor_name}, or simple rewrites. "
            f"You have 10 turns. Just close the second sorry."
        )

        cr = tools.check_compiles(temp_path)
        sorry_by_thm = tools.get_sorries_by_theorem(temp_path)
        direction1 = cr.success and variant_name not in sorry_by_thm
        _vlog.info(f"  verify_ancestor: direction1 (variant from ancestor) = {direction1}")

        if not direction1:
            return False

        # Direction 2: prove ancestor from variant (swap who has sorry)
        # Rewrite temp file: variant proved (remove sorry), ancestor gets sorry
        content = (cwd / temp_path).read_text()
        # The variant is now proved (direction 1 succeeded). Put sorry back on ancestor.
        # Actually we need a fresh file with roles reversed.
        temp_content_rev = await _build_equivalence_file(
            agent, ancestor_file, our_file, ancestor_statement, our_statement)
        if not temp_content_rev:
            _vlog.info(f"  verify_ancestor: couldn't build reverse file")
            return False

        (cwd / temp_path).write_text(temp_content_rev)
        cr = tools.check_compiles(temp_path)
        if not cr.success:
            _vlog.info(f"  verify_ancestor: reverse file doesn't compile — not a true cycle")
            return False

        await _run_short_writer(
            agent, temp_path,
            f"This file has two theorems. The first (`{variant_name}`) has sorry. "
            f"Prove the SECOND theorem (`{ancestor_name}`) using the first. "
            f"Try: exact {variant_name}, apply {variant_name}, or simple rewrites. "
            f"You have 10 turns. Just close the second sorry."
        )

        cr = tools.check_compiles(temp_path)
        sorry_by_thm = tools.get_sorries_by_theorem(temp_path)
        direction2 = cr.success and ancestor_name not in sorry_by_thm
        _vlog.info(f"  verify_ancestor: direction2 (ancestor from variant) = {direction2}")

        # True cycle only if BOTH directions work
        return direction1 and direction2
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


# ─── DAG consistency passes (called from UPDATE phase) ───────────────────────

def propagate_cycles(ledger) -> int:
    """Pass 2: For each CYCLE node, mark everything between it and its ancestor as CYCLE.

    If node C is CYCLE with ancestor A, and the path is A → B → ... → parent → C,
    then parent, ..., B all get marked CYCLE (they are part of the tainted decomposition chain).
    We don't mark A itself — A is the healthy ancestor that needs to be re-proved with induction.

    Returns number of newly marked nodes.
    """
    from .lemma_ledger import LemmaStatus
    marked = 0
    for entry in ledger.entries():
        if entry.status != LemmaStatus.CYCLE or not entry.cycle_ancestor_id:
            continue
        # Walk from this node's parent up to (but not including) the ancestor
        current_id = entry.parent_id
        while current_id and current_id != entry.cycle_ancestor_id:
            node = ledger.get(current_id)
            if not node:
                break
            if node.status not in (LemmaStatus.CYCLE, LemmaStatus.PROVED, LemmaStatus.PRUNED):
                node.status = LemmaStatus.CYCLE
                node.cycle_ancestor_id = entry.cycle_ancestor_id
                marked += 1
            current_id = node.parent_id
    return marked


def prune_siblings_of_dead(ledger, cwd: Path = None) -> int:
    """For each FAILED/CYCLE node, prune ALL children of its parent + re-activate parent.

    When one child fails, the parent's decomposition is broken — it needs
    a full re-decomposition. ALL children (including the failed one, and even
    proved ones from this batch) get pruned. The parent goes back to PENDING
    with its Stub.lean restored from clean backup.

    Proved siblings' work is NOT lost — their file_path still exists on disk.
    If the new decomposition produces the same lemma, cycle detection finds it
    via REUSE and short-circuits.

    Root is never pruned.

    Returns number of newly pruned nodes.
    """
    from .lemma_ledger import LemmaStatus
    import shutil

    pruned_count = 0
    parents_reactivated = set()

    for entry in ledger.entries():
        if entry.status not in (LemmaStatus.FAILED, LemmaStatus.CYCLE):
            continue
        if not entry.parent_id:
            continue
        if entry.parent_id in parents_reactivated:
            continue  # already handled this parent

        parent = ledger.get(entry.parent_id)
        if not parent or parent.status in (LemmaStatus.PROVED, LemmaStatus.PRUNED):
            continue

        if entry.status == LemmaStatus.FAILED:
            # FAILED: the writer's approach was wrong. Prune ALL children,
            # parent re-decomposes from scratch.
            for child_id in parent.children:
                child = ledger.get(child_id)
                if child and child.status != LemmaStatus.PRUNED:
                    pruned = ledger.prune_branch(child_id,
                        f"parent '{parent.name}' re-decomposing (child '{entry.name}' failed)")
                    pruned_count += len(pruned)

            # Re-activate parent with priority boost + restore clean Stub
            parent.status = LemmaStatus.PENDING
            parent.priority_boost = True
            parents_reactivated.add(parent.id)
            if cwd:
                clean = cwd / parent.workspace / "Stub.clean.lean"
                stub = cwd / parent.workspace / "Stub.lean"
                if clean.exists():
                    shutil.copy2(clean, stub)

        elif entry.status == LemmaStatus.CYCLE:
            # CYCLE: node X recreates ancestor A. The entire sub-graph under A
            # is from the same bad decomposition.
            # - Path A → X: mark as CYCLE (the tainted chain)
            # - Everything else under A: mark as PRUNED (collateral)
            # - A itself: back to PENDING (retry with induction)
            ancestor_id = entry.cycle_ancestor_id
            ancestor = ledger.get(ancestor_id) if ancestor_id else parent
            if not ancestor:
                ancestor = parent

            # Mark the path from entry up to ancestor as CYCLE
            path_ids = set()
            current_id = entry.id
            while current_id and current_id != ancestor.id:
                path_ids.add(current_id)
                node = ledger.get(current_id)
                if node and node.status not in (LemmaStatus.CYCLE,):
                    node.status = LemmaStatus.CYCLE
                    node.cycle_ancestor_id = ancestor.id
                current_id = node.parent_id if node else None

            # Prune everything else under ancestor (not on the path, not already pruned)
            def _prune_subtree_except_path(node_id):
                node = ledger.get(node_id)
                if not node:
                    return
                for child_id in node.children:
                    if child_id in path_ids:
                        _prune_subtree_except_path(child_id)
                    else:
                        child = ledger.get(child_id)
                        if child and child.status not in (LemmaStatus.PRUNED, LemmaStatus.CYCLE):
                            ledger.prune_branch(child_id,
                                f"cycle detected: '{entry.name}' → ancestor '{ancestor.name}'")
                            nonlocal pruned_count
                            pruned_count += 1

            _prune_subtree_except_path(ancestor.id)

            # Re-activate ancestor with priority boost
            if ancestor.id not in parents_reactivated:
                ancestor.status = LemmaStatus.PENDING
                ancestor.priority_boost = True
                parents_reactivated.add(ancestor.id)
                if cwd:
                    clean = cwd / ancestor.workspace / "Stub.clean.lean"
                    stub = cwd / ancestor.workspace / "Stub.lean"
                    if clean.exists():
                        shutil.copy2(clean, stub)

    return pruned_count


def _can_reach(ledger, from_id: str, target_id: str) -> bool:
    """BFS: can we reach target_id by walking DOWN (through children) from from_id?

    This checks if from_id is an ancestor of target_id in the full DAG
    (considering ALL parent-child edges, not just the primary parent_id chain).
    """
    if from_id == target_id:
        return True
    visited = set()
    queue = [from_id]
    while queue:
        current = queue.pop(0)
        if current in visited:
            continue
        visited.add(current)
        entry = ledger.get(current)
        if not entry:
            continue
        for child_id in entry.children:
            if child_id == target_id:
                return True
            if child_id not in visited:
                queue.append(child_id)
    return False


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


async def _build_equivalence_file(agent, our_file: str, ancestor_file: str,
                                   our_statement: str, ancestor_statement: str) -> str:
    """Use a file_merger agent to combine two files' preambles into one equivalence check file."""
    from .._helpers import swarm_agent

    @dataclass
    class MergedFile:
        content: str = ""

    async with swarm_agent(
        "file_merger",
        swarm=agent.swarm,
        cwd=agent._cwd,
    ) as merger:
        result = await merger.run_ai(
            inp=(
                f"Merge these two Lean 4 files into a single file.\n\n"
                f"File A: {our_file}\n"
                f"File B: {ancestor_file}\n\n"
                f"Read both files. Produce ONE file containing:\n"
                f"1. Merged imports (deduplicated)\n"
                f"2. Merged open/variable/namespace/set_option declarations (deduplicated)\n"
                f"3. These two theorem statements exactly as given:\n\n"
                f"-- Theorem 1:\n{ancestor_statement}\n\n"
                f"-- Theorem 2:\n{our_statement}\n\n"
                f"Output the full file content. It must compile (sorry is fine)."
            ),
            result_type=MergedFile,
            max_turns=10,
        )

    if result.output and result.output.content:
        return result.output.content
    return ""




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
        import logging
        logging.getLogger("strataswarm.cycle").warning("check_soft returned empty matches")
        return DetectionResult(match_type=MatchType.NO_MATCH)

    # 3. Hard: verify each match (strategy depends on status + ancestry)
    # Use full BFS to determine if adding new node under parent_id would create
    # a cycle with the matched entry (checks ALL edges, not just parent_id chain)
    import logging
    _log = logging.getLogger("strataswarm.cycle")
    _log.info(f"check_soft returned {len(matches)} matches: {[m.get('entry_id','?')[:8] for m in matches]}")

    for m in matches:
        entry_id = m["entry_id"]
        match_entry = ledger.get(entry_id)
        if not match_entry:
            _log.warning(f"  match entry_id={entry_id[:8]} not found in ledger")
            continue
        match_name = match_entry.name
        match_file = match_entry.file_path
        match_status = match_entry.status.value

        # BFS: can we reach parent_id by walking DOWN from match_entry?
        # If yes → the match is an ancestor of our new node → adding would create cycle
        is_ancestor = _can_reach(ledger, entry_id, parent_id)
        _log.info(f"  match: {match_name} (id={entry_id[:8]}, status={match_status}, is_ancestor={is_ancestor})")

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
