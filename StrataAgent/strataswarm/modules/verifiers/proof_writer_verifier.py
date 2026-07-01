"""Verifier for proof_writer output.

Pure deterministic checks after proof_writer runs:
1. File compiles (sorry OK, real errors NOT OK)
2. No axiom keyword
3. Progress was made (file differs from original)
4. Main theorem structure is intact (theorem name still exists)

Does NOT diagnose WHY the writer is stuck — that's for goal_analyzer.
Does NOT suggest strategy — that's for proof_guide.

Usage:
    verify_fn = make_proof_writer_verifier(stub_rel, stub_clean_path, workspace)
    outcome = await verified_loop(
        agent_ctx=writer,
        initial_input="Prove this...",
        verify=verify_fn,
        max_rounds=3,
    )
"""

from __future__ import annotations

from pathlib import Path

from ..po_lean import get_lean_tools


def make_proof_writer_verifier(
    target_file: str,
    original_content: str,
    workspace: str,
    main_theorem: str = "",
    ancestor_modules: list[str] | None = None,
    ledger=None,
) -> callable:
    """Create a verify function for proof_writer's verified_loop.

    Args:
        target_file: Relative path to the file being proved
        original_content: Content of the file BEFORE proof_writer touched it
        workspace: Workspace relative path
        main_theorem: Name of the main theorem (optional, for structure check)
        ancestor_modules: Module paths of ancestors in the DAG. If the writer
            imports any of these, it's a circular dependency (not a real proof).
        ledger: LemmaLedger instance for dedup checks (optional).

    Returns:
        Callable that returns None (pass) or error string (fed back to writer).
    """

    def verify() -> str | None:
        tools = get_lean_tools()

        # 1. Must compile (sorry OK, errors NOT OK)
        cr = tools.check_compiles(target_file)
        if not cr.success:
            return (
                "COMPILATION ERROR: Your file does not compile. "
                "Fix the errors — the file must compile even with sorry. "
                "Run lean_verify to see the exact errors."
            )

        # 2. No axiom
        ax = tools.check_axioms(target_file)
        if ax.has_axiom:
            return (
                f"AXIOM DETECTED: Your file uses the `axiom` keyword ({ax.axiom_names}). "
                f"This is UNSOUND. Replace with `theorem ... := by sorry`."
            )

        # 3. No circular imports (importing an ancestor's Stub = delegating back, not proving)
        if ancestor_modules:
            # Build the exact module paths that would be circular:
            # importing an ancestor's Stub.lean (workspace.Stub) creates a real cycle
            circular_modules = set()
            for anc_mod in ancestor_modules:
                circular_modules.add(f"{anc_mod}.Stub")
            imports = tools.check_imports(target_file)
            if not imports.error:
                for imp in imports.imports:
                    if imp in circular_modules:
                        return (
                            f"CIRCULAR IMPORT: You imported '{imp}' which is an ancestor's Stub "
                            f"in the proof DAG. This creates a circular dependency. "
                            f"You MUST prove this theorem WITHOUT importing ancestor Stubs. "
                            f"Importing sibling/cousin lemmas from other branches is fine."
                        )

        # 3.5 Dedup: check new theorem/def names against ledger
        if ledger:
            import re as _re

            # Get current names from file
            split = tools.split_theorems(target_file)
            current_names = {b.name for b in split.blocks} if split and not split.error else set()

            # Get original names (regex — just need names, not full parse)
            original_names = set(_re.findall(
                r'(?:theorem|def|lemma)\s+(\S+)', original_content))

            # Check new names against ledger
            from ..lemma_ledger import LemmaStatus as _LS
            for name in current_names - original_names:
                if name == main_theorem:
                    continue
                results = ledger.search(name, page_size=5)
                for hit in results.hits:
                    if hit.entry.name == name:
                        if hit.entry.status in (_LS.FAILED, _LS.CYCLE):
                            stmt = hit.entry.statement[:300] if hit.entry.statement else ""
                            reason = hit.entry.failure_reason or (
                                f"Cycled back to ancestor '{hit.entry.cycle_ancestor_id[:8]}'"
                                if hit.entry.cycle_ancestor_id else "unknown")
                            label = "FAILED" if hit.entry.status == _LS.FAILED else "CYCLIC"
                            return (
                                f"RECREATING {label} LEMMA: '{name}' previously {label.lower()}.\n"
                                f"Reason: {reason[:200]}\n"
                                f"Statement: {stmt}\n\n"
                                f"Use a different approach or create another one with a different name. "
                                f"Make sure not to have the exact same body, because we failed last time."
                            )
                        if hit.entry.file_path != target_file:
                            import_module = hit.entry.file_path.replace("/", ".").removesuffix(".lean")
                            return (
                                f"POSSIBLE DUPLICATE: theorem '{name}' already exists in the ledger "
                                f"(module: {import_module}). If possible, import it with "
                                f"add_import_safely. Otherwise create another one with a different name."
                            )

        # 3.6 No private helpers with sorry (they can't be extracted/reused)
        if split and not split.error:
            for block in split.blocks:
                if block.name == main_theorem:
                    continue
                if block.has_sorry and "private " in block.text[:50]:
                    return (
                        f"PRIVATE SORRY: '{block.name}' is private and has sorry. "
                        f"Remove the `private` keyword — helpers with sorry will be "
                        f"extracted to separate files and must be public for reuse."
                    )

        # 3.7 Main theorem must be sorry-free (including termination_by/decreasing_by)
        # split_theorems extends block boundaries to include these clauses
        if split and not split.error and main_theorem:
            main_block = next((b for b in split.blocks if b.name == main_theorem), None)
            if main_block and main_block.has_sorry:
                # Find sorry lines in the main theorem's text to give specific feedback
                root = tools._root
                current_content = (root / target_file).read_text()
                file_lines = current_content.splitlines()
                sorry_context_lines = []
                for line_idx in range(main_block.start - 1, min(main_block.end, len(file_lines))):
                    if "sorry" in file_lines[line_idx]:
                        line_text = file_lines[line_idx].strip()
                        sorry_context_lines.append(f"  line {line_idx + 1}: {line_text}")

                context_str = "\n".join(sorry_context_lines[:5])
                if "decreasing_by" in "\n".join(sorry_context_lines):
                    return (
                        f"MAIN THEOREM HAS SORRY in termination proof:\n{context_str}\n\n"
                        f"Factor the termination obligation into a helper theorem:\n"
                        f"  theorem decreasing_helper (args...) : <size_condition> := by sorry\n"
                        f"Then use: `decreasing_by exact decreasing_helper ...`\n"
                        f"Or: restructure using fuel-based induction to avoid termination_by."
                    )
                else:
                    return (
                        f"MAIN THEOREM HAS SORRY:\n{context_str}\n\n"
                        f"The main theorem '{main_theorem}' must be sorry-free. "
                        f"Factor any sorry into a separate helper theorem above."
                    )

        # 4. Check if file is entirely sorry-free (success — fully proved!)
        root = tools._root
        current_content = (root / target_file).read_text()
        if "sorry" not in current_content:
            return None  # fully proved!

        # 5. Check progress was made (file changed from original)
        if current_content.strip() == original_content.strip():
            return (
                "NO PROGRESS: The file is unchanged from the original. "
                "You must write proof tactics to make progress. "
                "Use lean_goal to see what needs to be proved, "
                "ask SearchAgent for relevant lemmas, then write the proof."
            )

        # 6. Main theorem still exists (structure not broken)
        if main_theorem:
            split = tools.split_theorems(target_file)
            if not split.error:
                names = [b.name for b in split.blocks]
                if main_theorem not in names:
                    pass

        # File compiles, has sorry but made progress — acceptable for now
        # Report private count as info (not an error)
        if split and not split.error:
            private_count = sum(1 for b in split.blocks
                                if b.name != main_theorem and "private " in b.text[:50])
            if private_count > 3:
                return (
                    f"TOO MANY PRIVATE: You have {private_count} private helpers. "
                    f"Consider making them public (remove `private`) so they can be "
                    f"reused by other proof branches. Only use private for truly local utilities."
                )
        return None

    return verify
