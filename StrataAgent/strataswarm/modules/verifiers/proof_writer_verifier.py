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
) -> callable:
    """Create a verify function for proof_writer's verified_loop.

    Args:
        target_file: Relative path to the file being proved
        original_content: Content of the file BEFORE proof_writer touched it
        workspace: Workspace relative path
        main_theorem: Name of the main theorem (optional, for structure check)

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

        # 3. Check if sorry-free (success!)
        if not tools.has_sorry(target_file):
            return None  # fully proved!

        # 4. Check progress was made (file changed from original)
        root = tools._root
        current_content = (root / target_file).read_text()
        if current_content.strip() == original_content.strip():
            return (
                "NO PROGRESS: The file is unchanged from the original. "
                "You must write proof tactics to make progress. "
                "Use lean_goal to see what needs to be proved, "
                "ask SearchAgent for relevant lemmas, then write the proof."
            )

        # 5. Main theorem still exists (structure not broken)
        if main_theorem:
            split = tools.split_theorems(target_file)
            if not split.error:
                names = [b.name for b in split.blocks]
                if main_theorem not in names:
                    return (
                        f"STRUCTURE ERROR: The main theorem '{main_theorem}' "
                        f"is no longer in the file. You may have accidentally "
                        f"deleted or renamed it. Current theorems: {names}"
                    )

        # File compiles, has sorry but made progress — acceptable for now
        # (the PO will handle extraction of remaining sorries)
        return None

    return verify
