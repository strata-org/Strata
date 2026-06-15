"""Verifier for lemma_extractor agent output.

After lemma_extractor runs, this verifier checks:
1. Target file still compiles
2. Main theorem is sorry-free (all sorries moved to helpers)
3. Each helper file in decomposed/ compiles independently
4. Each helper has exactly 1 theorem
5. No axiom keyword anywhere
6. All helper imports are present in the target file

Returns a VerificationResult with pass/fail + details for feedback.

Usage with verified_loop:
    from .verifiers.lemma_extractor_verifier import make_extractor_verifier

    verify_fn = make_extractor_verifier(stub_rel, theorem_name, workspace)
    outcome = await verified_loop(
        agent_ctx=extractor,
        initial_input={"file": stub_rel, "main_theorem": name, ...},
        verify=verify_fn,
        max_rounds=3,
    )
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from ..po_lean import get_lean_tools


@dataclass
class VerificationResult:
    passed: bool = False
    issues: list[str] = field(default_factory=list)
    main_theorem_sorry_free: bool = False
    helper_count: int = 0
    helpers_compile: int = 0
    helpers_fail: list[str] = field(default_factory=list)

    def summary(self) -> str:
        if self.passed:
            return f"✅ PASSED: main theorem sorry-free, {self.helper_count} helpers all compile"
        return f"❌ FAILED: {'; '.join(self.issues)}"


def verify_lemma_extraction(
    target_file: str,
    main_theorem: str,
    workspace: str,
) -> VerificationResult:
    """Verify lemma_extractor's output is correct.

    Args:
        target_file: Relative path to the file that was processed
        main_theorem: Name of the main theorem that should be sorry-free
        workspace: Workspace relative path (decomposed/ is under this)

    Returns:
        VerificationResult with detailed pass/fail info.
    """
    tools = get_lean_tools()
    result = VerificationResult()

    # ── Check 1: Target file compiles ──
    compile_result = tools.check_compiles(target_file)
    if not compile_result.success:
        result.issues.append(f"Target file does not compile: {target_file}")
        return result

    # ── Check 2: Main theorem is sorry-free ──
    sorries_by_thm = tools.get_sorries_by_theorem(target_file, filter_names=[main_theorem])
    if main_theorem in sorries_by_thm:
        sorry_count = len(sorries_by_thm[main_theorem])
        result.issues.append(
            f"Main theorem '{main_theorem}' still has {sorry_count} sorry(s)")
        return result
    result.main_theorem_sorry_free = True

    # ── Check 3: Helper files exist and compile ──
    root = tools._root
    decomposed_dir = root / workspace / "decomposed"
    if not decomposed_dir.exists():
        result.issues.append("No decomposed/ directory found")
        return result

    helper_files = list(decomposed_dir.glob("lemma_helper_*.lean"))
    result.helper_count = len(helper_files)

    if result.helper_count == 0:
        result.issues.append("No helper files created in decomposed/")
        return result

    for helper in helper_files:
        helper_rel = f"{workspace}/decomposed/{helper.name}"

        # Check compiles
        cr = tools.check_compiles(helper_rel)
        if not cr.success:
            result.helpers_fail.append(f"{helper.name}: does not compile")
            continue

        # Check exactly 1 theorem
        split = tools.split_theorems(helper_rel)
        if split.error:
            result.helpers_fail.append(f"{helper.name}: parse error")
            continue
        if len(split.blocks) != 1:
            result.helpers_fail.append(
                f"{helper.name}: has {len(split.blocks)} theorems (expected 1)")
            continue

        # Check no axiom
        ax = tools.check_axioms(helper_rel)
        if ax.has_axiom:
            result.helpers_fail.append(
                f"{helper.name}: uses axiom keyword ({ax.axiom_names})")
            continue

        result.helpers_compile += 1

    if result.helpers_fail:
        result.issues.append(
            f"{len(result.helpers_fail)} helper(s) have issues: {result.helpers_fail}")
        return result

    # ── Check 4: Target file imports all helpers ──
    imports_result = tools.check_imports(target_file)
    if not imports_result.error:
        workspace_module = workspace.replace("/", ".")
        decomposed_prefix = f"{workspace_module}.decomposed.lemma_helper_"
        helper_imports = [i for i in imports_result.imports if i.startswith(decomposed_prefix)]

        if len(helper_imports) < result.helper_count:
            result.issues.append(
                f"Target imports {len(helper_imports)} helpers but {result.helper_count} exist in decomposed/")
            return result

    # ── Check 5: No axiom in target ──
    ax = tools.check_axioms(target_file)
    if ax.has_axiom:
        result.issues.append(f"Target file uses axiom: {ax.axiom_names}")
        return result

    # ── All checks passed ──
    result.passed = True
    return result


def make_extractor_verifier(
    target_file: str,
    main_theorem: str,
    workspace: str,
) -> callable:
    """Create a verify function compatible with verified_loop.

    Returns a callable that:
    - Returns None if extraction is correct (all checks pass)
    - Returns an error string if something is wrong (fed back to agent)

    Usage:
        verify_fn = make_extractor_verifier(stub_rel, "main_thm", workspace)
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input=...,
            verify=verify_fn,
            max_rounds=3,
        )
    """
    def verify() -> str | None:
        result = verify_lemma_extraction(target_file, main_theorem, workspace)
        if result.passed:
            return None
        return result.summary()

    return verify
