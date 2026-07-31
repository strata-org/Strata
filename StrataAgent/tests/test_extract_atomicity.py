"""Regression tests for the non-atomic-commit / doomed-decompose bugs found in
the IMO2026 run (session 2026-07-31_09-48-03), where ``Stub.lean`` was left with
dangling ``import ...new_decomposition.*`` lines pointing at a directory that was
later wiped.

Three independent fixes, each tested here without a real ``lake build`` (the
verification build is monkeypatched, so these are fast + deterministic):

  Fix B — ``MoveSession.move_decl`` refuses to move a protected/sibling
     obligation (and any mutual group containing one), enforced at the TOOL layer
     rather than in the prompt. The extractor moved 5 protected siblings in the
     real run because the prompt was the only guard.

  Fix C — ``MoveSession.commit`` is atomic against BOTH a build error AND a build
     TIMEOUT: on either it calls ``revert()`` so ``Stub.lean`` and the staging
     dir are restored, leaving NO dangling imports. The old code had no
     ``TimeoutExpired`` handler, so an ``import Mathlib`` build blowing past the
     hardcoded 300s raised uncaught and skipped the revert.

  (Fix A — the orchestrator skips the extractor entirely when nothing is
     extractable — lives in po_v5 and is covered by the e2e harness, not here.)

Run:  cd StrataAgent && python tests/test_extract_atomicity.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_lean import (
    MoveSession,
    SplitResult,
    TheoremBlock,
)


# ── A fake SwarmLeanTools: only the two things commit()/move_decl() touch. ─────
class _FakeTools:
    """Stands in for SwarmLeanTools: exposes ``_root`` and ``split_theorems``
    returning a fixed parse, so no Lean RPC / lake project is needed."""

    def __init__(self, root: Path, blocks, mutual_groups=None):
        self._root = root
        self._blocks = blocks
        self._mutual_groups = mutual_groups or {}

    def split_theorems(self, file_path: str) -> SplitResult:
        return SplitResult(blocks=list(self._blocks),
                           mutual_groups=dict(self._mutual_groups))


def _mk_session(protected, blocks, mutual_groups=None, root=None):
    tools = _FakeTools(root or Path("/tmp"), blocks, mutual_groups)
    sess = MoveSession(tools, "Stub.lean", "main_thm", "WS",
                       output_subdir="new_decomposition",
                       protected_names=set(protected))
    sess._split = SplitResult(blocks=list(blocks),
                              mutual_groups=dict(mutual_groups or {}))
    return sess


# ══ Fix B: move_decl protected-name enforcement ═══════════════════════════════

def test_move_decl_refuses_main_theorem():
    sess = _mk_session(protected={"sib"}, blocks=[
        TheoremBlock(name="main_thm", start=1, end=1, namespace="Demo"),
    ])
    out = sess.move_decl("main_thm")
    assert "cannot move main theorem" in out, out
    assert not sess._moves
    print("✓ test_move_decl_refuses_main_theorem")


def test_move_decl_refuses_protected_sibling():
    sess = _mk_session(protected={"sib"}, blocks=[
        TheoremBlock(name="sib", start=1, end=1, namespace="Demo"),
    ])
    out = sess.move_decl("sib")
    assert "protected sibling obligation" in out, out
    assert not sess._moves, "a protected sibling must NOT register"
    print("✓ test_move_decl_refuses_protected_sibling")


def test_move_decl_allows_genuine_helper():
    sess = _mk_session(protected={"sib"}, blocks=[
        TheoremBlock(name="sib", start=1, end=1, namespace="Demo"),
        TheoremBlock(name="helper", start=3, end=3, namespace="Demo"),
    ])
    out = sess.move_decl("helper")
    assert out.startswith("OK"), out
    assert [m.decl_name for m in sess._moves] == ["helper"]
    print("✓ test_move_decl_allows_genuine_helper")


def test_move_decl_refuses_mutual_group_with_protected_member():
    sess = _mk_session(
        protected={"sib_c"},
        blocks=[
            TheoremBlock(name="mut_x", start=7, end=7, namespace="Demo", mutual_group=0),
            TheoremBlock(name="sib_c", start=8, end=8, namespace="Demo", mutual_group=0),
        ],
        mutual_groups={0: ["mut_x", "sib_c"]},
    )
    out = sess.move_decl("mut_x")
    assert "mutual group contains protected" in out, out
    assert not sess._moves, "a group containing a protected member must NOT register"
    print("✓ test_move_decl_refuses_mutual_group_with_protected_member")


# ══ Fix C: commit() is atomic on build error AND timeout ══════════════════════

_CLEAN_SRC = (
    "import WS.Stub.Def\n"
    "\n"
    "theorem main_thm : True := by trivial\n"
    "\n"
    "theorem helper : True := by trivial\n"
)


def _commit_with_build(monkeypatched_run):
    """Set up a real on-disk Stub.lean + session, patch subprocess.run in the
    commit() verification build, run commit(), and return (result, final_src)."""
    root = Path(tempfile.mkdtemp())
    stub = root / "Stub.lean"
    stub.write_text(_CLEAN_SRC)

    blocks = [
        TheoremBlock(name="main_thm", start=3, end=3, namespace="",
                     decl_type="theorem", text="theorem main_thm : True := by trivial"),
        TheoremBlock(name="helper", start=5, end=5, namespace="",
                     decl_type="theorem", text="theorem helper : True := by trivial"),
    ]
    sess = _mk_session(protected=set(), blocks=blocks, root=root)
    sess.move_decl("helper")  # a genuine, non-protected move

    orig_run = subprocess.run
    subprocess.run = monkeypatched_run
    try:
        result = sess.commit()
    finally:
        subprocess.run = orig_run
    return result, stub.read_text(), root


def test_commit_reverts_on_build_timeout():
    def fake_run(cmd, **kw):
        # Only the verification `lake build` should reach here.
        raise subprocess.TimeoutExpired(cmd=cmd, timeout=kw.get("timeout", 0))

    result, final_src, root = _commit_with_build(fake_run)

    assert result.error and "timed out" in result.error.lower(), result.error
    # The file must be byte-identical to the pre-extraction original — no dangling
    # `import ...new_decomposition.*` line left behind.
    assert final_src == _CLEAN_SRC, f"file not restored after timeout:\n{final_src}"
    assert "new_decomposition" not in final_src
    # Staging dir must be gone (revert() rmtree's it).
    assert not (root / "WS" / "new_decomposition").exists()
    assert not result.created_files, "created_files must be cleared on a reverted commit"
    print("✓ test_commit_reverts_on_build_timeout")


def test_commit_reverts_on_build_error():
    def fake_run(cmd, **kw):
        class R:
            stdout = "Stub.lean:5:0: error: something broke\n"
            stderr = ""
        return R()

    result, final_src, root = _commit_with_build(fake_run)

    assert result.error and "Build failed" in result.error, result.error
    assert final_src == _CLEAN_SRC, f"file not restored after error:\n{final_src}"
    assert "new_decomposition" not in final_src
    assert not (root / "WS" / "new_decomposition").exists()
    print("✓ test_commit_reverts_on_build_error")


def test_commit_succeeds_on_clean_build():
    def fake_run(cmd, **kw):
        class R:
            stdout = "Build completed successfully.\n"
            stderr = ""
        return R()

    result, final_src, root = _commit_with_build(fake_run)

    assert result.error is None, result.error
    assert "helper" in [n for n in result.extracted_names], result.extracted_names
    # On success the import IS added and the block removed.
    assert "import WS.new_decomposition.lemma_helper_helper" in final_src, final_src
    assert (root / "WS" / "new_decomposition" / "lemma_helper_helper.lean").exists()
    print("✓ test_commit_succeeds_on_clean_build")


if __name__ == "__main__":
    print("=" * 60)
    print("test_extract_atomicity (move_decl guard + commit atomicity)")
    print("=" * 60)
    # Fix B — pure
    test_move_decl_refuses_main_theorem()
    test_move_decl_refuses_protected_sibling()
    test_move_decl_allows_genuine_helper()
    test_move_decl_refuses_mutual_group_with_protected_member()
    # Fix C — commit atomicity (build monkeypatched)
    test_commit_reverts_on_build_timeout()
    test_commit_reverts_on_build_error()
    test_commit_succeeds_on_clean_build()
    print("\n✅ All extract-atomicity tests passed!")
