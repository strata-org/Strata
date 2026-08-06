"""Tests for the union-merge decomposition commit + dangling-import guard.

Background: the old decomposition-commit rotated an existing ``decomposed/`` dir
aside to ``decomposed_old_N/`` before swapping in ``new_decomposition/``. On a
RE-EXTRACTION that regenerated only some files, already-proved helpers that a
sibling still imported (e.g. ``bd_shape.lean`` importing the ``bd_*`` leaves) were
shoved into ``decomposed_old_N`` while their import path
(``.../decomposed/lemma_helper_bd_*``) stayed pointing at ``decomposed/`` → a
"bad import" / "no such file" build gate that neither writer nor guide could fix
(a 15-chunk loop observed live on 2026-08-06). Nothing ever read
``decomposed_old_N``.

The fix (union/overwrite): copy ``new_decomposition/`` INTO the existing
``decomposed/`` — overwrite same-named files, KEEP the rest — so referenced-but-
not-regenerated helpers stay in place and imports keep resolving. No
``decomposed_old`` is ever created. Genuinely-dead files are BigSur's to prune.

These test the pure helpers that implement/guard the behavior:
  * ``_find_dangling_imports`` — flags a decomposed/ file importing a workspace-
    local module whose .lean does not exist (the orphan signature); ignores
    external (Strata.*/Mathlib) imports.
  * ``_sweep_decomposed_old`` — removes leftover decomposed_old_* dirs.
  * union-merge semantics via shutil.copytree(dirs_exist_ok=True): a filesystem-
    level assertion that a re-extraction preserves an imported helper and creates
    no decomposed_old dir.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_decomposition_merge.py
"""

from __future__ import annotations

import os
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_v5 import _find_dangling_imports, _sweep_decomposed_old


def _mk_ws():
    """A temp cwd with a workspace 'ws': an empty decomposed/ dir plus the shared
    Stub/Def.lean that real decompositions import (so a `ws.Stub.Def` import is not
    a false dangling hit)."""
    cwd = Path(tempfile.mkdtemp())
    (cwd / "ws" / "decomposed").mkdir(parents=True)
    (cwd / "ws" / "Stub").mkdir(parents=True)
    (cwd / "ws" / "Stub" / "Def.lean").write_text("-- shared defs\n")
    return cwd


# ── _find_dangling_imports ────────────────────────────────────────────────────

def test_dangling_import_flagged_when_file_missing():
    cwd = _mk_ws()
    dec = cwd / "ws" / "decomposed"
    # bd_shape imports a workspace-local helper whose file does NOT exist.
    (dec / "lemma_helper_bd_shape.lean").write_text(
        "public import ws.Stub.Def\n"
        "import ws.decomposed.lemma_helper_bd_cmd_reaches_terminal\n"
        "theorem bd_shape : True := by trivial\n")
    dangling = _find_dangling_imports(cwd, "ws")
    assert len(dangling) == 1, dangling
    assert "lemma_helper_bd_cmd_reaches_terminal" in dangling[0]
    shutil.rmtree(cwd)
    print("✓ test_dangling_import_flagged_when_file_missing")


def test_no_dangling_when_imported_file_present():
    cwd = _mk_ws()
    dec = cwd / "ws" / "decomposed"
    (dec / "lemma_helper_bd_cmd_reaches_terminal.lean").write_text(
        "theorem bd_cmd_reaches_terminal : True := by trivial\n")
    (dec / "lemma_helper_bd_shape.lean").write_text(
        "import ws.decomposed.lemma_helper_bd_cmd_reaches_terminal\n"
        "theorem bd_shape : True := by trivial\n")
    assert _find_dangling_imports(cwd, "ws") == []
    shutil.rmtree(cwd)
    print("✓ test_no_dangling_when_imported_file_present")


def test_external_imports_not_flagged():
    cwd = _mk_ws()
    dec = cwd / "ws" / "decomposed"
    # Imports of OTHER libraries must never be flagged as dangling — only
    # workspace-local (ws.*) modules are our responsibility.
    (dec / "lemma_helper_x.lean").write_text(
        "public import Strata.DL.Imperative.StmtSemantics\n"
        "import Mathlib.Tactic\n"
        "import Strata.Transform.CallElimCorrect\n"
        "theorem x : True := by trivial\n")
    assert _find_dangling_imports(cwd, "ws") == []
    shutil.rmtree(cwd)
    print("✓ test_external_imports_not_flagged")


def test_dangling_scan_is_recursive():
    """Nested decompositions (decomposed/.../decomposed/) are scanned too."""
    cwd = _mk_ws()
    nested = cwd / "ws" / "decomposed" / "lemma_helper_a" / "decomposed"
    nested.mkdir(parents=True)
    (nested / "lemma_helper_b.lean").write_text(
        "import ws.decomposed.lemma_helper_a.decomposed.lemma_helper_gone\n"
        "theorem b : True := by trivial\n")
    dangling = _find_dangling_imports(cwd, "ws")
    assert len(dangling) == 1 and "lemma_helper_gone" in dangling[0]
    shutil.rmtree(cwd)
    print("✓ test_dangling_scan_is_recursive")


# ── _sweep_decomposed_old ─────────────────────────────────────────────────────

def test_sweep_removes_decomposed_old_dirs():
    cwd = _mk_ws()
    (cwd / "ws" / "decomposed_old_0").mkdir()
    (cwd / "ws" / "decomposed_old_1").mkdir()
    # a nested one, and a legit dir that must survive
    (cwd / "ws" / "decomposed" / "sub" / "decomposed_old_0").mkdir(parents=True)
    (cwd / "ws" / "decomposed" / "keep.lean").write_text("-- keep\n")
    removed = _sweep_decomposed_old(cwd)
    assert removed == 3, removed
    assert not (cwd / "ws" / "decomposed_old_0").exists()
    assert not (cwd / "ws" / "decomposed_old_1").exists()
    assert not (cwd / "ws" / "decomposed" / "sub" / "decomposed_old_0").exists()
    assert (cwd / "ws" / "decomposed" / "keep.lean").exists()   # untouched
    shutil.rmtree(cwd)
    print("✓ test_sweep_removes_decomposed_old_dirs")


def test_sweep_noop_when_none():
    cwd = _mk_ws()
    assert _sweep_decomposed_old(cwd) == 0
    shutil.rmtree(cwd)
    print("✓ test_sweep_noop_when_none")


# ── union-merge semantics (filesystem level) ──────────────────────────────────

def test_union_merge_preserves_referenced_helper_no_old_dir():
    """Simulate the commit merge: decomposed/ has a proved helper that bd_shape
    imports; a re-extraction regenerates ONLY bd_shape (in new_decomposition/).
    After union-merge (copytree dirs_exist_ok=True + rmtree new), the imported
    helper must STILL be in decomposed/, bd_shape is the fresh version, and NO
    decomposed_old dir exists — so _find_dangling_imports is clean."""
    cwd = _mk_ws()
    ws = cwd / "ws"
    dec = ws / "decomposed"
    # Existing proved helper (imported by bd_shape) + an old bd_shape.
    (dec / "lemma_helper_bd_cmd_reaches_terminal.lean").write_text(
        "theorem bd_cmd_reaches_terminal : True := by trivial\n")
    (dec / "lemma_helper_bd_shape.lean").write_text("-- OLD bd_shape\n")
    # Re-extraction: new_decomposition/ regenerates ONLY bd_shape (fresh content),
    # still importing the proved helper.
    newd = ws / "new_decomposition"
    newd.mkdir()
    (newd / "lemma_helper_bd_shape.lean").write_text(
        "-- NEW bd_shape\n"
        "import ws.decomposed.lemma_helper_bd_cmd_reaches_terminal\n"
        "theorem bd_shape : True := by trivial\n")

    # The union-merge the commit performs:
    shutil.copytree(newd, dec, dirs_exist_ok=True)
    shutil.rmtree(newd)

    # Imported helper preserved (would have been orphaned by the old rotation):
    assert (dec / "lemma_helper_bd_cmd_reaches_terminal.lean").exists()
    # bd_shape is the FRESH version:
    assert "NEW bd_shape" in (dec / "lemma_helper_bd_shape.lean").read_text()
    # No decomposed_old_* created anywhere:
    assert list(cwd.rglob("decomposed_old_*")) == []
    # And no dangling imports:
    assert _find_dangling_imports(cwd, "ws") == []
    shutil.rmtree(cwd)
    print("✓ test_union_merge_preserves_referenced_helper_no_old_dir")


if __name__ == "__main__":
    print("=" * 60)
    print("test_decomposition_merge (union-merge + dangling-import guard)")
    print("=" * 60)
    test_dangling_import_flagged_when_file_missing()
    test_no_dangling_when_imported_file_present()
    test_external_imports_not_flagged()
    test_dangling_scan_is_recursive()
    test_sweep_removes_decomposed_old_dirs()
    test_sweep_noop_when_none()
    test_union_merge_preserves_referenced_helper_no_old_dir()
    print("\n✅ All decomposition-merge tests passed!")
