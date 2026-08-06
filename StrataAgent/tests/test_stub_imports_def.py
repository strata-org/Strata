"""Regression: verify_stub_imports_def must recognize module-system imports.

Bug (session 2026-08-06_21-53-50): the split produced a COMPILING Stub.lean with
`public import StrataAgent.Sandbox.Stub.Def` (Lean module syntax), but the check
used the `check__imports_` RPC, which returns an EMPTY import list for module
files — so `verify_stub_imports_def` wrongly reported the import as missing and the
INIT hard-gate failed an otherwise-valid split. Fix: scan the file text (sees every
import form) instead of the RPC.

Run:
    StrataAgent/.venv/bin/python StrataAgent/tests/test_stub_imports_def.py
"""

from __future__ import annotations

import os
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm.modules.po_verify import verify_stub_imports_def


def _ws_with_stub(stub_text: str):
    cwd = Path(tempfile.mkdtemp())
    (cwd / "StrataAgent" / "Sandbox").mkdir(parents=True)
    (cwd / "StrataAgent" / "Sandbox" / "Stub.lean").write_text(stub_text)
    return cwd


def test_public_import_recognized():
    """The exact form that broke it: `module` + `public import ...Stub.Def`."""
    cwd = _ws_with_stub(
        "module\n\n"
        "public import StrataAgent.Sandbox.Stub.Def\n"
        "set_option warningAsError false\n"
        "theorem foo : True := by sorry\n")
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is True
    shutil.rmtree(cwd)
    print("✓ test_public_import_recognized")


def test_plain_import_recognized():
    cwd = _ws_with_stub("import StrataAgent.Sandbox.Stub.Def\ntheorem f : True := by sorry\n")
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is True
    shutil.rmtree(cwd)
    print("✓ test_plain_import_recognized")


def test_import_all_recognized():
    cwd = _ws_with_stub("import all StrataAgent.Sandbox.Stub.Def\ntheorem f : True := by sorry\n")
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is True
    shutil.rmtree(cwd)
    print("✓ test_import_all_recognized")


def test_missing_import_rejected():
    cwd = _ws_with_stub("import Mathlib.Tactic\ntheorem f : True := by sorry\n")
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is False
    shutil.rmtree(cwd)
    print("✓ test_missing_import_rejected")


def test_commented_import_not_counted():
    """A commented-out import must NOT satisfy the check."""
    cwd = _ws_with_stub(
        "import Mathlib.Tactic  -- public import StrataAgent.Sandbox.Stub.Def\n"
        "theorem f : True := by sorry\n")
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is False
    shutil.rmtree(cwd)
    print("✓ test_commented_import_not_counted")


def test_missing_file_rejected():
    cwd = Path(tempfile.mkdtemp())
    assert verify_stub_imports_def(cwd, "StrataAgent/Sandbox") is False
    shutil.rmtree(cwd)
    print("✓ test_missing_file_rejected")


if __name__ == "__main__":
    test_public_import_recognized()
    test_plain_import_recognized()
    test_import_all_recognized()
    test_missing_import_rejected()
    test_commented_import_not_counted()
    test_missing_file_rejected()
    print("\n✅ All stub-imports-def tests passed!")
