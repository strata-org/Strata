#!/usr/bin/env python3
"""Test SARIF output for pyAnalyze command.

Runs pyAnalyze --sarif on selected test files and validates the SARIF output.
Run from StrataTest/Languages/Python/ (same as run_py_analyze.sh).
"""

import os
import subprocess
import sys
from pathlib import Path

from validate_sarif import validate

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
TEST_DIR = Path(__file__).resolve().parent
TEST_FILES = [
    "tests/test_arithmetic.py",
    "tests/test_precondition_verification.py",
]


def run(test_file: str) -> bool:
    test_path = TEST_DIR / test_file
    if not test_path.exists():
        return True

    base_name = Path(test_file).stem
    ion_rel = f"StrataTest/Languages/Python/tests/{base_name}.python.st.ion"
    ion_abs = REPO_ROOT / ion_rel
    sarif_abs = REPO_ROOT / f"{ion_rel}.sarif"

    print(f"Testing SARIF output for {base_name}...")

    # Generate Ion file
    subprocess.run(
        [
            "python", "-m", "strata.gen", "py_to_strata",
            "--dialect", "dialects/Python.dialect.st.ion",
            str(test_path),
            str(ion_abs),
        ],
        cwd=REPO_ROOT / "Tools" / "Python",
        check=True,
    )

    # Run pyAnalyze with --sarif
    subprocess.run(
        ["lake", "exe", "strata", "pyAnalyze", "--sarif", ion_rel, "0"],
        cwd=REPO_ROOT,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    ok = True
    if not sarif_abs.exists():
        print(f"ERROR: SARIF file not created for {base_name} (expected {sarif_abs})")
        ok = False
    else:
        result = validate(str(sarif_abs), base_name)
        if result != "OK":
            print(f"ERROR: SARIF validation failed for {base_name}: {result}")
            ok = False
        else:
            print(f"Test passed: {base_name}")

    # Clean up generated files
    ion_abs.unlink(missing_ok=True)
    sarif_abs.unlink(missing_ok=True)
    return ok


def main() -> int:
    failed = 0
    for tf in TEST_FILES:
        if not run(tf):
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main())
