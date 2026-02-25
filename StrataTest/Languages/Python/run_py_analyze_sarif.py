#!/usr/bin/env python3
"""Test SARIF output for pyAnalyze / pyAnalyzeLaurel commands.

Runs pyAnalyze --sarif (or pyAnalyzeLaurel --sarif with --laurel) on selected
test files and validates the SARIF output.
Run from StrataTest/Languages/Python/ (same as run_py_analyze.sh).
"""

import argparse
import subprocess
import sys
from pathlib import Path

from validate_sarif import validate

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
TEST_DIR = Path(__file__).resolve().parent
TEST_FILES = sorted(
    f"tests/{p.name}" for p in (Path(__file__).resolve().parent / "tests").glob("test_*.py")
)
SKIP_TESTS = {"test_foo_client_folder", "test_invalid_client_type", "test_unsupported_config"}
SKIP_TESTS_LAUREL = SKIP_TESTS | {"test_class_decl", "test_datetime", "test_strings"}


def run(test_file: str, *, laurel: bool) -> bool:
    test_path = TEST_DIR / test_file
    if not test_path.exists():
        return True

    base_name = Path(test_file).stem
    skip = SKIP_TESTS_LAUREL if laurel else SKIP_TESTS
    if base_name in skip:
        print(f"Skipping: {base_name}")
        return True

    ion_rel = f"StrataTest/Languages/Python/tests/{base_name}.python.st.ion"
    ion_abs = REPO_ROOT / ion_rel
    sarif_abs = REPO_ROOT / f"{ion_rel}.sarif"

    cmd_name = "pyAnalyzeLaurel" if laurel else "pyAnalyze"
    print(f"Testing SARIF output for {cmd_name} {base_name}...")

    # Generate Ion file
    subprocess.run(
        [
            sys.executable, "-m", "strata.gen", "py_to_strata",
            "--dialect", "dialects/Python.dialect.st.ion",
            str(test_path),
            str(ion_abs),
        ],
        cwd=REPO_ROOT / "Tools" / "Python",
        check=True,
    )

    # Run analysis with --sarif
    subprocess.run(
        ["lake", "exe", "strata", cmd_name, "--sarif", ion_rel],
        cwd=REPO_ROOT,
        stdout=subprocess.DEVNULL,
    )

    ok = True
    if not sarif_abs.exists():
        print(f"ERROR: SARIF file not created for {base_name} (expected {sarif_abs})")
        ok = False
    else:
        result = validate(str(sarif_abs), base_name, laurel=laurel)
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
    parser = argparse.ArgumentParser(description="Test SARIF output for pyAnalyze commands.")
    parser.add_argument("--laurel", action="store_true", help="Use pyAnalyzeLaurel instead of pyAnalyze")
    args = parser.parse_args()

    failed = 0
    for tf in TEST_FILES:
        if not run(tf, laurel=args.laurel):
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main())
