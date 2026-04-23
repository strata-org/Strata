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

BOTH_SKIP = {
    "test_foo_client_folder",
    "test_invalid_client_type",
    "test_unsupported_config",
    "test_with_void_enter",
    "test_class_no_init_extra_args", # No SARIF output because does not run SMT analysis
    "test_user_error_metadata", # No SARIF output because does not run SMT analysis
    "test_is_non_none", # No SARIF output because does not run SMT analysis
    "test_is_not_non_none", # No SARIF output because does not run SMT analysis
    "test_list", # Module-level asserts cause "asserts not supported in functions" error
}
SKIP_TESTS = BOTH_SKIP | {
    "test_augmented_assign",
    "test_boolean_logic",
    "test_break_continue",
    "test_class_field_any",
    "test_class_field_init",
    "test_class_field_use",
    "test_class_methods",
    "test_class_with_methods",
    "test_default_params",
    "test_dict_operations",
    "test_for_loop",
    "test_func_input_type_constraints",
    "test_if_elif",
    "test_ifexpr",
    "test_list",
    "test_list_slice",
    "test_loops",
    "test_module_level",
    "test_multi_function",
    "test_multiple_except",
    "test_nested_calls",
    "test_regex_negative",
    "test_regex_positive",
    "test_return_types",
    "test_subscription",
    "test_try_except",
    "test_try_except_scoping",
    "test_tuple_create",
    "test_tuple_swap",
    "test_tuple_type",
    "test_tuple_unpack",
    "test_variable_reassign",
    "test_while_loop",
    "test_with_statement",
    "test_fstrings",
}
SKIP_TESTS_LAUREL = BOTH_SKIP


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
