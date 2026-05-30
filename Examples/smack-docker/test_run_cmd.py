#!/usr/bin/env python3
"""Tests for run_pipeline.run_cmd timeout behaviour.

Run as: python3 test_run_cmd.py
Exits 0 on success, non-zero with a diagnostic on failure.
"""

import sys
import time
from pathlib import Path

# Allow `import run_pipeline` from the same directory.
sys.path.insert(0, str(Path(__file__).resolve().parent))

import run_pipeline  # noqa: E402


def assert_eq(label, actual, expected):
    if actual != expected:
        print(f"FAIL {label}: expected {expected!r}, got {actual!r}")
        sys.exit(1)
    print(f"PASS {label}")


def assert_lt(label, actual, bound):
    if not (actual < bound):
        print(f"FAIL {label}: expected < {bound}, got {actual}")
        sys.exit(1)
    print(f"PASS {label} ({actual:.2f} < {bound})")


def test_hang_under_layer_1():
    """Contrived CPU-bound hang must time out cleanly under the primary path."""
    if not run_pipeline.TIMEOUT_BIN:
        print("SKIP test_hang_under_layer_1: no timeout binary available")
        return
    t0 = time.monotonic()
    rc, stdout, stderr = run_pipeline.run_cmd(
        [sys.executable, "-c", "while True: pass"], timeout=2
    )
    elapsed = time.monotonic() - t0
    assert_eq("rc on hang (Layer 1)", rc, -1)
    assert_eq("stderr on hang (Layer 1)", stderr, "TIMEOUT")
    assert_lt("elapsed on hang (Layer 1)", elapsed, 5.0)


def test_self_test_passed():
    """The module-load probe must have selected a working timeout binary.

    On a stock macOS dev machine with Homebrew coreutils, this should always
    succeed. If it doesn't, we still want to know — but we report SKIP rather
    than FAIL because we cannot guarantee gtimeout is installed everywhere.
    """
    if run_pipeline.TIMEOUT_BIN is None:
        print("SKIP test_self_test_passed: no timeout binary on PATH")
        return
    print(f"PASS test_self_test_passed (TIMEOUT_BIN = {run_pipeline.TIMEOUT_BIN})")


def test_hang_under_layer_3():
    """Force-disable Layer 1; the Popen+killpg fallback must kill cleanly.

    This is the regression test for the original macOS Python 3.11 bug.
    """
    saved = run_pipeline.TIMEOUT_BIN
    run_pipeline.TIMEOUT_BIN = None
    try:
        t0 = time.monotonic()
        rc, stdout, stderr = run_pipeline.run_cmd(
            [sys.executable, "-c", "while True: pass"], timeout=2
        )
        elapsed = time.monotonic() - t0
    finally:
        run_pipeline.TIMEOUT_BIN = saved
    assert_eq("rc on hang (Layer 3)", rc, -1)
    assert_eq("stderr on hang (Layer 3)", stderr, "TIMEOUT")
    assert_lt("elapsed on hang (Layer 3)", elapsed, 10.0)


def test_happy_path():
    """Normal commands should pass through unmodified."""
    rc, stdout, stderr = run_pipeline.run_cmd(["echo", "hello"], timeout=5)
    assert_eq("rc on echo", rc, 0)
    assert_eq("stdout on echo", stdout, "hello\n")


def main():
    test_self_test_passed()
    test_hang_under_layer_1()
    test_hang_under_layer_3()
    test_happy_path()
    print("ALL PASS")


if __name__ == "__main__":
    main()
