#!/usr/bin/env python3
"""Validate a SARIF file produced by Strata's pyAnalyze --sarif."""

import json
import sys


def validate(sarif_path: str, base_name: str, *, laurel: bool = False) -> str:
    with open(sarif_path) as f:
        d = json.load(f)

    errors = []
    if d.get("version") != "2.1.0":
        errors.append("wrong version")
    if "runs" not in d or len(d["runs"]) != 1:
        errors.append("missing or wrong runs")
        return "FAIL: " + "; ".join(errors)

    run = d["runs"][0]
    if run.get("tool", {}).get("driver", {}).get("name") != "Strata":
        errors.append("wrong tool name")
    results = run.get("results", [])
    if len(results) == 0:
        errors.append("no results")
    for r in results:
        if r.get("level") not in ("none", "error", "warning", "note"):
            errors.append(f"invalid level: {r.get('level')}")
        if "ruleId" not in r:
            errors.append("missing ruleId")
        if "message" not in r or "text" not in r.get("message", {}):
            errors.append("missing message text")

    error_results = [r for r in results if r.get("level") == "error"]
    located_results = [r for r in results if r.get("locations")]

    if base_name == "test_precondition_verification":
        if laurel:
            # Laurel path produces "unknown" (warning) instead of "fail" (error)
            warning_results = [r for r in results if r.get("level") == "warning"]
            if len(warning_results) < 1:
                errors.append(
                    f"expected warnings, got {len(warning_results)} warning-level results"
                )
        else:
            if len(error_results) < 1:
                errors.append(
                    f"expected failures, got {len(error_results)} error-level results"
                )

    if base_name == "test_arithmetic":
        if len(error_results) != 0:
            errors.append(f"expected 0 errors, got {len(error_results)}")
        if len(located_results) < 1:
            errors.append(
                f"expected results with locations, got {len(located_results)}"
            )

    return "FAIL: " + "; ".join(errors) if errors else "OK"


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <sarif_path> <base_name>", file=sys.stderr)
        sys.exit(2)
    result = validate(sys.argv[1], sys.argv[2])
    print(result)
    sys.exit(0 if result == "OK" else 1)
