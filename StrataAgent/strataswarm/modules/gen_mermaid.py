#!/usr/bin/env python3
"""Generate a Mermaid state diagram from any module with a TRANSITIONS table.

Usage:
    python -m strataswarm.modules.gen_mermaid task_manager
    python -m strataswarm.modules.gen_mermaid task_manager --output diagram.md
    python -m strataswarm.modules.gen_mermaid prover_orchestrator
"""

from __future__ import annotations

import argparse
import importlib
import sys


def generate_mermaid(module_name: str) -> str:
    full_module = f"strataswarm.modules.{module_name}" if "." not in module_name else module_name
    try:
        mod = importlib.import_module(full_module)
    except ImportError:
        # Try relative
        mod = importlib.import_module(f".{module_name}", package="strataswarm.modules")

    transitions = getattr(mod, "TRANSITIONS", None)
    if not transitions:
        print(f"Error: {full_module} has no TRANSITIONS table", file=sys.stderr)
        sys.exit(1)

    states = sorted(set(
        [k[0] for k in transitions] + [v for v in transitions.values()]
    ))

    lines = ["stateDiagram-v2"]

    # Mark start state
    first_state = next(iter(transitions))[0]
    lines.append(f"    [*] --> {first_state}")

    # Group transitions by (from, to) to combine labels
    edge_labels: dict[tuple[str, str], list[str]] = {}
    for (from_state, transition_name), to_state in transitions.items():
        key = (from_state, to_state)
        edge_labels.setdefault(key, []).append(transition_name)

    for (from_state, to_state), labels in edge_labels.items():
        label = " / ".join(labels)
        lines.append(f"    {from_state} --> {to_state} : {label}")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Generate Mermaid state diagram from TRANSITIONS table")
    parser.add_argument("module", help="Module name (e.g. task_manager)")
    parser.add_argument("--output", "-o", help="Output file (default: stdout)")
    parser.add_argument("--wrap", action="store_true", help="Wrap in markdown code fence")
    args = parser.parse_args()

    diagram = generate_mermaid(args.module)

    if args.wrap:
        output = f"```mermaid\n{diagram}\n```\n"
    else:
        output = diagram + "\n"

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
