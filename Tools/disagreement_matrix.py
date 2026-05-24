#!/usr/bin/env python3
"""Read run_pipeline.py output and emit a markdown verdict-disagreement matrix.

Usage: disagreement_matrix.py < pipeline-output.txt > matrix.md

Reads the Program/Strip/B2S/Fix/<backends>/Detail table from
run_pipeline.py output. For each row, classifies divergence:

  - all-agree (no flag)
  - cbmc-vs-native: Strata's cbmc and cbmc-native columns differ;
    auto-tagged as (T-lowering)
  - one-off: one backend's verdict differs from the other(s)
  - all-disagree: every backend has a distinct verdict

Emits a markdown table with a Divergence column.
"""

import re
import sys
from collections import Counter

MATERIAL_VERDICTS = {"PASS", "PARTIAL", "FAIL", "TIMEOUT", "WARN"}


def parse_pipeline_output(text: str) -> tuple[list[str], list[dict]]:
    lines = text.splitlines()
    header_idx = None
    for i, line in enumerate(lines):
        if line.startswith("Program") and "|" in line:
            header_idx = i
            break
    if header_idx is None:
        raise SystemExit("Could not find header line in input")

    header = [c.strip() for c in lines[header_idx].split("|")]
    backends = [h for h in header[4:]
                if h not in ("Strip", "B2S", "Fix", "Detail", "Program", "")]

    rows = []
    for line in lines[header_idx + 2:]:
        if not line.strip() or line.startswith("---") or line.startswith(" "):
            if line.strip().startswith(("deductive:", "bugFinding:", "cbmc:",
                                         "cbmc-native:")):
                continue
            if not line.strip():
                continue
        cells = [c.strip() for c in line.split("|")]
        if len(cells) < 4 + len(backends):
            continue
        if cells[0].startswith("#"):
            continue
        row = {"name": cells[0]}
        for i, bk in enumerate(backends):
            row[bk] = cells[4 + i]
        rows.append(row)
    return backends, rows


def classify_divergence(row: dict, backends: list[str]) -> str:
    verdicts = [row[b] for b in backends if row[b] in MATERIAL_VERDICTS]
    if len(set(verdicts)) <= 1:
        return ""

    if "cbmc" in backends and "cbmc-native" in backends:
        c1 = row.get("cbmc")
        c2 = row.get("cbmc-native")
        if (c1 in MATERIAL_VERDICTS and c2 in MATERIAL_VERDICTS
                and c1 != c2):
            return "**(T-lowering)**"

    counts = Counter(verdicts)
    if all(c == 1 for c in counts.values()):
        return "all-disagree"
    return "one-off"


def emit_markdown(backends: list[str], rows: list[dict]) -> str:
    lines = []
    header = "| Program | " + " | ".join(backends) + " | Divergence |"
    sep = "|" + "---|" * (len(backends) + 2)
    lines.append(header)
    lines.append(sep)
    for row in rows:
        cells = [row["name"]] + [row.get(b, "") for b in backends]
        cells.append(classify_divergence(row, backends))
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n"


def main() -> int:
    text = sys.stdin.read()
    backends, rows = parse_pipeline_output(text)
    sys.stdout.write(emit_markdown(backends, rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())
