#!/usr/bin/env python3
"""Tally feature counts across all files from pyFeatures log_all output."""

import sys
from collections import defaultdict

totals = defaultdict(lambda: defaultdict(int))
file_count = 0
current_section = None

for line in sys.stdin:
    line = line.rstrip()
    if line.startswith("=== FILE:"):
        file_count += 1
        current_section = None
    elif line.startswith("=== ") and line.endswith(" ==="):
        current_section = line[4:-4]
    elif current_section and ":" in line:
        parts = line.strip().split(": ", 1)
        if len(parts) == 2:
            name, count = parts[0], int(parts[1])
            totals[current_section][name] += count

print(f"Files analyzed: {file_count}\n")

for section in sorted(totals):
    print(f"=== {section} ===")
    entries = sorted(totals[section].items(), key=lambda x: -x[1])
    for name, count in entries:
        print(f"  {name:20s} {count:6d}")
    print()
