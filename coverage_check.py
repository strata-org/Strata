#!/usr/bin/env python3
"""Check how many files are covered by a given set of features."""

import sys
from collections import defaultdict

# Define "dominant" feature sets
DOMINANT = {
    "Statement Features": {
        "Expr", "AnnAssign", "Return", "If", "FunctionDef", "Try",
        "Import", "Assign", "For", "ImportFrom", "Raise", "ClassDef", "With",
    },
    "Expression Features": {
        "Name", "Constant", "Call", "Attribute", "Subscript",
        "FormattedValue", "JoinedStr", "Dict", "List", "Compare",
        "BinOp", "UnaryOp", "BoolOp", "ListComp", "Tuple",
    },
    "Constant Features": {
        "ConString", "ConPos", "ConNone", "ConTrue", "ConFalse", "ConFloat",
    },
    "Operator Features": {
        "Mult", "Add", "Sub", "Mod", "Div", "Pow",
    },
    "UnaryOp Features": {"Not", "USub"},
    "BoolOp Features": {"And", "Or"},
    "CmpOp Features": {"Eq", "In", "Gt", "NotIn", "NotEq", "GtE", "Lt"},
    "Pattern Features": set(),
}

# Parse log_all
files = {}  # filename -> {section -> {feature}}
current_file = None
current_section = None

for line in sys.stdin:
    line = line.rstrip()
    if line.startswith("=== FILE:"):
        current_file = line.split("=== FILE: ")[1].rstrip(" ===")
        files[current_file] = defaultdict(set)
        current_section = None
    elif line.startswith("=== ") and line.endswith(" ==="):
        current_section = line[4:-4]
    elif current_section and current_file and ": " in line:
        parts = line.strip().split(": ", 1)
        if len(parts) == 2:
            files[current_file][current_section].add(parts[0])

# Check coverage
covered = []
not_covered = []

for fname, sections in sorted(files.items()):
    missing = []
    for section, features in sections.items():
        supported = DOMINANT.get(section, set())
        unsupported = features - supported
        if unsupported:
            missing.append((section, unsupported))
    if not missing:
        covered.append(fname)
    else:
        not_covered.append((fname, missing))

print(f"=== COVERED: {len(covered)}/{len(files)} files ===\n")
for f in covered:
    print(f"  {f}")

print(f"\n=== NOT COVERED: {len(not_covered)}/{len(files)} files ===\n")
for fname, missing in not_covered:
    missing_flat = []
    for section, features in missing:
        for feat in sorted(features):
            missing_flat.append(f"{section}:{feat}")
    print(f"  {fname}")
    print(f"    missing: {', '.join(missing_flat)}")

# What features would we need to add to cover more files?
print(f"\n=== FEATURES NEEDED TO COVER REMAINING FILES ===\n")
feature_to_files = defaultdict(list)
for fname, missing in not_covered:
    for section, features in missing:
        for feat in features:
            feature_to_files[f"{section}:{feat}"].append(fname)

for feat, fnames in sorted(feature_to_files.items(), key=lambda x: -len(x[1])):
    print(f"  {feat:40s} would help {len(fnames):2d} files: {', '.join(f[:20] for f in fnames)}")
