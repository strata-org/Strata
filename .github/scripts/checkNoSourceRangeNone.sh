#!/bin/bash
# Check that new code does not introduce net-new SourceRange.none without justification.
# Only raises an error if more SourceRange.none are added than removed in this PR.
#
# Suppression:
#   Per-line:  add "-- sourcerange:ok" on the same line
#   Per-file:  add "-- sourcerange:file-ok" anywhere in the file (covers all occurrences)

set -euo pipefail

BASE_REF="${1:-origin/main}"

MERGE_BASE=$(git merge-base HEAD "$BASE_REF" 2>/dev/null || echo "$BASE_REF")

# Get all new SourceRange.none lines (unsuppressed per-line)
HITS=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | awk '
    /^--- /    { next }
    /^\+\+\+ / { file = substr($0, 7); next }
    /^@@/      { split($3, a, /[,+]/); lineno = a[2]; next }
    /^\+/      { print file ":" lineno ":" substr($0, 2); lineno++ }
  ' \
  | { \
      grep -F 'SourceRange.none' | \
      grep -v -F 'sourcerange:ok'; grep_status=$?; \
      if [ "$grep_status" -gt 1 ]; then exit "$grep_status"; else exit 0; fi; })

if [ -z "$HITS" ]; then
  echo "OK: No new SourceRange.none usage found."
  exit 0
fi

# Filter out files that contain a file-level suppression marker (check actual file content)
FILTERED=""
while IFS= read -r line; do
  file="${line%%:*}"
  if ! grep -q -F 'sourcerange:file-ok' "$file" 2>/dev/null; then
    FILTERED="${FILTERED}${line}
"
  fi
done <<< "$HITS"

# Remove trailing newline
FILTERED=$(echo "$FILTERED" | sed '/^$/d')

if [ -z "$FILTERED" ]; then
  echo "OK: All SourceRange.none occurrences are suppressed."
  exit 0
fi

ADDED=$(echo "$FILTERED" | wc -l | tr -d ' ')

# Count removed SourceRange.none lines from the same diff
REMOVED=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | grep -E '^-[^-]' \
  | grep -cF 'SourceRange.none' || true)

NET=$((ADDED - REMOVED))

if [ "$NET" -gt 0 ]; then
  echo "ERROR: Net increase of $NET unsuppressed SourceRange.none occurrence(s)."
  echo "  (added: $ADDED, removed: $REMOVED)"
  echo ""
  echo "Each SourceRange.none should either propagate real source metadata or"
  echo "be suppressed with one of:"
  echo "  -- sourcerange:ok       (on the same line)"
  echo "  -- sourcerange:file-ok  (anywhere in the file, covers all occurrences)"
  echo ""
  echo "$FILTERED"
  exit 1
fi

echo "OK: No net increase in unsuppressed SourceRange.none usage (added: $ADDED, removed: $REMOVED)."
