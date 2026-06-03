#!/bin/bash
# Check that new code does not introduce net-new panic! calls.
# Only raises an error if more panics are added than removed in this PR.
# To suppress a specific line, add a "-- nopanic:ok" comment on that line.

set -euo pipefail

BASE_REF="${1:-origin/main}"

# Find the merge base so we only inspect lines new to this branch
MERGE_BASE=$(git merge-base HEAD "$BASE_REF" 2>/dev/null || echo "$BASE_REF")

# Get added lines ('+' prefix) from the diff, restricted to .lean files.
# Output format: <file>:<line_number>:<content>
HITS=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | awk '
    /^--- /    { next }
    /^\+\+\+ / { file = substr($0, 7); next }
    /^@@/      { split($3, a, /[,+]/); lineno = a[2]; next }
    /^\+/      { print file ":" lineno ":" substr($0, 2); lineno++ }
  ' \
  | { \
      grep -F 'panic!' | \
      grep -v -- '-- nopanic:ok'; grep_status=$?; \
      if [ "$grep_status" -gt 1 ]; then exit "$grep_status"; else exit 0; fi; })

if [ -z "$HITS" ]; then
  echo "OK: No new panic! usage found."
  exit 0
fi

ADDED=$(echo "$HITS" | wc -l | tr -d ' ')

# Count removed panic! lines from the same diff
REMOVED=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | grep -E '^-[^-]' \
  | grep -cF 'panic!' || true)

NET=$((ADDED - REMOVED))

if [ "$NET" -gt 0 ]; then
  echo "ERROR: Net increase of $NET panic! call(s) — use Except/throw instead."
  echo "  (added: $ADDED, removed: $REMOVED)"
  echo "To suppress a specific occurrence, add '-- nopanic:ok' on that line."
  echo ""
  echo "$HITS"
  exit 1
fi

echo "OK: No net increase in panic! usage (added: $ADDED, removed: $REMOVED)."
