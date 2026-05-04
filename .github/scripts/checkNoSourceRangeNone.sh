#!/bin/bash
# Check that new code does not introduce net-new SourceRange.none or ExprSourceLoc.none
# without justification.
#
# Suppression:
#   Per-line:  add "-- nosourcerange: <explanation>" on the same line
#   Per-file:  add "-- nosourcerange-file: <explanation>" anywhere in the file
#
# The explanation must be non-empty and must not consist solely of "ok".

set -euo pipefail

BASE_REF="${1:-origin/main}"

# Patterns to check. If any of these are renamed, the safety check below will
# detect that the pattern no longer appears anywhere in the codebase and fail,
# forcing the developer to update this list.
NONE_PATTERNS=("SourceRange.none" "ExprSourceLoc.none")

# Safety check: every pattern must appear at least once in the tracked Lean
# files. If a pattern disappears entirely (e.g. due to a rename), this script
# must be updated to track the new name.
for pat in "${NONE_PATTERNS[@]}"; do
  if ! git ls-files '*.lean' | xargs grep -qF "$pat" 2>/dev/null; then
    echo "ERROR: Pattern '$pat' not found in any tracked .lean file."
    echo "It may have been renamed. Update NONE_PATTERNS in this script."
    exit 1
  fi
done

MERGE_BASE=$(git merge-base HEAD "$BASE_REF" 2>/dev/null || echo "$BASE_REF")

# Build a grep -F pattern file from the array
GREP_PATTERNS=$(printf '%s\n' "${NONE_PATTERNS[@]}")

# Get all new lines matching any none-pattern (unsuppressed per-line)
HITS=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | awk '
    /^--- /    { next }
    /^\+\+\+ / { file = substr($0, 7); next }
    /^@@/      { split($3, a, /[,+]/); lineno = a[2]; next }
    /^\+/      { print file ":" lineno ":" substr($0, 2); lineno++ }
  ' \
  | { \
      grep -F -f <(echo "$GREP_PATTERNS") | \
      grep -v -P -- '-- nosourcerange(-file)?:\s*(?!ok\s*$)\S'; grep_status=$?; \
      if [ "$grep_status" -gt 1 ]; then exit "$grep_status"; else exit 0; fi; })

if [ -z "$HITS" ]; then
  echo "OK: No new SourceRange.none / ExprSourceLoc.none usage found."
  exit 0
fi

# Filter out files that contain a file-level suppression marker (check actual file content)
FILTERED=""
while IFS= read -r line; do
  file="${line%%:*}"
  if ! grep -qP -- '-- nosourcerange-file:\s*(?!ok\s*$)\S' "$file" 2>/dev/null; then
    FILTERED="${FILTERED}${line}
"
  fi
done <<< "$HITS"

# Remove trailing newline
FILTERED=$(echo "$FILTERED" | sed '/^$/d')

if [ -z "$FILTERED" ]; then
  echo "OK: All occurrences are suppressed."
  exit 0
fi

ADDED=$(echo "$FILTERED" | wc -l | tr -d ' ')

# Count removed lines matching any none-pattern from the same diff
REMOVED=$(git diff "$MERGE_BASE"...HEAD --unified=0 --diff-filter=ACMR -- '*.lean' \
  | grep -E '^-[^-]' \
  | grep -cF -f <(echo "$GREP_PATTERNS") || true)

NET=$((ADDED - REMOVED))

if [ "$NET" -gt 0 ]; then
  echo "ERROR: Net increase of $NET unsuppressed SourceRange.none / ExprSourceLoc.none occurrence(s)."
  echo "  (added: $ADDED, removed: $REMOVED)"
  echo ""
  echo "Each occurrence should either propagate real source metadata or"
  echo "be suppressed with one of:"
  echo "  -- nosourcerange: <explanation>       (on the same line)"
  echo "  -- nosourcerange-file: <explanation>  (anywhere in the file, covers all occurrences)"
  echo ""
  echo "The explanation must be non-empty and must not consist solely of \"ok\"."
  echo ""
  echo "$FILTERED"
  exit 1
fi

echo "OK: No net increase in unsuppressed usage (added: $ADDED, removed: $REMOVED)."
