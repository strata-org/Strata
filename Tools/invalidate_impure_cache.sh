#!/bin/bash

# Usage: ./invalidate_impure_cache.sh [--dry-run]
#
# Runs the purityCheck tool on all .lean files in Strata/ and StrataTest/,
# then deletes cached build artifacts for any module whose elaboration
# might perform I/O.
#
# Options:
#   --dry-run   Show what would be deleted without actually deleting

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LAKE_BUILD="$PROJECT_ROOT/.lake/build"

dry_run=0
if [ "${1:-}" = "--dry-run" ]; then
    dry_run=1
fi

# Ensure purityCheck is built
echo "Building purityCheck..."
(cd "$PROJECT_ROOT" && lake build purityCheck > /dev/null 2>&1)

# Run purity check
echo "Scanning for impure modules..."
LEAN_PATH="$LAKE_BUILD/lib/lean:$PROJECT_ROOT/.lake/packages/plausible/.lake/build/lib/lean"
impure_files=$(cd "$PROJECT_ROOT" && LEAN_PATH="$LEAN_PATH" \
    .lake/build/bin/purityCheck --impure-only \
    Strata/ StrataTest/ StrataMain.lean 2>/dev/null \
    | grep "^IMPURE:" | sed 's/^IMPURE: *//' || true)

if [ -z "$impure_files" ]; then
    echo "All modules are pure — nothing to invalidate."
    exit 0
fi

count=0
deleted=0

while IFS= read -r lean_file; do
    # Strata//Foo/Bar.lean → Strata/Foo/Bar (strip .lean, normalize //)
    stem=$(echo "$lean_file" | sed 's/\.lean$//' | sed 's|//|/|g')

    for dir in "$LAKE_BUILD/lib/lean" "$LAKE_BUILD/ir"; do
        # Find all artifacts matching this stem
        for artifact in "$dir/$stem".*; do
            [ -e "$artifact" ] || continue
            if [ $dry_run -eq 1 ]; then
                echo "  would delete: $artifact"
            else
                rm -f "$artifact"
            fi
            deleted=$((deleted + 1))
        done
    done
    count=$((count + 1))
done <<< "$impure_files"

if [ $dry_run -eq 1 ]; then
    echo ""
    echo "Dry run: $count impure modules, $deleted artifacts would be deleted."
else
    echo "Invalidated $count impure modules ($deleted artifacts deleted)."
fi
