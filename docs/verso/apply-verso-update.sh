#!/bin/bash
# Copy the updated Verso site files in verso-update/ over the sites that Verso
# generated under the given output directory (default: _out next to this
# script).
#
# A site root is a directory that holds index.html, xref.json and
# -verso-search/. Every site that Verso v4.34.0 generates has all three
# replaced files, so a missing one means the output layout changed: stop
# rather than deploy a site that wasn't updated.
#
# Remove this script, its callers and verso-update/ when the docs move to a
# Verso release that generates these files itself (a patched v4.34.x, or
# v4.36.0 or later).
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
src="$here/verso-update"
out="${1:-$here/_out}"

files=(
  find/index.html
  -verso-search/search-highlight.js
  -verso-search/search-box.js
)

if [[ ! -d "$out" ]]; then
  echo "error: output directory '$out' does not exist" >&2
  exit 1
fi

roots=()
while IFS= read -r -d '' xref; do
  root="$(dirname "$xref")"
  if [[ -f "$root/index.html" && -d "$root/-verso-search" ]]; then
    roots+=("$root")
  fi
done < <(find "$out/" -name xref.json -type f -print0)

if (( ${#roots[@]} == 0 )); then
  echo "error: no Verso sites found under '$out'" >&2
  exit 1
fi

# Every html-single or html-multi directory that Verso wrote must be a site
# root found above, so that no site is left out silently.
for dir in "$out"/html-single "$out"/html-multi "$out"/*/html-single "$out"/*/html-multi; do
  [[ -d "$dir" ]] || continue
  found=0
  for root in "${roots[@]}"; do
    if [[ "$root" -ef "$dir" ]]; then
      found=1
      break
    fi
  done
  if (( found == 0 )); then
    echo "error: '$dir' is not a Verso site (no index.html, xref.json or -verso-search/);" \
      "remove stale output with 'make clean'" >&2
    exit 1
  fi
done

for root in "${roots[@]}"; do
  # The updated search-box.js needs search-page.js, which Verso v4.30.0 and
  # later generate.
  if [[ ! -f "$root/-verso-search/search-page.js" ]]; then
    echo "error: '$root' has no -verso-search/search-page.js" >&2
    exit 1
  fi
  for f in "${files[@]}"; do
    if [[ ! -f "$root/$f" ]]; then
      echo "error: '$root/$f' does not exist" >&2
      exit 1
    fi
    cp -- "$src/$f" "$root/$f"
    if ! cmp -s -- "$src/$f" "$root/$f"; then
      echo "error: failed to update '$root/$f'" >&2
      exit 1
    fi
  done
  echo "Updated $root"
done
