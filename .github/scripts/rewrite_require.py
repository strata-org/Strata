# Copyright Strata Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Rewrite a `[[require]]` block in a lakefile.toml to point at a local path.

Used by the downstream-check workflow: a downstream repo's git/rev dependency
on an upstream package (e.g. Strata) is replaced with a local `path` require so
the build runs against the PR's checked-out code instead of a published rev.
This is fork-safe (no need for the PR head SHA to be fetchable from the upstream
remote) and faster (no re-clone of the upstream).

Usage:
    python rewrite_require.py <lakefile.toml> <package-name> <local-path>

Example:
    python rewrite_require.py downstream/lakefile.toml Strata ../upstream

The targeted `[[require]]` block keeps its `name` line; any `git`, `rev`,
`path`, `subDir`, or `scope` lines in that block are dropped and replaced with a
single `path = "<local-path>"` line. Other require blocks are left untouched.
Exits non-zero if no matching block is found, so the workflow fails loudly
rather than silently building against the wrong rev.
"""

import sys

# Keys that describe a dependency source. We strip all of them from the target
# block and substitute a single `path` line, so a prior `git`+`rev` pair can't
# linger and shadow the local override.
SOURCE_KEYS = ("git", "rev", "path", "subdir", "scope", "url")


def main() -> int:
    if len(sys.argv) != 4:
        print(__doc__)
        return 2
    lakefile, pkg, local_path = sys.argv[1], sys.argv[2], sys.argv[3]

    with open(lakefile, encoding="utf-8") as f:
        lines = f.readlines()

    out: list[str] = []
    i = 0
    n = len(lines)
    rewrote = False

    while i < n:
        line = lines[i]
        if line.strip() == "[[require]]":
            # Collect the block: every line up to (but not including) the next
            # table header (`[` at column 0) or EOF.
            block = [line]
            j = i + 1
            while j < n and not lines[j].lstrip().startswith("["):
                block.append(lines[j])
                j += 1

            # Does this block require the package we're overriding?
            is_target = any(
                _is_name(bl, pkg) for bl in block
            )
            if is_target:
                rewrote = True
                out.append("[[require]]\n")
                # Preserve the name line verbatim; drop source keys; keep
                # anything else (e.g. options) as-is. Trailing blank lines are
                # collected separately so the substituted `path` line sits
                # directly under the kept keys, not after a gap.
                kept: list[str] = []
                trailing_blanks: list[str] = []
                for bl in block[1:]:
                    if bl.strip() == "":
                        trailing_blanks.append(bl)
                        continue
                    # A non-blank line ends any run of pending blanks (they
                    # were interior, not trailing) — flush them back.
                    kept.extend(trailing_blanks)
                    trailing_blanks = []
                    key = bl.split("=", 1)[0].strip().lower()
                    if key in SOURCE_KEYS:
                        continue
                    kept.append(bl)
                out.extend(kept)
                out.append(f'path = "{local_path}"\n')
                out.extend(trailing_blanks)
            else:
                out.extend(block)
            i = j
        else:
            out.append(line)
            i += 1

    if not rewrote:
        print(
            f"ERROR: no [[require]] block with name = \"{pkg}\" found in {lakefile}",
            file=sys.stderr,
        )
        return 1

    with open(lakefile, "w", encoding="utf-8") as f:
        f.writelines(out)
    print(f"Rewrote require \"{pkg}\" -> path = \"{local_path}\" in {lakefile}")
    return 0


def _is_name(line: str, pkg: str) -> bool:
    s = line.strip()
    if not s.startswith("name"):
        return False
    _, _, rhs = s.partition("=")
    return rhs.strip().strip('"').strip("'") == pkg


if __name__ == "__main__":
    raise SystemExit(main())
