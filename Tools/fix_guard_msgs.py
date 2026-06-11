# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT
#!/usr/bin/env python3
"""
Parse `lake test` output to extract #guard_msgs diffs and apply fixes.

The diff format from Lean's #guard_msgs is:
  error: FILE:LINE:COL: ❌️ Docstring on `#guard_msgs` does not match generated message:
  (blank line or diff lines follow)
  + new line (present in actual output, missing from expected)
  - old line (present in expected, missing from actual output)
    context line (two-space indent, present in both)

We reconstruct the full expected message from context + new lines.
"""

import re
import sys
from pathlib import Path
from collections import defaultdict


def parse_lake_test_output(output: str):
    """Parse lake test output and extract (file, line, new_message) tuples."""
    results = []
    lines = output.split('\n')
    i = 0

    while i < len(lines):
        line = lines[i]

        # Match the error header for a guard_msgs mismatch
        m = re.match(
            r'^error: (.+?):(\d+):\d+: ❌️ Docstring on `#guard_msgs` does not match generated message:',
            line
        )
        if not m:
            i += 1
            continue

        filepath = m.group(1)
        guard_line = int(m.group(2))
        i += 1

        # Collect the new (actual) message from diff lines
        new_msg_lines = []

        while i < len(lines):
            dl = lines[i]

            # Stop at next error/info/trace at column 0 that isn't part of the diff
            # Diff lines start with '+ ', '- ', or '  ' (two spaces)
            if dl.startswith('+ '):
                # New line - part of actual output
                new_msg_lines.append(dl[2:])
            elif dl.startswith('- '):
                # Old line - skip (not part of new message)
                pass
            elif dl.startswith('  '):
                # Context line - part of both old and new
                new_msg_lines.append(dl[2:])
            elif dl == '+' :
                # A '+' alone means an empty line in the new output
                new_msg_lines.append('')
            elif dl == ' ':
                # A single space means an empty context line
                new_msg_lines.append('')
            elif dl == '':
                # Empty line - could be part of message or end of diff
                # Peek ahead: if next line is a diff line, this is part of the message
                if i + 1 < len(lines):
                    next_line = lines[i + 1]
                    if (next_line.startswith('+ ') or next_line.startswith('- ') or
                        next_line.startswith('  ') or next_line == '+' or next_line == ' '):
                        new_msg_lines.append('')
                    else:
                        break
                else:
                    break
            else:
                break
            i += 1

        # Strip trailing empty lines
        while new_msg_lines and new_msg_lines[-1] == '':
            new_msg_lines.pop()

        if new_msg_lines:
            results.append((filepath, guard_line, new_msg_lines))

    return results


def find_docstring_range(file_lines, guard_msgs_line_num):
    """
    Given the 1-indexed line number of #guard_msgs, find the /-- ... -/ or /- ... -/ docstring.
    Returns (start_idx, end_idx) as 0-indexed inclusive line indices.
    """
    guard_idx = guard_msgs_line_num - 1  # convert to 0-indexed

    # Scan backwards from the line before #guard_msgs to find -/
    end_idx = None
    for j in range(guard_idx - 1, -1, -1):
        stripped = file_lines[j].strip()
        if stripped == '-/' or stripped.endswith('-/'):
            end_idx = j
            break
        # Skip blank lines between -/ and #guard_msgs
        if stripped != '':
            break

    if end_idx is None:
        return None

    # Now scan backwards from end_idx to find /-- or /-
    start_idx = None
    for j in range(end_idx, -1, -1):
        line = file_lines[j]
        stripped = line.strip()
        if stripped.startswith('/--') or stripped.startswith('/-'):
            start_idx = j
            break

    if start_idx is None:
        return None

    return (start_idx, end_idx)


def apply_fixes(results):
    """Apply all fixes grouped by file."""
    by_file = defaultdict(list)
    for filepath, guard_line, new_lines in results:
        by_file[filepath].append((guard_line, new_lines))

    total_fixes = 0
    for filepath, fixes in sorted(by_file.items()):
        p = Path(filepath)
        if not p.exists():
            print(f"WARNING: File not found: {filepath}", file=sys.stderr)
            continue

        file_content = p.read_text()
        file_lines = file_content.split('\n')

        # Sort fixes by line number in REVERSE order so edits don't shift line numbers
        fixes.sort(key=lambda x: x[0], reverse=True)

        for guard_line, new_msg_lines in fixes:
            ds_range = find_docstring_range(file_lines, guard_line)
            if ds_range is None:
                print(f"WARNING: Could not find docstring for {filepath}:{guard_line}", file=sys.stderr)
                continue

            start_idx, end_idx = ds_range

            # #guard_msgs always requires doc comments (/--), not regular comments (/-)
            # Build new docstring block
            new_block = ['/--']
            # Skip leading empty lines to avoid blank line after /- or /--
            start_idx_msg = 0
            while start_idx_msg < len(new_msg_lines) and new_msg_lines[start_idx_msg] == '':
                start_idx_msg += 1
            for ml in new_msg_lines[start_idx_msg:]:
                new_block.append(ml)
            new_block.append('-/')

            # Replace the old docstring
            file_lines[start_idx:end_idx + 1] = new_block
            total_fixes += 1

        new_content = '\n'.join(file_lines)
        p.write_text(new_content)
        print(f"Updated {filepath} ({len(fixes)} fix(es))")

    print(f"\nTotal: {total_fixes} fixes applied")


def main():
    output = sys.stdin.read()
    results = parse_lake_test_output(output)
    print(f"Found {len(results)} guard_msgs failures to fix")
    if results:
        apply_fixes(results)


if __name__ == '__main__':
    main()
