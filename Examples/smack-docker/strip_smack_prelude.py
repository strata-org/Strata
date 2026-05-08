#!/usr/bin/env python3
"""Strip SMACK prelude procedure implementations from a .bpl file.

SMACK-generated Boogie files contain ~14 prelude procedure implementations
(e.g., __SMACK_and32, __SMACK_or64) that use unstructured multi-target gotos
incompatible with BoogieToStrata. This script removes their bodies, converting
them into uninterpreted procedure declarations while preserving user code.

Usage:
    python3 strip_smack_prelude.py <input.bpl> [output.bpl]

If output is omitted, writes to <input>_stripped.bpl.
"""

import re
import sys


def is_user_procedure(name: str) -> bool:
    """Return True if this procedure is user code that should keep its body."""
    # Always keep main and initialization
    if name in ('main', '$initialize', '__SMACK_static_init', '__SMACK_init_func_memory_model'):
        return True
    # Skip known SMACK/Corral prelude patterns
    if name.startswith('__SMACK_') or name.startswith('__VERIFIER_'):
        return False
    if name.startswith('corral_'):
        return False
    if name.startswith('boogie_si_record'):
        return False
    if name in ('$alloc', '$malloc', '$free', '$$alloc'):
        return False
    # Keep everything else (user-defined functions)
    return True


def strip_prelude_implementations(content: str) -> str:
    """Remove implementation bodies from prelude procedures."""
    lines = content.split('\n')
    output = []
    i = 0
    skip_count = 0

    while i < len(lines):
        line = lines[i]

        # Match procedure with a body (not ending in ';')
        m = re.match(r'\s*procedure\s+(?:\{[^}]*\}\s*)?(\S+)\(', line)
        if m and not line.rstrip().endswith(';'):
            proc_name = m.group(1)

            if not is_user_procedure(proc_name):
                # Collect the full signature (procedure ... returns (...))
                sig_lines = [line]
                i += 1
                while i < len(lines) and not lines[i].strip().startswith('{'):
                    sig_lines.append(lines[i])
                    i += 1

                # Skip the body (match braces)
                if i < len(lines) and lines[i].strip().startswith('{'):
                    brace_depth = 0
                    while i < len(lines):
                        brace_depth += lines[i].count('{') - lines[i].count('}')
                        i += 1
                        if brace_depth <= 0:
                            break

                # Reconstruct as a declaration: strip body, add semicolons
                # Remove any 'modifies', 'requires', 'ensures', 'free' clauses
                # from the declaration (they reference globals that become params)
                decl_parts = []
                for sl in sig_lines:
                    stripped = sl.strip()
                    if stripped.startswith('modifies') or stripped.startswith('free'):
                        continue
                    decl_parts.append(sl)

                # Join and ensure it ends with exactly one semicolon
                decl = '\n'.join(decl_parts).rstrip().rstrip(';') + ';'
                output.append(decl)
                skip_count += 1
                continue

        output.append(line)
        i += 1

    print(f"  Stripped {skip_count} prelude implementations", file=sys.stderr)
    return '\n'.join(output)


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <input.bpl> [output.bpl]", file=sys.stderr)
        sys.exit(1)

    infile = sys.argv[1]
    if len(sys.argv) >= 3:
        outfile = sys.argv[2]
    else:
        outfile = infile.replace('.bpl', '_stripped.bpl')

    with open(infile) as f:
        content = f.read()

    result = strip_prelude_implementations(content)

    with open(outfile, 'w') as f:
        f.write(result)

    print(f"  {infile} -> {outfile}", file=sys.stderr)


if __name__ == '__main__':
    main()
