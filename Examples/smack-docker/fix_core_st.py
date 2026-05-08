#!/usr/bin/env python3
"""Post-process BoogieToStrata .core.st output to fix known issues.

Fixes:
  1. Function forward references: topologically sorts function definitions
  2. Parameter/type name shadowing: renames parameters that collide with type names

Usage:
    python3 fix_core_st.py <input.core.st> [output.core.st]

If output is omitted, overwrites input in place.
"""

import re
import sys
from collections import defaultdict


def parse_type_names(content: str) -> set:
    """Extract all type synonym and type constructor names."""
    names = set()
    for m in re.finditer(r'^type (\w+)\s*:=', content, re.MULTILINE):
        names.add(m.group(1))
    for m in re.finditer(r'^type (\w+)\s*;', content, re.MULTILINE):
        names.add(m.group(1))
    return names


def parse_functions(lines: list, start: int, end: int) -> list:
    """Parse function definitions from lines[start:end].
    Returns list of (name, start_line, end_line, text)."""
    funcs = []
    i = start
    while i < end:
        line = lines[i]
        m = re.match(r'function\s+(\w+)\s*', line)
        if m:
            name = m.group(1)
            func_start = i
            if '{' not in line and line.rstrip().endswith(';'):
                # Declaration only (no body)
                funcs.append((name, i, i, line))
                i += 1
                continue
            # Multi-line function: collect until braces balance
            brace_depth = line.count('{') - line.count('}')
            i += 1
            while i < end and brace_depth > 0:
                brace_depth += lines[i].count('{') - lines[i].count('}')
                i += 1
            funcs.append((name, func_start, i - 1, '\n'.join(lines[func_start:i])))
        else:
            i += 1
    return funcs


def toposort_functions(funcs: list) -> list:
    """Topologically sort functions by their call dependencies."""
    func_names = {name for name, _, _, _ in funcs}
    func_map = {name: text for name, _, _, text in funcs}

    # Build dependency graph
    deps = defaultdict(set)
    for name, _, _, text in funcs:
        body = text.split('{', 1)[-1] if '{' in text else ''
        for other in func_names:
            if other != name and re.search(r'\b' + re.escape(other) + r'\b', body):
                deps[name].add(other)

    # Kahn's algorithm
    in_degree = {name: len(deps[name]) for name in func_names}
    reverse_deps = defaultdict(set)
    for name, dep_set in deps.items():
        for dep in dep_set:
            reverse_deps[dep].add(name)

    queue = sorted([n for n in func_names if in_degree[n] == 0])
    result = []
    while queue:
        node = queue.pop(0)
        result.append(node)
        for dependent in sorted(reverse_deps[node]):
            in_degree[dependent] -= 1
            if in_degree[dependent] == 0:
                queue.append(dependent)

    # Append any remaining (cycles)
    remaining = [n for n in func_names if n not in set(result)]
    result.extend(remaining)

    return result


def fix_param_shadowing(func_text: str, type_names: set) -> str:
    """Rename function parameters that shadow type names."""
    # Extract parameter names from signature
    sig_match = re.match(r'(function\s+\w+\s*(?:<[^>]*>\s*)?\()(.+?)(\)\s*:\s*\()', func_text, re.DOTALL)
    if not sig_match:
        return func_text

    prefix, params_str, suffix = sig_match.groups()
    rest = func_text[sig_match.end():]

    # Parse parameters
    params = re.findall(r'(\w+)\s*:\s*([^,)]+)', params_str)
    renames = {}
    new_params = []
    for pname, ptype in params:
        if pname in type_names:
            new_name = f"p_{pname}"
            renames[pname] = new_name
            new_params.append(f"{new_name} : {ptype.strip()}")
        else:
            new_params.append(f"{pname} : {ptype.strip()}")

    if not renames:
        return func_text

    new_sig = prefix + ', '.join(new_params) + suffix + rest

    # Apply renames in the body
    body_start = new_sig.find('{')
    if body_start >= 0:
        header = new_sig[:body_start]
        body = new_sig[body_start:]
        for old, new in renames.items():
            # Replace word-boundary occurrences in body only
            body = re.sub(r'\b' + re.escape(old) + r'\b', new, body)
        new_sig = header + body

    return new_sig


def fix_core_st(content: str) -> str:
    """Apply all fixes to a .core.st file."""
    lines = content.split('\n')
    type_names = parse_type_names(content)

    # Find the functions section
    func_section_start = None
    func_section_end = None
    for i, line in enumerate(lines):
        if line == '// Functions':
            func_section_start = i + 1
        elif func_section_start is not None and line.startswith('// ') and i > func_section_start:
            func_section_end = i
            break
    if func_section_start is None:
        return content
    if func_section_end is None:
        func_section_end = len(lines)

    # Parse, sort, and fix functions
    funcs = parse_functions(lines, func_section_start, func_section_end)
    sorted_order = toposort_functions(funcs)
    func_text_map = {name: text for name, _, _, text in funcs}

    # Apply param shadowing fix and rebuild
    fixed_funcs = []
    for name in sorted_order:
        if name in func_text_map:
            fixed = fix_param_shadowing(func_text_map[name], type_names)
            fixed_funcs.append(fixed)

    # Reconstruct file
    before = '\n'.join(lines[:func_section_start])
    after = '\n'.join(lines[func_section_end:])
    new_func_section = '\n'.join(fixed_funcs)

    return before + '\n' + new_func_section + '\n' + after


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <input.core.st> [output.core.st]", file=sys.stderr)
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2] if len(sys.argv) >= 3 else infile

    with open(infile) as f:
        content = f.read()

    result = fix_core_st(content)

    with open(outfile, 'w') as f:
        f.write(result)

    print(f"  Fixed: {infile} -> {outfile}", file=sys.stderr)


if __name__ == '__main__':
    main()
