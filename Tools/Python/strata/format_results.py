#!/usr/bin/env python3
"""Post-process Strata verification output into human-readable format."""
import ast
import os
import re
import sys


def find_decorated_funcs(spec_file: str) -> dict:
    """Returns {func_name: [param_names]} for decorated functions."""
    tree = ast.parse(open(spec_file).read())
    decorated = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            for dec in node.decorator_list:
                if isinstance(dec, ast.Call):
                    func = dec.func
                    if (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                            and func.value.id == 'icontract'):
                        decorated[node.name] = [a.arg for a in node.args.args]
                        break
                    elif isinstance(func, ast.Name) and func.id in ('require', 'ensure'):
                        decorated[node.name] = [a.arg for a in node.args.args]
                        break
    return decorated


def find_call_sites(user_file: str, decorated: dict) -> list:
    """Returns call sites: [(caller_name, lineno, callee_name, col, end_col)]."""
    tree = ast.parse(open(user_file).read())
    sites = []
    for parent in ast.walk(tree):
        if isinstance(parent, ast.FunctionDef):
            for child in ast.walk(parent):
                if isinstance(child, ast.Call):
                    name = None
                    if isinstance(child.func, ast.Name) and child.func.id in decorated:
                        name = child.func.id
                    if name and hasattr(child, 'lineno'):
                        sites.append((parent.name, child.lineno, name,
                                      getattr(child, 'col_offset', 0),
                                      getattr(child, 'end_col_offset', 0)))
    return sites


def identify_callee(assertions: list, decorated: dict) -> str:
    """Try to identify which decorated function a call-site group targets
    by matching assertion parameter names to function signatures."""
    assertion_params = set()
    for assertion_text, _, _ in assertions:
        # Extract parameter names from assertion text like "balance >= amount"
        for token in re.findall(r'\b[a-zA-Z_]\w*\b', assertion_text):
            if token not in ('int', 'result', 'pass', 'fail', 'Assertion', 'failed'):
                assertion_params.add(token)
    # Match against decorated function parameter lists
    best_match = None
    best_score = 0
    for fname, params in decorated.items():
        param_set = set(params)
        overlap = len(assertion_params & param_set)
        if overlap > best_score:
            best_score = overlap
            best_match = fname
    return best_match


def main():
    if len(sys.argv) < 3:
        print("Usage: format_results.py <spec_file> <user_file> [display_file]", file=sys.stderr)
        sys.exit(1)

    spec_file = sys.argv[1]
    user_file = sys.argv[2]
    display_file = sys.argv[3] if len(sys.argv) > 3 else user_file
    raw = sys.stdin.read()

    # spec_file can be colon-separated list of spec files
    spec_files = spec_file.split(':')
    decorated = {}
    for sf in spec_files:
        decorated.update(find_decorated_funcs(sf))
    call_sites = find_call_sites(user_file, decorated)

    noise = ['Verification Results', 'DETAIL:', 'RESULT:', 'ite_cond_calls',
             'Required parameter', 'assert(0):', 'PySpec translation', 'BUG:',
             'SARIF output']

    results = []
    postcond_pyspec = []
    postcond_user = []
    module_name = os.path.splitext(os.path.basename(user_file))[0]
    module_prefix = module_name + '_'
    for line in raw.strip().split('\n'):
        if not line.strip():
            continue
        if any(n in line for n in noise):
            continue
        if ('✅' in line or '❌' in line or '❓' in line):
            stripped = line.strip()
            # Postcondition body checks have [procname] prefix
            if stripped.startswith('['):
                bracket_end = stripped.find(']')
                if bracket_end > 0:
                    proc_name = stripped[1:bracket_end]
                    if proc_name.startswith(module_prefix):
                        postcond_pyspec.append(stripped)
                    else:
                        postcond_user.append(stripped)
                    continue
            # Postcondition summary lines (procname:postcondition_N)
            if ':postcondition' in stripped:
                label = stripped.split(':postcondition')[0]
                if label.startswith(module_prefix):
                    postcond_pyspec.append(stripped)
                else:
                    postcond_user.append(stripped)
                continue
            # Call-site results
            site_match = re.search(r'\(call site (\d+)\)', line)
            site_id = site_match.group(1) if site_match else None
            clean = re.sub(r' \(call site \d+\)', '', line).strip()
            if site_id is not None:
                results.append((site_id, clean))

    # --- Terminal output ---
    print('==== Verification Results ====')
    passes = 0
    fails = 0
    unknowns = 0

    if postcond_user:
        user_passes = sum(1 for line in postcond_user if '✅' in line)
        user_fails = sum(1 for line in postcond_user if '❌' in line or '❓' in line)
        if user_passes > 0 and user_fails == 0:
            print(f'  postcondition body checks: ✅ {user_passes} verified')
            print()
        elif user_fails > 0:
            # Show which functions failed
            failed_funcs = []
            for line in postcond_user:
                if '❌' in line or '❓' in line:
                    func_name = line.split(':postcondition')[0].strip()
                    if func_name not in failed_funcs:
                        failed_funcs.append(func_name)
            if user_passes > 0:
                print(f'  postcondition body checks: ✅ {user_passes} verified, ❌ {user_fails} unproven ({", ".join(failed_funcs)})')
            else:
                print(f'  postcondition body checks: ❌ {user_fails} unproven ({", ".join(failed_funcs)})')
            print()

    # Group results by call site (consecutive IDs = same call).
    grouped = []
    last_id = None
    for site_id, line in results:
        sid = int(site_id)
        if last_id is None or sid != last_id + 1:
            grouped.append([])
        last_id = sid
        is_pass = '✅' in line
        assertion = re.sub(r':.*$', '', line).strip()
        grouped[-1].append((assertion, is_pass, line))

    # Match each group to a call site by identifying the callee from assertions,
    # then finding the next unmatched call site for that callee.
    callee_site_idx = {}  # callee_name -> next index into filtered call_sites
    for group in grouped:
        callee = identify_callee(group, decorated)
        if callee is None:
            # Can't identify — show raw
            print(f'\n  unknown call:')
            for assertion, is_pass, line in group:
                if is_pass: passes += 1
                elif '❓' in line: unknowns += 1
                else: fails += 1
                print(f'    {line}')
            continue

        # Find the next call site for this callee
        idx = callee_site_idx.get(callee, 0)
        matching_sites = [(i, s) for i, s in enumerate(call_sites) if s[2] == callee]
        if idx < len(matching_sites):
            _, (caller, lineno, callee_name, col, end_col) = matching_sites[idx]
            callee_site_idx[callee] = idx + 1
            print(f'\n  {caller}() line {lineno} → {callee_name}():')
        else:
            print(f'\n  → {callee}():')
            col, end_col, lineno, caller = 0, 0, 0, '?'

        for assertion, is_pass, line in group:
            if is_pass: passes += 1
            elif '❓' in line: unknowns += 1
            else: fails += 1
            print(f'    {line}')

    total = passes + fails + unknowns
    print()
    if fails == 0 and unknowns == 0 and passes > 0:
        print(f'RESULT: ✅ Verified ({passes}/{total} passed)')
    elif fails > 0:
        summary = f'RESULT: ❌ {fails}/{total} failed'
        if unknowns > 0:
            summary += f', {unknowns} inconclusive'
        print(summary)
    elif unknowns > 0:
        print(f'RESULT: ⚠️  {unknowns}/{total} inconclusive (no failures)')
    else:
        print('RESULT: No icontract assertions found')

    # --- Diagnostics output (gcc-style for VS Code problemMatcher) ---
    # Postcondition body check failures → underline the function definition
    if postcond_user:
        tree = ast.parse(open(user_file).read())
        func_lines = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                func_lines[node.name] = (node.lineno, node.col_offset, node.end_col_offset or 0)
        # Collect failing functions with their postcondition text from [procname] lines
        failing = {}  # func_name -> list of postcondition texts
        for line in postcond_user:
            if '❌' in line or '❓' in line:
                if line.startswith('['):
                    func_name = line[1:line.find(']')]
                    # Extract postcondition text: "[cap] b >= result: ❌ fail" → "b >= result"
                    text = line[line.find(']') + 2:].split(':')[0].strip()
                elif ':postcondition' in line:
                    func_name = line.split(':postcondition')[0].strip()
                    text = 'postcondition'
                else:
                    continue
                failing.setdefault(func_name, []).append(text)
        for func_name in sorted(failing):
            if func_name in func_lines:
                lineno, col, end_col = func_lines[func_name]
                name_col = col + 4  # len("def ")
                texts = failing[func_name]
                # Filter out internal postconditions (isfrom_int etc)
                texts = [t for t in texts if t != 'postcondition' and 'isfrom' not in t]
                if texts:
                    msg = ', '.join(f'`{t}`' for t in texts)
                    print(f'{display_file}:{lineno}:{name_col + 1}: error: '
                          f'postcondition {msg} unproven for {func_name}()')
                else:
                    print(f'{display_file}:{lineno}:{name_col + 1}: error: '
                          f'postcondition unproven for {func_name}()')

    # Call-site precondition failures
    callee_site_idx2 = {}
    for group in grouped:
        callee = identify_callee(group, decorated)
        if callee is None:
            continue
        idx = callee_site_idx2.get(callee, 0)
        matching_sites = [(i, s) for i, s in enumerate(call_sites) if s[2] == callee]
        if idx < len(matching_sites):
            _, (caller, lineno, callee_name, col, end_col) = matching_sites[idx]
            callee_site_idx2[callee] = idx + 1
        else:
            continue
        for assertion, is_pass, line in group:
            if is_pass or '❓' in line:
                continue
            print(f'{display_file}:{lineno}:{col + 1}: error: '
                  f'precondition `{assertion}` violated in call to {callee_name}()')

    has_unproven = any('❌' in line or '❓' in line for line in postcond_user) if postcond_user else False
    sys.exit(2 if (fails > 0 or has_unproven) else 0)


if __name__ == '__main__':
    main()
