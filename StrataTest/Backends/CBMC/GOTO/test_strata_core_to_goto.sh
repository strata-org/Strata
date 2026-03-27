#!/bin/bash
# Test: StrataCoreToGoto translates multi-procedure programs with contracts.
#
# Exercises:
# 1. Multi-procedure translation (two procedures)
# 2. Global variable in symbol table
# 3. Contract annotations on procedures
# 4. Assertions in GOTO output

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
STRATA_CORE_TO_GOTO="$PROJECT_ROOT/.lake/build/bin/StrataCoreToGoto"
PYTHON=${PYTHON:-python3}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

INPUT="$SCRIPT_DIR/test_multi_proc.core.st"

# Test 1: Multi-procedure translation succeeds
echo "Test 1: Multi-procedure translation"
"$STRATA_CORE_TO_GOTO" --output-dir "$WORK" "$INPUT" 2>&1 | grep -q "Translated 2 procedures"
echo "  OK: translated 2 procedures"

# Test 2: Both procedures in symbol table
"$PYTHON" -c "
import json, sys
with open('$WORK/test_multi_proc.symtab.json') as f:
    st = json.load(f)['symbolTable']
assert 'helper' in st, 'helper not in symtab'
assert 'checker' in st, 'checker not in symtab'
print('  OK: helper and checker in symbol table')
"

# Test 3: Global variable in symbol table with correct attributes
"$PYTHON" -c "
import json
with open('$WORK/test_multi_proc.symtab.json') as f:
    st = json.load(f)['symbolTable']
assert 'g' in st, 'global variable g not in symtab'
assert st['g'].get('isStaticLifetime') is True, 'global variable g does not have static lifetime'
print('  OK: global variable g with static lifetime in symbol table')
"

# Test 4: Contract annotations present
"$PYTHON" -c "
import json
with open('$WORK/test_multi_proc.symtab.json') as f:
    st = json.load(f)['symbolTable']
helper_type = json.dumps(st['helper']['type'])
assert '#spec_ensures' in helper_type, 'No ensures on helper'
assert '#spec_assigns' in helper_type, 'No assigns on helper'
checker_type = json.dumps(st['checker']['type'])
assert '#spec_requires' in checker_type, 'No requires on checker'
print('  OK: contract annotations present')
"

# Test 5: GOTO output has assertions
"$PYTHON" -c "
import json
with open('$WORK/test_multi_proc.goto.json') as f:
    data = json.load(f)
fn_names = [fn['name'] for fn in data['functions']]
assert 'helper' in fn_names, f'helper not in goto functions: {fn_names}'
assert 'checker' in fn_names, f'checker not in goto functions: {fn_names}'
for fn in data['functions']:
    if fn['name'] == 'checker':
        types = [i['instructionId'] for i in fn['instructions']]
        assert 'ASSERT' in types, f'No ASSERT in checker: {types}'
        print('  OK: checker has ASSERT instruction')
        break
"

echo "PASS: all StrataCoreToGoto tests passed"
