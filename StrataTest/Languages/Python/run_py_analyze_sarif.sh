#!/bin/bash

# Test SARIF output for pyAnalyze command.
# Runs pyAnalyze --sarif on selected test files and validates the SARIF output.
# Run from StrataTest/Languages/Python/ (same as run_py_analyze.sh).

REPO_ROOT="$(cd ../../.. && pwd)"
failed=0

for test_file in tests/test_arithmetic.py tests/test_precondition_verification.py; do
    if [ ! -f "$test_file" ]; then
        continue
    fi

    base_name=$(basename "$test_file" .py)
    ion_file="tests/${base_name}.python.st.ion"
    # Relative to repo root
    ion_rel="StrataTest/Languages/Python/${ion_file}"
    sarif_abs="${REPO_ROOT}/${ion_rel}.sarif"

    echo "Testing SARIF output for $base_name..."

    # Generate Ion file
    (cd "${REPO_ROOT}/Tools/Python" && python -m strata.gen py_to_strata \
        --dialect "dialects/Python.dialect.st.ion" \
        "${REPO_ROOT}/${test_file/#/StrataTest/Languages/Python/}" \
        "${REPO_ROOT}/${ion_rel}")

    # Run pyAnalyze with --sarif
    (cd "$REPO_ROOT" && lake exe strata pyAnalyze --sarif "${ion_rel}" 0) > /dev/null 2>&1

    # Check that SARIF file was created
    if [ ! -f "$sarif_abs" ]; then
        echo "ERROR: SARIF file not created for $base_name (expected $sarif_abs)"
        failed=1
        rm -f "$ion_file"
        continue
    fi

    # Validate JSON structure and SARIF content
    validation=$(python3 -c "
import json, sys

with open('$sarif_abs') as f:
    d = json.load(f)

errors = []
if d.get('version') != '2.1.0':
    errors.append('wrong version')
if 'runs' not in d or len(d['runs']) != 1:
    errors.append('missing or wrong runs')
    print('FAIL: ' + '; '.join(errors))
    sys.exit(0)

run = d['runs'][0]
if run.get('tool', {}).get('driver', {}).get('name') != 'Strata':
    errors.append('wrong tool name')
results = run.get('results', [])
if len(results) == 0:
    errors.append('no results')
for r in results:
    if r.get('level') not in ('none', 'error', 'warning', 'note'):
        errors.append(f'invalid level: {r.get(\"level\")}')
    if 'ruleId' not in r:
        errors.append('missing ruleId')
    if 'message' not in r or 'text' not in r.get('message', {}):
        errors.append('missing message text')

error_results = [r for r in results if r['level'] == 'error']
located_results = [r for r in results if r.get('locations')]

# test_precondition_verification should have failures
if '$base_name' == 'test_precondition_verification':
    if len(error_results) < 1:
        errors.append(f'expected failures, got {len(error_results)} error-level results')

# test_arithmetic should have no failures and some located results
if '$base_name' == 'test_arithmetic':
    if len(error_results) != 0:
        errors.append(f'expected 0 errors, got {len(error_results)}')
    if len(located_results) < 1:
        errors.append(f'expected results with locations, got {len(located_results)}')

if errors:
    print('FAIL: ' + '; '.join(errors))
else:
    print('OK')
" 2>&1)

    if [ "$validation" != "OK" ]; then
        echo "ERROR: SARIF validation failed for $base_name: $validation"
        failed=1
    else
        echo "Test passed: $base_name"
    fi

    # Clean up generated files
    rm -f "$ion_file" "$sarif_abs"
done

exit $failed
