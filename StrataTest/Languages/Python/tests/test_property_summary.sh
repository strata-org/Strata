#!/bin/bash
# Test: Python assert messages propagate as property summaries to GOTO output.
#
# Verifies that `assert cond, "message"` in Python produces a GOTO assert
# instruction with the message as the sourceLocation comment.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
STRATA="$PROJECT_ROOT/.lake/build/bin/strata"
DIALECT="$PROJECT_ROOT/Tools/Python/dialects/Python.dialect.st.ion"
PYTHON=${PYTHON:-python3}

WORK=$(mktemp -d)
trap "rm -rf $WORK" EXIT

# Create Python test file with assert messages
cat > "$WORK/test.py" << 'PY'
def main(x: int) -> None:
    assert x == x, "reflexivity"
    assert x + 0 == x, "additive identity"
PY

# Generate .py.ion
(cd "$WORK" && PYTHONPATH="$PROJECT_ROOT/Tools/Python" \
  "$PYTHON" -m strata.gen py_to_strata --dialect "$DIALECT" test.py test.py.ion) 2>/dev/null

# Translate to GOTO
(cd "$WORK" && "$STRATA" pyAnalyzeLaurelToGoto test.py.ion) 2>/dev/null

# Verify GOTO JSON contains property summaries
python3 -c "
import json, sys
with open('$WORK/test.goto.json') as f:
    data = json.load(f)
comments = []
for fn in data['functions']:
    for inst in fn['instructions']:
        if inst.get('instructionId') == 'ASSERT':
            comments.append(inst.get('sourceLocation', {}).get('comment', ''))

ok = True
for expected in ['reflexivity', 'additive identity']:
    if expected in comments:
        print(f'OK: \"{expected}\" found in GOTO assert comment')
    else:
        print(f'FAIL: \"{expected}\" not found. Got: {comments}')
        ok = False

if not ok:
    sys.exit(1)
print('PASS: Python assert messages propagate to GOTO property summaries')
"
