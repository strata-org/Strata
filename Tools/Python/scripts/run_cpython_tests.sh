#!/bin/bash
set -euo pipefail

if [ ! -f "scripts/run_test.sh" ]; then
  >@2 echo "File does not exist: scripts/run_test.sh"
  exit 1
elif [ ! -f "scripts/gen_dialect.sh" ]; then
  >@2 echo "File does not exist: scripts/gen_dialect.sh"
  exit 1
fi

if [ "$#" -ne 1 ]; then
    >&2 echo "Missing CPython version to test"
    exit
fi

VER="$1"
prefix="cpython-$VER"
if [ -d "$prefix" ]; then
  echo "Skipping download: $prefix already exists"
else
  git clone https://github.com/python/cpython.git --branch $VER --depth 1 $prefix
fi

if [ ! -f "dialects/Python.dialect.st.ion" ]; then
  >@2 echo "Missing Python dialect.  Run ./scripts/gen_dialect.sh with Python 3.13 or later"
  exit 1
fi

if [ "$VER" == "3.14" ]; then
  expected_failures="/tokenizedata/bad_coding.py"
  expected_failures="$expected_failures;/tokenizedata/bad_coding2.py"
  expected_failures="$expected_failures;/tokenizedata/badsyntax_3131.py"
  expected_failures="$expected_failures;/tokenizedata/badsyntax_pep3120.py"

elif [ "$VER" == "3.13" ]; then
  expected_failures=""
elif [ "$VER" == "3.12" ]; then
  expected_failures="/tokenizedata/badsyntax_3131.py"
  expected_failures="$expected_failures;/tokenizedata/badsyntax_pep3120.py"
  expected_failures="$expected_failures;/tokenizedata/bad_coding.py"
  expected_failures="$expected_failures;/tokenizedata/bad_coding2.py"
  expected_failures="$expected_failures;/test_lib2to3/data/different_encoding.py"
  expected_failures="$expected_failures;/test_lib2to3/data/false_encoding.py"
  expected_failures="$expected_failures;/test_lib2to3/data/bom.py"
  expected_failures="$expected_failures;/test_lib2to3/data/py2_test_grammar.py"
  expected_failures="$expected_failures;/test_lib2to3/data/crlf.py"
else
  expected_failures=""
fi

if command -v mise >/dev/null 2>&1; then
  python="mise x python@$VER -- python"
else
  python="python3"
fi

if [ "$VER" == "3.14" ]; then
  python="$python -Xgil=0"
fi

report="report.$VER.txt"

echo "Generating report in $report" | tee $report
count=1
failures=0
for i in `find $prefix/Lib/test -name "*.py"`; do
  if [[ "$expected_failures" == *"${i#$prefix/Lib/test}"* ]]; then
    should_fail=1
    echo "$count : $i (expecting failure)" | tee -a "$report"
  else
    should_fail=0
    echo "$count : $i" | tee -a "$report"
  fi
  count=$((count + 1))

  set +e
  PYTHON="$python" ./scripts/run_test.sh $i >> "$report" 2>&1
  status=$?
  set -e
  if [ $should_fail -ne 0 ]; then
    if [ "$status" -eq 0 ]; then
      failures=$((failures + 1))
    fi
  else
    if [ "$status" -ne 0 ]; then
      failures=$((failures + 1))
    fi
  fi
done

if [ "$failures" -ne 0 ]; then
  echo "$failures failure(s).  See $report"
  exit 1
fi
