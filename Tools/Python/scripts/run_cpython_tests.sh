#!/bin/bash
set -euo pipefail

if [ ! -f "scripts/run_test.sh" ]; then
  echo "File does not exist: scripts/run_test.sh"
  exit 1
elif [ ! -f "scripts/gen_dialect.sh" ]; then
  echo "File does not exist: scripts/gen_dialect.sh"
  exit 1
fi

rm -rf cpython-3.13
git clone https://github.com/python/cpython.git --branch 3.13 --depth 1 cpython-3.13

./scripts/gen_dialect.sh

expected_failures="cpython-3.13/Lib/test/tokenizedata/bad_coding.py"
expected_failures="${expected_failures};cpython-3.13/Lib/test/tokenizedata/bad_coding2.py"
expected_failures="${expected_failures};cpython-3.13/Lib/test/tokenizedata/badsyntax_3131.py"
expected_failures="${expected_failures};cpython-3.13/Lib/test/tokenizedata/badsyntax_pep3120.py"


echo "Generating report in report.xt" | tee report.txt
count=1
for i in `find cpython-3.13/Lib/test -name "*.py"`; do
  if [[ "$expected_failures" == *"$i"* ]]; then
    should_fail=1
    echo "$count : $i (expecting failure)" | tee -a report.txt
  else
    should_fail=0
    echo "$count : $i" | tee -a report.txt
  fi

  set +e
  ./scripts/run_test.sh $i 2>>report.txt >> report.txt
  status=$?
  set -e
  if [ $should_fail -ne 0 ]; then
    if [ "$status" -eq 0 ]; then
      echo "Expected failure.  See report.txt"
      exit 1
    fi
  else
    if [ "$status" -ne 0 ]; then
      echo "FAILED.  See report.txt"
      exit 1
    fi
  fi
  count=$((count + 1))
done
