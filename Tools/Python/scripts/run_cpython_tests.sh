#!/bin/bash

if [ ! -f "scripts/run_test.sh" ]; then
  echo "File does not exist: scripts/run_test.sh"
  exit 1
elif [ ! -f "scripts/gen_dialect.sh" ]; then
  echo "File does not exist: scripts/gen_dialect.sh"
  exit 1
fi

rm -rf cpython-3.12
git clone https://github.com/python/cpython.git --branch 3.12 --depth 1 cpython-3.12

./scripts/gen_dialect.sh

count=1
for i in `find cpython-3.12/Lib/test -name "*.py"`; do
  echo "$count : $i"
  ./scripts/run_test.sh $i
  count=$((count + 1))
done 2>&1 | tee report.txt

! grep "Two programs are different" report.txt
