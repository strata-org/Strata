for f in *.bpl ; do
  echo "== $f"
  boogie $f 2>&1 | tee $f.out
done

for f in *.boogie.st ; do
  echo "== $f"
  timeout -v 60 ../../../.lake/build/bin/strata verify --check $f 2>$f.err 1> $f.out
  echo "Exit code: $?" >> $f.out
done
