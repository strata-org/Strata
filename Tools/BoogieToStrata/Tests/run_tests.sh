for f in *.bpl ; do
  echo "== $f"
  boogie $f 2>&1 | tee $f.out
done

for f in *.boogie.st ; do
  echo "== $f"
  ../../../.lake/build/bin/strata verify $f 2>$f.err 1> $f.out
  echo "Exit code: $?" >> $f.out
done
