# Java Test Data

`ion-java-1.11.11.jar` is the [ion-java](https://github.com/amazon-ion/ion-java)
runtime used by the javac-gated tests in `../TestGen.lean` (`#testCompile`,
`#testRoundtrip`, `#testCompileNested`). Those tests compile the Java emitted by
`getIonSerializer%` against this jar, and `#testRoundtrip` additionally runs it to
produce an Ion payload that Lean then decodes. Each test skips with a warning when
javac or this jar is unavailable.

To refresh the jar:

```bash
curl -sLo ion-java-1.11.11.jar \
  https://github.com/amazon-ion/ion-java/releases/download/v1.11.11/ion-java-1.11.11.jar
```

This directory previously also held `comprehensive.ion` / `comprehensive-files.ion`
and the `Simple.dialect.st` dialect used to generate them, for the DDM
dialect-based Java generator. That generator has been removed in favour of
`getIonSerializer%`, and no test read those fixtures, so they are gone.
