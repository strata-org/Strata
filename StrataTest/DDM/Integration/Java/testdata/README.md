# Java Roundtrip Test Data

`comprehensive.ion` is a Java-generated Ion file that tests all DDM types.

## To regenerate

From this directory:

```bash
./regenerate-testdata.sh
```

This will:
1. Generate Java classes from `Simple.dialect.st`
2. Build and run `GenerateTestData.java` to produce `comprehensive.ion`
3. Clean up generated classes
4. Verify the output with Lean

## What's tested

The test file covers all DDM types in a single AST:
- Num, Str, Ident
- Bool (true and false)
- Decimal, ByteArray
- Option (some and none)
- Seq (with items and empty)
- Nested operations (3 levels deep)
