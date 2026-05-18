# Java Roundtrip Test Data

The Java code generator uses the `getIonSerializer%` elaborator to generate
Java source files from Lean types. The generated Java code produces Ion data
in the same format that `getIonDeserializer%` expects.

## Test approach

The roundtrip test in `TestGen.lean`:
1. Generates Java source files for Lean types using `getIonSerializer%`
2. Compiles the Java code with `javac`
3. Runs the Java code to produce Ion binary data
4. Deserializes the Ion data back into Lean values using `getIonDeserializer%`
5. Verifies the round-tripped values match the originals

## Requirements

- `javac` (Java 17+)
- `ion-java-1.11.11.jar` in this directory (downloaded automatically by tests)
