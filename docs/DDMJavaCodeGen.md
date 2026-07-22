# Laurel Java Code Generator

Generates Java source files for Lean types using the `getIonSerializer%`
compile-time elaborator. The generated Java consists of sealed interfaces,
records, and Ion serialization methods matching the format expected by
`getIonDeserializer%`.

## Usage from the CLI

The `laurelJavaGen` Lake executable generates Java source files for the
Laurel AST types.

```
lake exe laurelJavaGen <package> <output-dir>
```

### Arguments

| Argument | Description |
|----------|-------------|
| `package` | Java package name (e.g. `org.strata.jverify.laurel`) |
| `output-dir` | Directory where generated Java files will be written |

### Example

```bash
lake exe laurelJavaGen org.strata.jverify.laurel ../jverify/verifier/src/main/java
```

## Usage from Lean

```lean
import Strata.Java.Gen

open Strata.Java

-- getIonSerializer% inspects a Lean type and generates Java source files
-- at compile time. The second argument is the Java package name.
def myFiles : GeneratedFiles := getIonSerializer% MyType "com.example.mypackage"

-- Write the generated files to disk:
#eval writeJavaFiles "./generated" "com.example.mypackage" myFiles
```

## Ion encoding conventions

| Lean type | Ion encoding |
|-----------|-------------|
| Structures | Ion struct with field names as keys |
| Single-constructor inductives | Ion struct with positional keys `_0`, `_1`, ... |
| Multi-constructor inductives | Ion sexp `(ConstructorName arg₁ arg₂ ...)` |

## Type mapping

| Lean Type | Java Type |
|-----------|-----------|
| `Nat` | `long` |
| `Int` | `long` |
| `Float` | `double` |
| `String` | `java.lang.String` |
| `Bool` | `boolean` |
| `StrataDDM.Decimal` | `java.math.BigDecimal` |
| `List α` | `java.util.List<T>` |
| `Option α` | `java.util.Optional<T>` |
| Compound types | Generated sealed interface / record (implements `ToIon`) |

## Implementation

The generator lives in `Strata/Java/Gen.lean`.
The Laurel-specific CLI wrapper is `Scripts/LaurelJavaGen.lean`.
