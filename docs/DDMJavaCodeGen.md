# DDM Java Code Generator

The DDM Java code generator produces a set of Java source files from a
dialect definition. These files form a typed, immutable AST library that
can build dialect programs in Java and serialize them to Ion for
consumption by Strata.

## Usage from the CLI

The `strata` CLI provides the `javaGen` command for generating Java source
files directly from a dialect definition.

```
strata javaGen <dialect> <package> <output-dir> [--include <path>]
```

### Arguments

| Argument | Description |
|----------|-------------|
| `dialect` | A dialect name (e.g. `Laurel`) or a path to a `.dialect.st` file |
| `package` | Java package name (e.g. `com.example.mydialect`) |
| `output-dir` | Directory where generated Java files will be written |

### Flags

| Flag | Description |
|------|-------------|
| `--include <path>` | Add a dialect search path (may be repeated) |

### Examples

Generate Java files from a built-in dialect by name:

```bash
strata javaGen Laurel com.example.laurel ./generated
```

Generate from a dialect file on disk:

```bash
strata javaGen Examples/dialects/Bool.dialect.st com.example.bool ./generated
```

Use `--include` to add search paths when the dialect references other
dialect files:

```bash
strata javaGen MyDialect com.example.mydialect ./generated \
  --include ./dialects --include ./deps
```

The command creates the Java package directory structure under `output-dir`
and writes all generated files. On success it prints the output path, e.g.:

```
Generated Java files for Laurel in ./generated/com/example/laurel
```

## Usage from Lean

```lean
import Strata.DDM.Integration.Java.Gen

open Strata.Java

-- Obtain a Dialect value. The CLI builds one via DialectFileMap;
-- see the javaGenCommand in StrataMain.lean for the full pattern.
-- Here we assume `myDialect : Strata.Dialect` is already loaded.

let files ← IO.ofExcept (generateDialect myDialect "com.example.mypackage")
writeJavaFiles "./generated" "com.example.mypackage" files
```

`generateDialect` returns `Except String GeneratedFiles`, failing if the
dialect contains unsupported declarations. `writeJavaFiles` creates the
package directory structure and writes all files.

## Generated Files

For a dialect named `MyDialect` in package `com.example.mydialect`, the
generator produces the following files under `com/example/mydialect/`:

| File | Description |
|------|-------------|
| `SourceRange.java` | Source location record |
| `Node.java` | Root sealed interface for all AST nodes |
| `IonSerializer.java` | Serializer from AST nodes to Ion s-expressions |
| `MyDialect.java` | Static factory methods for building AST nodes |
| One `.java` per category | Sealed interface grouping related operators |
| One `.java` per operator | Record class implementing its category interface |

Additionally, for categories referenced by the dialect but not defined in
it (e.g., `Init.Expr`), the generator emits non-sealed stub interfaces.

## Core Types

### `SourceRange`

```java
public record SourceRange(long start, long stop) {
    public static final SourceRange NONE = new SourceRange(0, 0);
}
```

Every AST node carries a `SourceRange`. Use `SourceRange.NONE` when source
location information is not available.

### `Node`

```java
public sealed interface Node {
    SourceRange sourceRange();
    java.lang.String operationName();
}
```

The root of the AST type hierarchy. All category interfaces extend `Node`,
and all operator records implement a category interface. The `permits`
clause on `Node` is populated with every generated interface.

`operationName()` returns the fully qualified DDM operator name
(e.g., `"MyDialect.myOp"`).

## Category Interfaces

Each DDM syntactic category that has at least one operator becomes a
**sealed interface** extending `Node`. The `permits` clause lists all
operator records belonging to that category.

```java
// Example: a category "Stmt" with operators Assign and Return
public sealed interface Stmt extends Node permits Assign, Return {}
```

Categories referenced by operator arguments but not defined in the current
dialect (e.g., `Init.Expr`, `Init.Type`) become **non-sealed stub
interfaces**:

```java
public non-sealed interface Expr extends Node {}
```

This allows users to provide their own implementations for cross-dialect
extension points.

## Operator Records

Each DDM operator becomes a Java `record` that implements its category
interface. The record always has `sourceRange` as its first component,
followed by one component per operator argument.

```java
// For an operator: op assign(target : Init.Ident, value : Expr) : Stmt
public record Assign(
    SourceRange sourceRange,
    java.lang.String target,
    Expr value
) implements Stmt {
    @Override
    public java.lang.String operationName() { return "MyDialect.assign"; }
}
```

## Type Mapping

DDM argument types map to Java types as follows:

| DDM Type | Java Type |
|----------|-----------|
| `Init.Ident` | `java.lang.String` |
| `Init.Str` | `java.lang.String` |
| `Init.Num` | `java.math.BigInteger` |
| `Init.Decimal` | `java.math.BigDecimal` |
| `Init.Bool` | `boolean` |
| `Init.ByteArray` | `byte[]` |
| `Init.Option T` | `java.util.Optional<T>` |
| `Init.Seq T`, `Init.CommaSepBy T`, etc. | `java.util.List<T>` |
| `Init.Expr` (abstract) | `Expr` (stub interface) |
| `Init.Type` (abstract) | `Type_` (stub interface) |
| `Init.TypeP` (abstract) | `TypeP` (stub interface) |
| Type expressions (`:type T`) | `Expr` (stub interface) |
| Dialect-defined category | Generated sealed interface |

## Factory Class (Builders)

A static factory class is generated with the dialect's name. It provides
two overloads per operator:

1. **With `SourceRange`** — first parameter is the source range.
2. **Without `SourceRange`** — uses `SourceRange.NONE` automatically.

```java
public class MyDialect {
    // With explicit source range
    public static Stmt assign(SourceRange sourceRange, java.lang.String target, Expr value) {
        return new Assign(sourceRange, target, value);
    }

    // Convenience overload
    public static Stmt assign(java.lang.String target, Expr value) {
        return new Assign(SourceRange.NONE, target, value);
    }
}
```

### Numeric Convenience

For `Init.Num` arguments, the factory accepts `long` instead of
`BigInteger` and converts internally. A runtime check rejects negative
values:

```java
public static MyCategory myOp(long count) {
    if (count < 0) throw new IllegalArgumentException("count must be non-negative");
    return new MyOp(SourceRange.NONE, java.math.BigInteger.valueOf(count));
}
```

For `Init.Decimal` arguments, the factory accepts `double` and converts
via `BigDecimal.valueOf`.

## Ion Serializer

`IonSerializer` converts AST nodes into the Ion format that other DDM-generated
code (including the core Lean implementation of Strata) can read. It requires an
Amazon Ion `IonSystem` instance.

```java
IonSystem ion = IonSystemBuilder.standard().build();
IonSerializer serializer = new IonSerializer(ion);
```

### Methods

| Method | Description |
|--------|-------------|
| `serializeCommand(Node)` | Serialize a top-level command (no `op` wrapper) |
| `serialize(Node)` | Serialize a node as an argument (wrapped in `(op ...)`) |

### Serialization Format

The serializer produces Ion expressions matching Strata's internal
representation:

- **Operators**: `(Dialect.opName <sourceRange> <arg1> <arg2> ...)`
- **Arguments (nested nodes)**: `(op (Dialect.opName <sourceRange> ...))`
- **Identifiers and strings**: `(ident null "name")` — both `Init.Ident`
  and `Init.Str` serialize in this form
- **Numbers**: `(num null <bigint>)`
- **Decimals**: `(decimal null <decimal>)`
- **Booleans**: `(op (Init.boolTrue null))` or `(op (Init.boolFalse null))`
- **Byte arrays**: `(bytes null <blob>)`
- **Optionals**: `(option null)` (empty) or `(option null <value>)` (present)
- **Lists**: `(<separator> null <item1> <item2> ...)` where `<separator>` is one of:
  - `seq` — `Init.Seq`
  - `commaSepList` — `Init.CommaSepBy`
  - `spaceSepList` — `Init.SpaceSepBy`
  - `spacePrefixedList` — `Init.SpacePrefixSepBy`
  - `newlineSepList` — `Init.NewlineSepBy`
  - `semicolonSepList` — `Init.SemicolonSepBy`
- **Source ranges**: `(<start> <stop>)` or `null` for `SourceRange.NONE`

The correct list separator for each operator field is determined at
generation time from the DDM category and embedded in a static lookup
table inside `IonSerializer`.

## Name Disambiguation

The generator avoids name collisions through several mechanisms:

1. **Java reserved words** — a trailing `_` is appended (e.g., `class` → `class_`).
2. **Base class names** — `Node`, `SourceRange`, and `IonSerializer` are reserved.
3. **Cross-dialect collisions** — when two categories share the same short name,
   the dialect name is prefixed in PascalCase (e.g., `LambdaExpr` vs `CoreExpr`).
4. **Operator/category collisions** — a numeric suffix is added if needed.
5. **Invalid characters** — non-alphanumeric characters (e.g., `?`) are stripped.
6. **Common `java.lang` classes** — names like `String`, `Object`, `Integer`, etc.
   are escaped to avoid ambiguity with implicit imports.

All names are converted to PascalCase. Disambiguation is case-insensitive
to avoid collisions on case-insensitive file systems.

## Limitations

- **Type declarations** (`type` in DDM) are not supported and cause an error.
- **Function declarations** (`function` in DDM) are not supported and cause an error.
- Only operator declarations (`op`) are processed.

## Implementation

The generator lives in `Strata/DDM/Integration/Java/Gen.lean`.
