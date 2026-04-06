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
strata javaGen StrataTest/DDM/Integration/Java/testdata/Simple.dialect.st com.example.simple ./generated
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
| `IonSerializer.java` | Serialization helpers for converting AST nodes to Ion |
| `MyDialect.java` | Static factory methods for building AST nodes |
| One `.java` per category | Sealed interface with nested operator records |

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
location information is not available. The `start` and `stop` values are
byte offsets into the source file. Note that `SourceRange.NONE` (0, 0)
is indistinguishable from a zero-length range at byte offset 0.

### `Node`

```java
import com.amazon.ion.IonSexp;

public sealed interface Node permits Stmt, Expr, ... {
    SourceRange sourceRange();
    java.lang.String operationName();
    IonSexp toIon(IonSerializer $s);
}
```

The root of the AST type hierarchy. All category interfaces extend `Node`,
and all operator records implement a category interface. The `permits`
clause lists every generated category interface and stub interface.

`operationName()` returns the fully qualified DDM operator name
(e.g., `"MyDialect.myOp"`).

`toIon()` serializes the node to Ion format using the provided
`IonSerializer` helpers. This method is generated for each operator record
with field-specific serialization logic.

`Node` requires `com.amazon.ion:ion-java` as a compile-time dependency.

## Category Interfaces and Nested Records

Each DDM syntactic category becomes a **sealed interface** extending
`Node`, with its operator records defined as **nested types** within the
interface. This mirrors the DDM structure where operators belong to
categories.

```java
// Category "Stmt" with operators Assign and Return
public sealed interface Stmt extends Node permits Stmt.Assign, Stmt.Return {
    public record Assign(
        SourceRange sourceRange,
        java.lang.String target, Expr value
    ) implements Stmt {
        @Override public java.lang.String operationName() { return "MyDialect.assign"; }
        @Override public com.amazon.ion.IonSexp toIon(IonSerializer $s) { ... }
    }

    public record Return(
        SourceRange sourceRange,
        Expr value
    ) implements Stmt {
        @Override public java.lang.String operationName() { return "MyDialect.return"; }
        @Override public com.amazon.ion.IonSexp toIon(IonSerializer $s) { ... }
    }
}
```

Usage:

```java
var assign = new Stmt.Assign(SourceRange.NONE, "x", someExpr);
var ret = new Stmt.Return(SourceRange.NONE, someExpr);
List<Stmt> stmts = List.of(assign, ret);
```

### Naming Rules

When a **single-operator category** has an operator whose name matches the
category name (e.g., `category Parameter` with `op parameter`), the record
is named `Of` to avoid a collision with the enclosing interface:

```java
public sealed interface Parameter extends Node permits Parameter.Of {
    public record Of(SourceRange sourceRange, ...) implements Parameter { ... }
}
// Usage: new Parameter.Of(SourceRange.NONE, name, type)
```

When a **multi-operator category** has an operator whose name matches the
category name (compared case-insensitively), the record gets a `_` suffix:

```java
public sealed interface Procedure extends Node permits Procedure.Procedure_, Procedure.Function {
    public record Procedure_(...) implements Procedure { ... }
    public record Function(...) implements Procedure { ... }
}
```

### Stub Interfaces

Categories referenced by operator arguments but not defined in the current
dialect (e.g., `Init.Expr`, `Init.Type`) become **non-sealed stub
interfaces**:

```java
public non-sealed interface Expr extends Node {}
```

This allows users to provide their own implementations for cross-dialect
extension points.

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
| `Init.Seq T` | `java.util.List<T>` |
| `Init.CommaSepBy T` | `java.util.List<T>` |
| `Init.SpaceSepBy T` | `java.util.List<T>` |
| `Init.SpacePrefixSepBy T` | `java.util.List<T>` |
| `Init.NewlineSepBy T` | `java.util.List<T>` |
| `Init.SemicolonSepBy T` | `java.util.List<T>` |
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
    public static Stmt assign(SourceRange sourceRange, java.lang.String target, Expr value) {
        return new Stmt.Assign(sourceRange, target, value);
    }

    public static Stmt assign(java.lang.String target, Expr value) {
        return new Stmt.Assign(SourceRange.NONE, target, value);
    }
}
```

Factory method names preserve the original DDM operator name (with
reserved word escaping), while record and interface names use PascalCase.

### Numeric Convenience

For `Init.Num` arguments, the factory accepts `long` instead of
`BigInteger` and converts internally. A runtime check rejects negative
values. Values larger than `Long.MAX_VALUE` can be created by constructing
the record directly with `BigInteger`.

For `Init.Decimal` arguments, the factory accepts `double` and converts
via `BigDecimal.valueOf`. The `double` type has limited precision (~15-17
significant digits); for higher precision, construct the record directly
with `BigDecimal`.

## Ion Serializer

`IonSerializer` provides helper methods for converting AST nodes to Ion
format. Each generated record has a `toIon` method that uses these helpers
to serialize its fields with the correct Ion format.

Requires `com.amazon.ion:ion-java` as a runtime dependency.

```java
IonSystem ion = IonSystemBuilder.standard().build();
IonSerializer serializer = new IonSerializer(ion);
```

### Methods

| Method | Description |
|--------|-------------|
| `serializeCommand(Node)` | Serialize a top-level command (no `op` wrapper) |
| `serialize(Node)` | Serialize a node as an argument (wrapped in `(op ...)`) |

### Multi-file Format

When serializing multiple source files (e.g., for a multi-file Java
project), the convention is to wrap each file's program in a struct with
`filePath` and `program` fields, collected into an Ion list:

```java
IonList files = ion.newEmptyList();
for (var sourceFile : sourceFiles) {
    IonStruct entry = ion.newEmptyStruct();
    entry.put("filePath", ion.newString(sourceFile.path()));

    IonList program = ion.newEmptyList();
    IonSexp header = ion.newEmptySexp();
    header.add(ion.newSymbol("program"));
    header.add(ion.newString("Laurel"));
    program.add(header);
    for (var command : sourceFile.commands()) {
        program.add(serializer.serializeCommand(command));
    }
    entry.put("program", program);
    files.add(entry);
}
```

Each program starts with a header s-expression `(program "DialectName")`.

### Serialization Format

The serializer produces Ion expressions matching Strata's internal
representation:

- **Operators**: `(Dialect.opName <sourceRange> <arg1> <arg2> ...)`
- **Arguments (nested nodes)**: `(op (Dialect.opName <sourceRange> ...))`
- **Identifiers** (`Init.Ident`): `(ident null "name")`
- **String literals** (`Init.Str`): `(strlit null "value")`
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

The correct serialization method for each field is determined at generation
time from the DDM type and embedded directly in the record's `toIon`
method.

## Name Disambiguation

The generator avoids name collisions through several mechanisms:

1. **Java reserved words** — a trailing `_` is appended (e.g., `class` → `class_`).
   Applied after stripping invalid characters.
2. **Base class names** — `Node`, `SourceRange`, and `IonSerializer` are reserved.
3. **Cross-dialect collisions** — when two categories share the same short name,
   the dialect name is prefixed in PascalCase (e.g., `LambdaExpr` vs `CoreExpr`).
4. **Operator/category collisions** — for single-operator categories where the
   operator name matches the category name, the record is named `Of`. For
   multi-operator categories, a `_` suffix is added, then `_2`, `_3`, etc.
   for further collisions.
5. **Invalid characters** — non-alphanumeric characters (except `_`) are stripped.
   If stripping produces an empty name, it defaults to `field`.
6. **Common `java.lang` classes** — names like `String`, `Object`, `Integer`, etc.
   are escaped to avoid ambiguity with implicit imports.

Record and interface names are converted to PascalCase. Factory method
names preserve the original operator name (not PascalCased).
Disambiguation is case-insensitive to avoid collisions on case-insensitive
file systems.

Operator names are scoped within their category (since records are nested),
so the same operator name can appear in different categories without
collision.

## Limitations

- **Type declarations** (`type` in DDM) are not supported and cause an error.
- **Function declarations** (`function` in DDM) are not supported and cause an error.
- `syncat` and `metadata` declarations are accepted but do not produce output.
- Only operator declarations (`op`) are processed.

## Implementation

The generator lives in `Strata/DDM/Integration/Java/Gen.lean`.
