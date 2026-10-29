# Laurel Go Code Generator

The `getIonGoSerializer%` elaborator generates Go types and schema-specific
`MarshalIon` methods from Lean declarations. Generated types implement
`github.com/amazon-ion/ion-go/ion.Marshaler`; ion-go owns the binary format,
symbol tables, and writer state machine.

This is the Go counterpart of [`DDMJavaCodeGen.md`](DDMJavaCodeGen.md). Both
backends share the shape analysis in `Strata/CodeGen/TypeShape.lean` and
delegate Ion serialization to the standard library for their target language:
IonJava for Java and ion-go for Go.

## Usage from the CLI

The `laurelGoGen` executable generates the Laurel AST package:

```text
lake exe laurelGoGen <go-package-name> <output-dir>
```

For example:

```bash
lake exe laurelGoGen laurel ../gofrontend/laurel
```

The generated Go module must depend on ion-go:

```bash
go get github.com/amazon-ion/ion-go/ion
```

## Usage from Lean

```lean
import Strata.Go.Gen

open Strata.Go

def myFiles : GeneratedFiles := getIonGoSerializer% MyType "mypkg"

#eval writeGoFiles "./generated" myFiles
```

## Emitted files

A Go package is a directory, so every file lands directly in `output-dir`.

| File | Content |
|------|---------|
| `ion_value.go` | ion-go aliases, the `Decimal` mirror, integer constructors, and checked writer helpers |
| `ion_binary.go` | the `MarshalBinary` convenience wrapper around `ion.NewBinaryWriter` |
| `opt.go` | the `Opt` helper for populating optional fields |
| `<GoTypeName>.go` | one file per Lean type in the reachable closure |

The first three files are a small adapter maintained as ordinary Go source under
`Strata/Go/runtime`. `Strata/Go/GoIonRuntime.lean` embeds those templates at Lean
compile time and substitutes the requested package name when generating output.
They do not implement an Ion DOM or binary encoder.

## Ion encoding conventions

| Lean type | Ion encoding |
|-----------|--------------|
| Structure | struct with the Lean field names as keys |
| Single-constructor inductive | struct with positional keys `_0`, `_1`, ... |
| Multi-constructor inductive | sexp `(ConstructorName arg₁ arg₂ ...)` |

Generated methods write these representations directly through `ion.Writer`.
Compatibility tests marshal compiled Go values and decode them with
`getIonDeserializer%`; they intentionally do not require a particular valid Ion
binary layout.

## Type mapping

| Lean type | Go type |
|-----------|---------|
| `Nat` | `*big.Int` |
| `Int` | `*big.Int` |
| `Float` | `float64` |
| `String` | `string` |
| `Bool` | `bool` |
| `StrataDDM.Decimal` | `Decimal` |
| `List α` | `[]α` |
| `Option α` | `*α` |
| Type parameter `T` | `T` constrained by `ToIon` |
| Compound type | generated struct or interface implementing `ion.Marshaler` |

A generated type parameter is constrained by `ToIon`, so a *type argument* has to
be another generated type or a type parameter.

Everything else is rejected at generation time, with an error naming the generic
type, because Go would otherwise reject the emitted package:

| Lean type argument | Go | Why it fails |
|---|---|---|
| `Nat`, `String`, … | `Box[*big.Int]` | no method set |
| `List α` | `Box[[]Point]` | a slice has no method set |
| `Option` of a structure or single-constructor type | `Box[*Point]` | `none` is a nil `*Point`, which the generic body cannot write as Ion null |
| `Option` of a multi-constructor type | `Box[*Shape]` | pointer to interface, not interface |
| `Option` of a type parameter | `Box[*T]` | pointer to type parameter, not type parameter |
| `Option (Option α)` | `Box[**Point]` | pointer to pointer |

`Option` is therefore never a type argument (Java refuses it too, since
`Optional` is not `ToIon`). Wrap it in a structure instead: a field
`Option Point` inside a monomorphic wrapper writes `none` as Ion null.

### Integers

Lean `Nat` and `Int` are arbitrary precision, so both map to `*math/big.Int`.
The adapter provides constructors for common call sites:

| Constructor | Use |
|-------------|-----|
| `IntLit(int64)` | ordinary signed literals |
| `UintLit(uint64)` | the upper half of the `uint64` range |
| `ParseIntLit(string)` | literals beyond machine integer widths |

A nil `*big.Int` is a programming error and is reported rather than silently
encoded as zero. A negative `Nat` is also rejected at marshal time, with the
field or container path included in the error. Because `Option Int` adds another
pointer, its Go type is `**big.Int`; `Opt(IntLit(3))` constructs a present value.

### Option

`none` is written as an Ion null at every level of nesting, and
`getIonDeserializer%` decodes any Ion null back to `none`. `Option (Option α)` is
therefore **lossy**: `some none` and `none` produce the same bytes and cannot be
told apart on decode. This is a property of the Ion encoding rather than of the
Go backend — the Java backend has the identical hole — so changing it means
changing the generated Go, `getIonDeserializer%`, and the Java backend together.
`TestGen.lean` pins the current behaviour with a byte comparison.

### Decimal

ion-go represents decimal coefficients with `*big.Int` and exponents with
`int32`, so the generated mirror is:

```go
type Decimal struct {
    Mantissa *big.Int
    Exponent int32
}
```

For example:

```go
Decimal{Mantissa: IntLit(314), Exponent: -2} // 3.14
```

The adapter rejects a nil mantissa. It also rejects `math.MinInt32` as an
exponent because ion-go stores the negated exponent internally and that one
value cannot be negated in `int32`.

## Marshaling API

Every generated concrete type implements:

```go
func (v Point) MarshalIon(w IonWriter) error
```

`IonWriter` is an alias of `ion.Writer`, and `ToIon` is an alias of
`ion.Marshaler`. Callers may therefore use either ion-go directly or the
generated convenience wrapper:

```go
bytes, err := MarshalBinary(point)
```

Lists, options, nested generated values, struct field names, and constructor
symbols are all streamed to the same writer. Writer and validation failures are
annotated with the generated field/list/constructor path. Nil interface values
and typed nil pointers are returned as path-annotated errors before their
`MarshalIon` method can panic.

## Naming

Generated type and field names are PascalCased and exported. Ion field names
remain the original Lean names, so Go identifier escaping does not alter the
wire schema.

A Lean type ending in `?` receives an `Opt` suffix. Names that collide with Go
keywords, predeclared identifiers, imports, or declarations in the shared
adapter receive a `_` suffix.

Type parameters are escaped too. They occupy ordinary Go scope and must not
capture adapter names such as `IonWriter`, `Decimal`, or `ToIon`.

### Flat package namespace

Go has no nested types. Each constructor of a multi-constructor inductive is
therefore a top-level struct, such as `StmtExprBlock`. The generator checks all
generated type and constructor-struct names in one package-wide registry.
Cross-type collisions are reported as errors rather than silently renamed.

### Sealed interfaces

A multi-constructor inductive becomes an interface containing the marshaler
method and an unexported marker:

```go
type Shape interface {
    MarshalIon(w IonWriter) error
    isShape()
}
```

The marker prevents implementations outside the generated package. A
zero-constructor inductive becomes the same interface with no implementing
structs.

For a generic inductive the marker returns a pointer to each type parameter, so
a constructor is tied to the interface's type argument (the counterpart of
Java's `implements Holder<T>`):

```go
type Holder[T ToIon] interface {
    MarshalIon(w IonWriter) error
    isHolder() *T
}

func (HolderFull[T]) isHolder() *T { return nil }
```

Without it no method would mention `T`, and `HolderFull[Line]` would satisfy
`Holder[Point]`.

## Implementation and tests

The generator is in `Strata/Go/Gen.lean`, the ion-go adapter sources under
`Strata/Go/runtime`, their Lean embedding in `Strata/Go/GoIonRuntime.lean`, and
the shared shape analysis in `Strata/CodeGen/TypeShape.lean`. The Laurel CLI is
`StrataLaurel/Scripts/LaurelGoGen.lean`.

Tests require generated source to be `gofmt`-clean, pass `go vet`, compile from
a separate consumer package, and round-trip through the Lean deserializer. The
Go checks skip with a warning in local development without Go, but fail inside a
Brazil build or when `CI` is set.
