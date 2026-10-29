/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public meta import Init.Data.String.Legacy
public import StrataDDM.Util.Decimal
-- Shape analysis is shared with the Java backend. `public` because the term
-- elaborator below is a `public meta def` that calls into it.
public meta import Strata.CodeGen.TypeShape
-- The three embedded Go support templates, which `generateForType` prepends to the
-- per-type files so the emitted directory is a compilable Go package.
public meta import Strata.Go.GoIonRuntime
public import Strata.Go.GoIonRuntime

open Lean Meta Elab Term
open Strata.CodeGen

/-!
# Go Code Generator for Lean Types

`getIonGoSerializer%` is a term-level elaborator that inspects Lean inductive and
structure types at compile time and generates Go source code consisting of:

- An interface per multi-constructor inductive, with a struct per constructor
- A struct per Lean structure / single-constructor inductive
- `MarshalIon` methods implementing ion-go's `ion.Marshaler`

The shape analysis lives in `Strata.CodeGen.TypeShape` and is shared with
`Strata.Java.Gen`; only naming, type mapping and emission are here.

## Ion encoding conventions (matching `getIonDeserializer%`)

| Lean type | Ion encoding |
|-----------|-------------|
| Structures | Ion struct with field names as keys |
| Single-constructor inductives | Ion struct with positional keys `_0`, `_1`, … |
| Multi-constructor inductives | Ion sexp `(ConstructorName arg₁ arg₂ …)` |

## Supported leaf types

`Nat`, `Int`, `Float`, `String`, `Bool`, `Decimal`. `Nat` and `Int` are
arbitrary-precision in Lean and map to `*math/big.Int`, not to a machine integer
— see `leafGoType`.

## Container types

`List α` → `[]T`, `Option α` → `*T` (`nil` is the absent case)

## How this differs from the Java backend

Three Go facts drive every structural difference, and each is explained at the
declaration it affects:

- **Go has no nested types.** Java nests each constructor record inside its
  sealed interface, so `StmtExpr.Block` and `Variable.Block` coexist. Here they
  become the top-level `StmtExprBlock` and `VariableBlock`, so generated type
  names and constructor struct names have to be checked against each other across
  the whole package — see `registerGoName`. Method names are *not* part of that
  namespace and are not checked there.
- **Go has no expression-level `map` and no ternary.** Serializing a `List` needs
  a `for`, an `Option` needs an `if`; both are statements, so field emission
  produces statement blocks — see `writeInfo`.
- **Go has no built-in arbitrary-precision integer.** Java's `long` is wide
  enough for the values Strata's front-ends use in practice but not for the ones
  the Lean types admit, and Go can do better: `Nat` and `Int` map to
  `*math/big.Int` — see `leafGoType`. This is the one thing that makes a generated
  file carry an `import`, which `generateTypeFile` emits conditionally.
- **Go exports by capitalisation.** Every generated type and field name is
  PascalCased so a consumer in another package can use it, which `escapeGoName`
  enforces as a postcondition rather than leaving to `toPascalCase`; the Ion keys
  stay the original Lean names — see `fieldIdents`. The one deliberately
  *unexported* name is the `is<Type>` marker method, which is what seals the
  interface.

## Emitted files

One directory, because a Go package *is* a directory: the three fixed runtime
files (`ion_value.go`, `ion_binary.go`, `opt.go`) plus one `<GoTypeName>.go` per
Lean type in the closure. `writeGoFiles` does no package-path nesting; that is a
Java-ism.
-/

namespace Strata.Go

/-! ## All generated Go source files. -/

public structure GeneratedFiles where
  files : Array (String × String)  -- (filename, content)
  deriving Inhabited

/--
Write every generated file into `dir`.

Flat, unlike `Strata.Java.writeJavaFiles`: a Go package is a single directory, so
there is no package path to mirror on disk and the Go package name appears only
in each file's `package` clause.
-/
public def writeGoFiles (dir : System.FilePath) (files : GeneratedFiles) : IO Unit := do
  IO.FS.createDirAll dir
  for (filename, content) in files.files do
    IO.FS.writeFile (dir / filename) content

/-! ## Name Utilities -/

/--
Identifiers a generated name must not take. Three groups, each for a different
reason:

* **Keywords** cannot be identifiers at all.
* **Predeclared identifiers** (`string`, `error`, `len`, …) live in the universe
  block, so redeclaring one is legal but shadows it for the rest of the package —
  a generated type named `error` would quietly change what `error` means in the
  fixed runtime files.
* **Every package-scope name the fixed support files declare.** Generated code and
  support files share one Go package, so a Lean type named `Decimal` or `IonWriter`
  would be a redeclaration, not a shadow, and would not compile.

That third group is **not** written out here. It comes from
`Strata.Go.GoIonRuntime.packageScopeNames`, which scans the runtime source for
its own declarations, so the reserved set is derived from the source it protects.
`GenSmokeTest.lean`'s `#testReservedNameGate` checks the derivation with an
independent scanner.

`OptOf` is reserved although nothing declares it: it is the name a generically
typed companion to `opt.go`'s `Opt` would take, so holding it back now costs
nothing and keeps adding one from breaking a package that already generates a
type by that name. `big` is reserved for the `math/big`
import that a file with an `Int` or `Nat` field carries — file scope rather than
package scope, but a name in scope nonetheless.

Two of the groups are, given `escapeGoName`'s capitalisation step, belt and
braces rather than required: an escaped name always begins with an uppercase
ASCII letter, so it can never equal a keyword, a predeclared identifier or one of
the runtime's unexported helpers, all of which are lowercase. They are kept so the
set stays correct on its own terms if that invariant is ever relaxed.

Reserving the runtime names also keeps the generated *filenames* clear of
`ion_value.go`, `ion_binary.go` and `opt.go`: `toPascalCase` deletes underscores,
so a generated name can only contain one via a `disambiguate` suffix, and `Opt`
itself is among the reserved names.
-/
private meta def goReservedWords : Std.HashSet String := Std.HashSet.ofList (goKeywords ++ [
  -- Predeclared types, constants and functions.
  "any", "bool", "byte", "comparable", "complex64", "complex128", "error",
  "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune",
  "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr",
  "true", "false", "iota", "nil",
  "append", "cap", "clear", "close", "complex", "copy", "delete", "imag",
  "len", "make", "max", "min", "new", "panic", "print", "println", "real",
  "recover",
  -- Held back although undeclared, plus the one import the generator emits and
  -- the method name every generated type carries; see the docstring.
  "OptOf", "big", "MarshalIon"
] ++ packageScopeNames.toList)

/--
Make `name` usable as an **exported** Go identifier.

Four steps: strip everything Go does not allow in an identifier, fall back to
`Field` if that leaves nothing, force the result to begin with an uppercase ASCII
letter, and append `_` on a clash with `goReservedWords`.

The capitalisation step is not cosmetic, and it is not covered by the
`toPascalCase` that callers apply first. `toPascalCase` upcases the head of each
`_`-separated segment, but the strip runs *afterwards* and can remove that head:
Lean accepts `«$bar»` as a field name, which PascalCases to `$bar` and strips to
`bar` — an *unexported* Go identifier, which a consumer in another package cannot
set. `«σ»` strips to nothing at all, since `Char.isAlphanum` is ASCII-only. The
same step subsumes the leading-digit case (`«2x»` → `X2x`, because `2x` is not a
Go identifier) and an underscore head (`«_x»` → `X_x`, because `_x` is
unexported).

Capitalising *before* the reserved-word check is deliberate: the check then sees
the final spelling, which is what actually has to avoid a clash. It is also what
makes the lowercase halves of `goReservedWords` unreachable — see there.
-/
private meta def escapeGoName (name : String) : String :=
  let cleaned := String.ofList (name.toList.filter (fun c => c.isAlphanum || c == '_'))
  let cleaned := if cleaned.isEmpty then "Field" else cleaned
  let cleaned := match cleaned.toList with
    -- `c` is ASCII here, the strip having removed everything else, so
    -- `Char.isAlpha`'s ASCII-only behaviour is exactly the test wanted.
    | c :: cs => if c.isAlpha then String.ofList (c.toUpper :: cs) else "X" ++ cleaned
    | [] => cleaned
  if goReservedWords.contains cleaned then cleaned ++ "_" else cleaned

/--
Whether `name` is one of the identifiers `escapeGoName` refuses to emit.

Public only so that `StrataTestExtra/Languages/Go/GenSmokeTest.lean` can gate the
reserved set against the names `Strata.Go.GoIonRuntime`'s files actually declare.
Nothing in the generator calls it.
-/
public meta def isReservedGoName (name : String) : Bool := goReservedWords.contains name

/--
The Go type name for a Lean type, and the single source of truth for it: the
emitted filename, every field-type reference and every constructor struct name
derive from this, so they cannot disagree.

A trailing `?` is rendered as an `Opt` suffix rather than dropped, for the same
reason as `Strata.Java.javaClassName`: `escapeGoName` strips non-alphanumerics,
so `Laurel.Parameter?` would otherwise fold onto `Laurel.Parameter` — two
distinct Lean types (the second's `type` field is an `Option`) collapsing to one
`Parameter.go`, where the last one generated silently overwrote the other.
-/
private meta def goTypeName (typeName : Name) : String :=
  let base := typeName.getString!
  let (stem, suffix) :=
    if base.endsWith "?" then (base.dropEnd 1 |>.toString, "Opt") else (base, "")
  escapeGoName (toPascalCase stem ++ suffix)

/--
Render `s` as a Go interpreted string literal.

Ion keys and sexp tags are raw Lean names, and Lean accepts anything inside
`«…»` — including `"` and control characters — so the quoting has to be real.
-/
private meta def goStringLit (s : String) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  let escapeChar (c : Char) : String :=
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c =>
      -- Anything else printable, including multi-byte UTF-8, goes through as is:
      -- a Go interpreted string literal is UTF-8 source text.
      if c.toNat < 0x20 || c.toNat == 0x7f then
        String.ofList ['\\', 'x', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
      else c.toString
  "\"" ++ (s.toList.foldl (init := "") fun acc c => acc ++ escapeChar c) ++ "\""

/-! ## Leaf type mapping -/

/--
`Nat` and `Int` both map to `*big.Int`, because both are **arbitrary precision**
in Lean. This lets a Go front-end express every value admitted by the mirrored
Lean field, including integer literals outside the `int64` and `uint64` ranges.

The generated marshaler passes `Int` values to ion-go's `Writer.WriteBigInt`.
A checked `Nat` adapter additionally rejects negative values, since no Lean
`Nat` could have produced them. Both adapters reject nil rather than allowing
the writer to dereference it. `GoIonRuntime`'s
`IntLit`/`UintLit`/`ParseIntLit` keep common construction sites concise.

The **Java backend deliberately keeps `long`**: its own suite is written against
`long`, and it has no front-end with this problem to solve. The two backends are
free to disagree because
`Strata.CodeGen.TypeShape` deliberately carries no target-language type.

`Decimal` needs no entry beyond the mirror type below. Its mantissa remains
arbitrary precision, while its exponent is `int32`, matching ion-go's public
decimal representation.
-/
private meta def leafGoType (name : Name) : Option String :=
  match name with
  | ``Nat | ``Int => some "*big.Int"
  | ``Float => some "float64"
  | ``String => some "string"
  | ``Bool => some "bool"
  | ``StrataDDM.Decimal => some "Decimal"
  | _ => none

/-- Return the Go representation of a supported leaf or reject the field type. -/
private meta def requireLeafGoType (name : Name) : MetaM String := do
  if let some goType := leafGoType name then return goType
  throwError "getIonGoSerializer%: unsupported scalar field type '{name}'. \
              Supported scalar types are Nat, Int, Float, String, Bool, and \
              StrataDDM.Decimal."

/-- The ion-go writer call that serializes a leaf-typed `accessor`. -/
private meta def leafWriteCall (name : Name) (accessor : String) : MetaM String := do
  match name with
  | ``Nat => return s!"writeNat(w, {accessor})"
  | ``Int => return s!"writeBigInt(w, {accessor})"
  | ``Float => return s!"w.WriteFloat({accessor})"
  | ``String => return s!"writeString(w, {accessor})"
  | ``Bool => return s!"w.WriteBool({accessor})"
  | ``StrataDDM.Decimal => return s!"writeDecimal(w, {accessor})"
  | _ =>
    throwError "getIonGoSerializer%: unsupported scalar field type '{name}'. \
                Supported scalar types are Nat, Int, Float, String, Bool, and \
                StrataDDM.Decimal."

/-! ## Go type mapping -/

/--
Whether the Go type for `ti` satisfies the `ToIon` constraint that
`goTypeParams` puts on every generated type parameter — i.e. whether `ti` is
usable as a Go type *argument* at all.

A generated struct, a generated interface and a type parameter all do: the first
declares `MarshalIon` on a value receiver, the second has it in the interface,
and the third carries the constraint by construction. A leaf does not — it maps
to `*big.Int`, `float64`, `string`, `bool` or `Decimal` — and neither does a
`List`, which maps to a Go slice.

`Option` is never allowed. A generic body writes its `T`-typed field through
`MarshalIon` and cannot know that this instantiation is an `Option`, so
`Box (Option Point)` → `Box[*Point]` would compile and then refuse to encode
`none` (a nil `*Point` is a nil value, not an Ion null). Every other `Option`
is rejected by Go as well — `*Shape` is a pointer to an interface, `*T` a pointer
to a type parameter, `**Point` has an empty method set — so one rule covers them
all, the same one Java applies because `Optional` is not `ToIon`.
-/
private meta def satisfiesToIon : FieldTypeInfo → Bool
  | .leaf _ => false
  | .compound _ _ => true
  | .typeParam _ => true
  | .list _ => false
  | .option _ => false

/--
The Go type for a field.

`Option α` becomes `*α` because a nil pointer is the only "absent" Go has
without inventing a wrapper type; `opt.go`'s `Opt` helper makes populating one a
one-liner. Unlike Java there is no boxed/unboxed split to bridge (`List<Long>`
versus `long`), so one recursive function covers every position.

Type arguments are checked against `satisfiesToIon` before being rendered.
`Box Nat` would otherwise emit `Box[*big.Int]`, which is accepted here and then
rejected by the Go compiler — `*big.Int does not satisfy ToIon (missing method
MarshalIon)` — so the user would meet the problem as a build error in generated
code rather than as a message naming the Lean field. Rejecting it here is the
same treatment `requireLeafGoType` gives an unsupported scalar.
-/
private meta partial def goTypeForInfo : FieldTypeInfo → MetaM String
  | .leaf name => requireLeafGoType name
  | .compound name typeArgs => do
    let base := goTypeName name
    if typeArgs.isEmpty then return base
    for arg in typeArgs do
      unless satisfiesToIon arg do
        throwError "getIonGoSerializer%: '{name}' is applied to a type argument \
                    whose Go type cannot satisfy the `ToIon` constraint on a \
                    generated type parameter. A type argument may be another \
                    generated type or a type parameter. It may not be a scalar \
                    or a `List` (neither has a `MarshalIon` method), nor an \
                    `Option` (the generic body cannot write its `none` as an \
                    Ion null). Wrap the argument in a structure, or replace \
                    '{name}' with a monomorphic type."
    let args ← typeArgs.toList.mapM goTypeForInfo
    return s!"{base}[{", ".intercalate args}]"
  | .typeParam paramName => return paramName
  | .list elem => return s!"[]{← goTypeForInfo elem}"
  | .option elem => return s!"*{← goTypeForInfo elem}"

/-- Render one writer call with uniform path-aware error handling. -/
private meta def checkedWrite (call indent path : String) : List String :=
  [s!"{indent}if err := {call}; err != nil \{",
   s!"{indent}\treturn atPath(err, {path})",
   indent ++ "}"]

/-- Reject nil interface and typed-pointer values before invoking `MarshalIon`. -/
private meta def checkedMarshal (accessor indent path : String) : List String :=
  [s!"{indent}if isNilIonMarshaler({accessor}) \{",
   s!"{indent}\treturn atPath(errNilValue, {path})",
   indent ++ "}"] ++
  checkedWrite s!"{accessor}.MarshalIon(w)" indent path

/--
Statements that write `accessor` through the method's ion-go writer.

Containers recurse directly into the writer instead of first constructing a
parallel Ion value tree. `path` is a Go string expression used only when a
writer or validation error must be reported.
-/
private meta partial def writeInfo (ti : FieldTypeInfo) (accessor path : String)
    (indent : String) (listDepth : Nat := 0) (optDepth : Nat := 0) :
    MetaM (List String) := do
  match ti with
  | .leaf name => return checkedWrite (← leafWriteCall name accessor) indent path
  | .compound _ _ | .typeParam _ =>
    return checkedMarshal accessor indent path
  | .list elem =>
    let i := s!"_i{listDepth}"
    let e := s!"_e{listDepth}"
    let innerPath := s!"indexPath({path}, {i})"
    let inner ← writeInfo elem e innerPath (indent ++ "\t") (listDepth + 1) optDepth
    return checkedWrite "w.BeginList()" indent path ++
      [s!"{indent}for {i}, {e} := range {accessor} \{"] ++ inner ++
      [indent ++ "}"] ++ checkedWrite "w.EndList()" indent path
  | .option elem =>
    let p := s!"_p{optDepth}"
    let inner ← writeInfo elem p path (indent ++ "\t") listDepth (optDepth + 1)
    return [s!"{indent}if {accessor} == nil \{"] ++
      checkedWrite "w.WriteNull()" (indent ++ "\t") path ++
      [indent ++ "} else {", s!"{indent}\t{p} := *{accessor}"] ++ inner ++
      [indent ++ "}"]

/-! ## Go declarations -/

/--
The Go identifier to use for each field, by position, with collisions resolved.

Fields are PascalCased, i.e. **exported**, so that a consumer living in a
different Go package can construct and read these structs. The Ion key is
untouched — it stays the Lean field name, or the positional `_0`/`_1` — so
capitalising and disambiguating never perturb the wire format.

Capitalising makes collisions *more* likely than in Java, not less: `myField`
and `MyField` both fold to `MyField`, as do `my_field` and `myField`. As in
Java this is deterministic in the field array alone, so every site that needs a
field's identifier — the struct declaration and the `MarshalIon` body — derives
the same answer without threading state between them.
-/
private meta def fieldIdents (fields : Array FieldShape) : Array String :=
  (disambiguateAll (fields.toList.map fun f => escapeGoName (toPascalCase f.name))).toArray

/--
`type <name><tpDecl> struct { … }`.

Field declarations are padded to a common column because gofmt aligns a
contiguous run of them — for *every* run, with no width heuristic that would let
a one-space version through. Emitting a single space would make `gofmt -l`
report the file. Zero- and one-field structs use gofmt's single-line form.
-/
private meta def goStructDecl (name : String) (tpDecl : String) (fields : Array FieldShape) :
    MetaM String := do
  let idents := fieldIdents fields
  let decls ← (fields.toList.zip idents.toList).mapM fun (field, ident) => do
    return (ident, ← goTypeForInfo field.typeInfo)
  match decls with
  | [] => return s!"type {name}{tpDecl} struct\{}"
  | [(n, t)] => return s!"type {name}{tpDecl} struct\{ {n} {t} }"
  | _ =>
    let width := decls.foldl (fun w (n, _) => max w n.length) 0
    let lines := decls.map fun (n, t) => "\t" ++ n ++ ("".pushn ' ' (width - n.length)) ++ " " ++ t
    return s!"type {name}{tpDecl} struct \{\n{"\n".intercalate lines}\n}"

/--
The Go names for a type's parameters, plus the map from Lean name to Go name.

A type parameter is an ordinary Go identifier declared in ordinary Go scope, so
it has to be escaped like every other generated name. Skipping the escape lets a
Lean parameter **capture a runtime name**: `structure Box (ionWriter : Type)`
would declare `Box[IonWriter ToIon]`, and inside that scope the `IonWriter` in
`MarshalIon(IonWriter)` resolves to the parameter rather than to the writer
alias. A parameter named `decimal` is worse — it
compiles far enough to make a sibling field of type `StrataDDM.Decimal` silently
mean the parameter.

This is Go-specific. Java's emitted signature is fully qualified
(`com.amazon.ion.IonValue toIon(…)`), so a Java type variable cannot capture it,
which is why the shared `CodeGen.extractCtorFields` leaves `paramNames`
unescaped and this backend escapes on the way out.

`disambiguateAll` is necessary here. Escaping is what makes it necessary:
`Char.isAlphanum` is ASCII-only, so
`escapeGoName` strips a Greek letter to nothing and falls back to `Field`. That
means `structure Pair (α β : Type)` — entirely idiomatic Lean, and far more
likely in practice than the `ionValue` capture this escaping exists to prevent —
folds *both* parameters onto `Field`, and `[Field ToIon, Field ToIon]` does not
compile.
-/
private meta def goTypeParams (typeParams : Array String) :
    Array String × Std.HashMap String String :=
  let escaped := (disambiguateAll (typeParams.toList.map escapeGoName)).toArray
  let rename := (typeParams.zip escaped).foldl (init := ∅)
    fun m (leanName, goName) => m.insert leanName goName
  (escaped, rename)

/--
Rewrite every `.typeParam` payload to the Go name `goTypeParams` chose.

Done once, up front, on the field list rather than threaded through
`goTypeForInfo` and its callers: the declaration site and every *use* site must
agree, and rewriting the shape guarantees that by construction. Escaping in
`typeParamDecl` but not in `goTypeForInfo` would be worse than not escaping at
all, because the two spellings would then disagree.

The fallback covers `classifyFieldType`'s untagged `.typeParam "T"` case, which
is not in the declared parameter list.
-/
private meta partial def renameTypeParamsInfo (rename : Std.HashMap String String) :
    FieldTypeInfo → FieldTypeInfo
  | .leaf n => .leaf n
  | .compound n typeArgs => .compound n (typeArgs.map (renameTypeParamsInfo rename))
  | .typeParam p => .typeParam (rename.getD p (escapeGoName p))
  | .list elem => .list (renameTypeParamsInfo rename elem)
  | .option elem => .option (renameTypeParamsInfo rename elem)

/-- `renameTypeParamsInfo` lifted over a field list. -/
private meta def renameTypeParamsFields (rename : Std.HashMap String String)
    (fields : Array FieldShape) : Array FieldShape :=
  fields.map fun f => { f with typeInfo := renameTypeParamsInfo rename f.typeInfo }

/-- `[T ToIon, U ToIon]`. Constraining every Lean type parameter by `ToIon` is
what lets a field of parameter type be serialized with `.MarshalIon(w)`. Takes
the already-escaped names from `goTypeParams`. -/
private meta def typeParamDecl (typeParams : Array String) : String :=
  if typeParams.isEmpty then ""
  else s!"[{", ".intercalate (typeParams.toList.map fun p => s!"{p} ToIon")}]"

/-- `[T, U]`: the parameter list as written in a receiver or a type reference.
Takes the already-escaped names from `goTypeParams`. -/
private meta def typeParamUse (typeParams : Array String) : String :=
  if typeParams.isEmpty then ""
  else s!"[{", ".intercalate typeParams.toList}]"

/--
The body of a `MarshalIon` method that writes an Ion struct. `keyFor` supplies
the original Lean field name for a structure or `_i` for a single-constructor
inductive.
-/
private meta def structLikeMarshalBody (fields : Array FieldShape)
    (keyFor : Nat → FieldShape → String) : MetaM String := do
  let idents := fieldIdents fields
  let mut lines := checkedWrite "w.BeginStruct()" "\t" "\"\""
  for ((f, ident), i) in (fields.toList.zip idents.toList).zipIdx do
    let key := keyFor i f
    let path := goStringLit key
    lines := lines ++ checkedWrite s!"fieldName(w, {path})" "\t" path
    lines := lines ++ (← writeInfo f.typeInfo s!"v.{ident}" path "\t")
  lines := lines ++ checkedWrite "w.EndStruct()" "\t" "\"\"" ++ ["\treturn nil"]
  return "\n".intercalate lines

/-- The body of a `MarshalIon` method that writes an Ion sexp tagged with the
constructor's short name. -/
private meta def sexpMarshalBody (shortName : String) (fields : Array FieldShape) :
    MetaM String := do
  let idents := fieldIdents fields
  let tag := goStringLit shortName
  let mut lines := checkedWrite "w.BeginSexp()" "\t" "\"\""
  lines := lines ++ checkedWrite s!"writeSymbol(w, {tag})" "\t" tag
  for ((f, ident), i) in (fields.toList.zip idents.toList).zipIdx do
    let path := s!"sexpPath({tag}, {i + 1})"
    lines := lines ++ (← writeInfo f.typeInfo s!"v.{ident}" path "\t")
  lines := lines ++ checkedWrite "w.EndSexp()" "\t" "\"\"" ++ ["\treturn nil"]
  return "\n".intercalate lines

/-- Every generated file opens with this. The `DO NOT EDIT` line is the
conventional marker that tooling looks for. -/
private meta def goFileHeader (package : String) : String :=
  s!"{generatedGoFileMarker}\n\npackage {package}\n"

/--
Whether the Go type for `ti` mentions `big.Int`, and so whether the file
declaring it has to import `math/big`.

Computed from the *shape* rather than by scanning the rendered text, because a
Lean field may legitimately be named `«big.Int»` and a false positive is not
cosmetic: Go rejects an unused import, so the file would stop compiling.

`.compound` recurses into its type arguments for completeness, not because a
reachable shape needs it: `goTypeForInfo` rejects any type argument that cannot
satisfy `ToIon`, which rules out every argument that bottoms out in a leaf. The
recursion costs nothing and keeps the predicate correct on its own terms if that
check is ever loosened.
-/
private meta partial def usesBigInt : FieldTypeInfo → Bool
  | .leaf name => name == ``Nat || name == ``Int
  | .compound _ typeArgs => typeArgs.any usesBigInt
  | .typeParam _ => false
  | .list elem => usesBigInt elem
  | .option elem => usesBigInt elem

/-- `usesBigInt` over every field of every constructor of a shape. -/
private meta def shapeUsesBigInt : TypeShape → Bool
  | .struct _ fields _ => fields.any (usesBigInt ·.typeInfo)
  | .singleCtor _ ctor _ => ctor.fields.any (usesBigInt ·.typeInfo)
  | .multiCtor _ ctors _ => ctors.any fun c => c.fields.any (usesBigInt ·.typeInfo)

/--
The whole `<GoTypeName>.go` file for one Lean type.

`ctorStructNames` is supplied by `generateForType` rather than recomputed here,
because that is where the package-wide registry lives: the names the registry
reserved and the names written into the file must be the same ones.

Type parameters are escaped once here, via `goTypeParams`, and the field shapes
are rewritten to match before anything is rendered — see `renameTypeParamsInfo`
for why the declaration and the uses cannot be allowed to drift apart.

Receivers are **value** receivers throughout. The `ToIon` constraint on a type
parameter is satisfied by a type whose method set contains `MarshalIon`, and a
value type's method set only contains its value-receiver methods — so
`AstNode[Point]` would not compile if `Point.MarshalIon` took a pointer receiver.
-/
private meta def generateTypeFile (package : String) (shape : TypeShape)
    (ctorStructNames : Array String) : MetaM String := do
  -- Go rejects unused imports, so include `math/big` only when this type needs it.
  let imports := if shapeUsesBigInt shape then "import \"math/big\"\n\n" else ""
  let render (sections : List String) : String :=
    goFileHeader package ++ "\n" ++ imports ++ "\n\n".intercalate sections ++ "\n"
  match shape with
  | .struct typeName rawFields typeParams =>
    let name := goTypeName typeName
    let (tps, rename) := goTypeParams typeParams
    let fields := renameTypeParamsFields rename rawFields
    let tpDecl := typeParamDecl tps
    let tpUse := typeParamUse tps
    let structDecl ← goStructDecl name tpDecl fields
    let body ← structLikeMarshalBody fields (fun _ f => f.name)
    return render [structDecl,
      s!"func (v {name}{tpUse}) MarshalIon(w IonWriter) error \{\n\
         {body}\n}"]
  | .singleCtor typeName ctor typeParams =>
    let name := goTypeName typeName
    let (tps, rename) := goTypeParams typeParams
    let fields := renameTypeParamsFields rename ctor.fields
    let tpDecl := typeParamDecl tps
    let tpUse := typeParamUse tps
    let structDecl ← goStructDecl name tpDecl fields
    let body ← structLikeMarshalBody fields (fun i _ => s!"_{i}")
    return render [structDecl,
      s!"func (v {name}{tpUse}) MarshalIon(w IonWriter) error \{\n\
         {body}\n}"]
  | .multiCtor typeName ctors typeParams =>
    let name := goTypeName typeName
    let (tps, rename) := goTypeParams typeParams
    let tpDecl := typeParamDecl tps
    let tpUse := typeParamUse tps
    -- The unexported marker method is what makes the interface effectively
    -- sealed: only this package can implement it. It is the Go counterpart of
    -- Java's `sealed … permits`, and unlike `permits` it needs no special case
    -- for a zero-constructor inductive — an interface with no implementor is
    -- legal Go, and nothing can construct it, which is the correct meaning.
    --
    -- A generic marker returns a pointer to every type parameter. Without that no
    -- method mentions them, so `HolderFull[Line]` would satisfy `Holder[Point]`
    -- and marshal a `Line` where Lean expects a `Point`; Java closes the same
    -- hole with `implements Holder<T>`.
    let (markerResult, markerBody) := match tps.toList with
      | [] => ("", "{}")
      | [tp] => (s!" *{tp}", "{ return nil }")
      | tps => (s!" ({", ".intercalate (tps.map (s!"*{·}"))})",
                s!"\{ return {", ".intercalate (tps.map fun _ => "nil")} }")
    let marker := s!"is{name}"
    let interfaceDecl :=
      s!"type {name}{tpDecl} interface \{\n\tMarshalIon(w IonWriter) error\n\t\
         {marker}(){markerResult}\n}"
    let mut ctorDefs : List String := []
    for (ctor, structName) in ctors.toList.zip ctorStructNames.toList do
      let fields := renameTypeParamsFields rename ctor.fields
      let structDecl ← goStructDecl structName tpDecl fields
      let body ← sexpMarshalBody ctor.shortName fields
      ctorDefs := ctorDefs ++ [structDecl,
        s!"func ({structName}{tpUse}) {marker}(){markerResult} {markerBody}",
        s!"func (v {structName}{tpUse}) MarshalIon(w IonWriter) error \{\n{body}\n}"]
    return render (interfaceDecl :: ctorDefs)

/-! ## Package-wide name registry -/

/-- What a generated Go identifier came from, so a collision can name both
culprits. -/
private inductive NameOrigin where
  | typeDecl (leanType : Name)
  | ctorStruct (leanType : Name) (ctor : Name)

private meta def NameOrigin.describe : NameOrigin → String
  | .typeDecl t => s!"the type generated for '{t}'"
  | .ctorStruct t c => s!"the constructor struct generated for '{c}' of '{t}'"

/--
Claim `name` in the package-wide registry, failing if something else has it.

Java gets away with a per-file check because it nests each constructor record
inside its sealed interface, so `StmtExpr.Block` and `Variable.Block` coexist.
Go has no nested types: those become the top-level `StmtExprBlock` and
`VariableBlock`, so every generated type and every constructor struct in the
closure lands in one flat namespace. The check is therefore package-wide, not
per-file.

The registry holds **type and constructor-struct names only**. The `is<Type>`
marker is *not* registered, even though it is generated here too: a Go method
name lives in its receiver's method set, never in package scope, so `func (FooA)
isFoo()` and a separate `type IsFoo struct{…}` coexist. Distinct type names also
imply distinct `is<Type>` marker names, so the package-scope registry has no role
in checking them.

Nor does the marker need a narrower check. It can only clash inside its own
receiver's method set, against that struct's fields or its one other method, and
both are ruled out by construction: `escapeGoName` makes every field identifier
start with an uppercase letter while a marker starts with a lowercase `is`, and a
field that would fold onto `ToIon` is caught by `goReservedWords`.

Collisions are *reported*, not silently suffixed. Suffixing is right within one
type's constructor list and within one struct's field list (see
`CodeGen.disambiguate`): those lists are order-stable, so the renaming is stable
too. Across different Lean types it is not — the closure order comes from
`collectNestedTypes`, and adding an unrelated field elsewhere could reorder it
and silently rename a Go struct that callers already reference. A hard error at
generation time, naming both culprits, is the honest outcome.

Comparison is case-insensitive, matching `CodeGen.disambiguate`: Go identifiers
differing only in case are confusable, and each generated type is also a file on
a possibly case-insensitive filesystem.
-/
private meta def registerGoName (registry : Std.HashMap String NameOrigin) (name : String)
    (origin : NameOrigin) : MetaM (Std.HashMap String NameOrigin) := do
  let key := name.toLower
  if let some prior := registry[key]? then
    throwError "getIonGoSerializer%: the Go name '{name}' is claimed by both \
                {prior.describe} and {origin.describe}. Go has no nested types, \
                so a constructor struct is named '<Type><Constructor>' at \
                package scope and can collide with an unrelated declaration. \
                Rename one of the Lean declarations."
  return registry.insert key origin

/--
Generate the whole Go package for `rootName`'s closure.

The fixed support files come first so the ion-go adapter they define is written
even when the closure is empty.
-/
private meta def generateForType (env : Environment) (package : String) (rootName : Name) :
    MetaM GeneratedFiles := do
  unless isValidGoPackageName package do
    throwError "getIonGoSerializer%: '{package}' is not a valid Go package name. \
                It must be a Go identifier: a letter or underscore followed by \
                letters, digits or underscores, and not a keyword."
  let nestedTypes ← collectNestedTypes env rootName
  let mut files := runtimeFiles package
  let mut registry : Std.HashMap String NameOrigin := {}
  for typeName in nestedTypes do
    let shape ← analyzeType env typeName
    let goName := goTypeName typeName
    registry := ← registerGoName registry goName (.typeDecl typeName)
    let mut ctorStructNames : Array String := #[]
    if let .multiCtor _ ctors _ := shape then
      -- Disambiguated once, up front, so the struct definitions and the
      -- registry cannot disagree about a renamed constructor. This pass is
      -- local to the type; `registerGoName` then checks the results against
      -- the rest of the package.
      let localNames := disambiguateAll
        (ctors.toList.map fun ctor => escapeGoName (goName ++ toPascalCase ctor.shortName))
      for (ctor, structName) in ctors.toList.zip localNames do
        registry := ← registerGoName registry structName (.ctorStruct typeName ctor.name)
        ctorStructNames := ctorStructNames.push structName
    files := files.push (s!"{goName}.go", ← generateTypeFile package shape ctorStructNames)
  return { files }

/-! ## Elaborator -/

public section

/--
`getIonGoSerializer%` generates Go source files for a Lean type.
The result has type `Strata.Go.GeneratedFiles`.

Usage: `getIonGoSerializer% MyType "mypkg"`
-/
syntax (name := getIonGoSerializerStx) "getIonGoSerializer%" ident str : term

@[term_elab getIonGoSerializerStx]
meta def getIonGoSerializerElab : TermElab := fun stx _expectedType? => do
  match stx with
  | `(getIonGoSerializer% $typeId $pkgStr) => do
    let typeName ← resolveGlobalConstNoOverload typeId
    let env ← getEnv
    let package := pkgStr.getString
    let result ← generateForType env package typeName
    let filesArr ← result.files.mapM fun (name, content) => do
      let nameLit : TSyntax `str := ⟨Syntax.mkStrLit name⟩
      let contentLit : TSyntax `str := ⟨Syntax.mkStrLit content⟩
      `(($nameLit, $contentLit))
    let arrStx ← `(#[$[$filesArr],*])
    let resultStx ← `(Strata.Go.GeneratedFiles.mk $arrStx)
    elabTerm resultStx _expectedType?
  | _ => throwUnsupportedSyntax

end

end Strata.Go
