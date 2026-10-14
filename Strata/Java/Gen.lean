/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public meta import Init.Data.String.Legacy
public import StrataDDM.Util.Decimal
-- The language-neutral half of this generator (shape analysis, name
-- disambiguation) is shared with the Go backend in `Strata.Go.Gen`. The import
-- must be `public` because the term elaborator below is a `public meta def` and
-- calls into it.
public meta import Strata.CodeGen.TypeShape

open Lean Meta Elab Term
open Strata.CodeGen

/-!
# Java Code Generator for Lean Types

`getIonSerializer%` is a term-level elaborator that inspects Lean inductive and
structure types at compile time and generates Java source code consisting of:

- A sealed interface hierarchy mirroring the Lean type
- Records for each constructor / structure
- Ion serialization methods using the same format as `getIonDeserializer%`

## Ion encoding conventions (matching `getIonDeserializer%`)

| Lean type | Ion encoding |
|-----------|-------------|
| Structures | Ion struct with field names as keys |
| Single-constructor inductives | Ion struct with positional keys `_0`, `_1`, … |
| Multi-constructor inductives | Ion sexp `(ConstructorName arg₁ arg₂ …)` |

## Supported leaf types

`Nat`, `Int`, `Float`, `String`, `Bool`, `Decimal`

## Container types

`List α` → `java.util.List<T>`, `Option α` → `java.util.Optional<T>`
-/

namespace Strata.Java

/-! ## All generated Java source files. -/

public structure GeneratedFiles where
  files : Array (String × String)  -- (filename, content)
  deriving Inhabited

public def writeJavaFiles (baseDir : System.FilePath) (package : String)
    (files : GeneratedFiles) : IO Unit := do
  let parts := package.splitOn "."
  let dir := parts.foldl (init := baseDir) (· / ·)
  IO.FS.createDirAll dir
  for (filename, content) in files.files do
    IO.FS.writeFile (dir / filename) content

/-! ## Name Utilities -/

private meta def javaReservedWords : Std.HashSet String := Std.HashSet.ofList [
  "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
  "class", "const", "continue", "default", "do", "double", "else", "enum",
  "extends", "final", "finally", "float", "for", "goto", "if", "implements",
  "import", "instanceof", "int", "interface", "long", "native", "new",
  "package", "private", "protected", "public", "return", "short", "static",
  "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
  "transient", "try", "void", "volatile", "while",
  "exports", "module", "open", "opens", "permits", "provides",
  "record", "sealed", "to", "transitive", "uses", "var", "when", "with", "yield",
  "true", "false", "null", "_",
  "String", "Object", "Integer", "Boolean", "Long", "Double", "Float",
  "Character", "Byte", "Short"
]

private meta def escapeJavaName (name : String) : String :=
  let cleaned := String.ofList (name.toList.filter (fun c => c.isAlphanum || c == '_'))
  let cleaned := if cleaned.isEmpty then "field" else cleaned
  if javaReservedWords.contains cleaned then cleaned ++ "_" else cleaned

/--
The Java class name for a Lean type, and the single source of truth for it: the
emitted filename and every field-type reference derive from this, so they cannot
disagree.

A trailing `?` is rendered as an `Opt` suffix rather than dropped. `escapeJavaName`
strips non-alphanumerics, so `Laurel.Parameter?` would otherwise fold onto
`Laurel.Parameter` — two distinct Lean types (the second's `type` field is an
`Option`) collapsing to one `Parameter.java`, where the last one generated silently
overwrote the other.
-/
private meta def javaClassName (typeName : Name) : String :=
  let base := typeName.getString!
  let (stem, suffix) :=
    if base.endsWith "?" then (base.dropEnd 1 |>.toString, "Opt") else (base, "")
  escapeJavaName (toPascalCase stem ++ suffix)

/-! ## Leaf type mapping -/

private meta def leafJavaType (name : Name) : Option String :=
  match name with
  | ``Nat => some "long"
  | ``Int => some "long"
  | ``Float => some "double"
  | ``String => some "java.lang.String"
  | ``Bool => some "boolean"
  | ``StrataDDM.Decimal => some "java.math.BigDecimal"
  | _ => none

private meta def leafSerializeExpr (name : Name) (accessor : String) : Option String :=
  match name with
  | ``Nat => some s!"ion.newInt({accessor})"
  | ``Int => some s!"ion.newInt({accessor})"
  | ``Float => some s!"ion.newFloat({accessor})"
  | ``String => some s!"ion.newString({accessor})"
  | ``Bool => some s!"ion.newBool({accessor})"
  | ``StrataDDM.Decimal => some s!"ion.newDecimal({accessor})"
  | _ => none

/-! ## Java Code Generation -/

private meta partial def javaTypeForInfo : FieldTypeInfo → String
  | .leaf name => (leafJavaType name).getD "java.lang.Object"
  | .compound name typeArgs =>
    let base := javaClassName name
    if typeArgs.isEmpty then base
    else s!"{base}<{", ".intercalate (typeArgs.toList.map javaBoxedTypeForInfo)}>"
  | .typeParam paramName => paramName
  | .list elem => s!"java.util.List<{javaBoxedTypeForInfo elem}>"
  | .option elem => s!"java.util.Optional<{javaBoxedTypeForInfo elem}>"
where
  javaBoxedTypeForInfo : FieldTypeInfo → String
    | .leaf ``Nat | .leaf ``Int => "Long"
    | .leaf ``Float => "Double"
    | .leaf ``Bool => "Boolean"
    | .leaf ``StrataDDM.Decimal => "java.math.BigDecimal"
    | .leaf ``String => "java.lang.String"
    | other => javaTypeForInfo other

private meta def javaTypeFor (f : FieldShape) : String := javaTypeForInfo f.typeInfo

/-- Serialize `accessor` to an `IonValue` expression. `depth` distinguishes the
lambda parameters introduced for nested lists, which would otherwise shadow the
enclosing binder and fail to compile. -/
private meta partial def serializeExprForInfo (ti : FieldTypeInfo) (accessor : String)
    (depth : Nat := 0) : String :=
  match ti with
  | .leaf name => (leafSerializeExpr name accessor).getD "ion.newNull()"
  | .compound _ _ => s!"{accessor}.toIon(ion)"
  | .typeParam _ => s!"{accessor}.toIon(ion)"
  | .list elem =>
    -- Build the Ion list inline: `java.util.List` has no `toIon`, so nested
    -- containers (e.g. `Option (List T)`, `List (List T)`) need this form.
    let v := s!"_e{depth}"
    let inner := serializeExprForInfo elem v (depth + 1)
    s!"ion.newList({accessor}.stream().<com.amazon.ion.IonValue>map({v} -> {inner}).toList())"
  | .option elem =>
    let inner := serializeExprForInfo elem s!"{accessor}.get()" depth
    s!"({accessor}.isPresent() ? {inner} : ion.newNull())"

private meta def serializeExprFor (f : FieldShape) (accessor : String) : String :=
  serializeExprForInfo f.typeInfo accessor

/--
The Java identifier to use for each field, by position, with collisions resolved.

Two Lean field names can escape to one Java identifier (see `disambiguate`), which
would emit a record with duplicate components. This is deterministic in the field
array alone, so every site that needs a field's identifier — the record
parameter list and each `toIon` body — derives the same answer without threading
state between them.

Only the Java-side identifier changes; the Ion key stays `f.name` (or the
positional `_0`/`_1`), so disambiguation never perturbs the wire format.
-/
private meta def fieldIdents (fields : Array FieldShape) : Array String :=
  (disambiguateAll (fields.toList.map fun f => escapeJavaName f.name)).toArray

private meta def recordParams (fields : Array FieldShape) : String :=
  let idents := fieldIdents fields
  ", ".intercalate ((fields.toList.zip idents.toList).map fun (field, ident) =>
    s!"{javaTypeFor field} {ident}")

private meta def typeParamDecl (typeParams : Array String) : String :=
  if typeParams.isEmpty then ""
  else s!"<{", ".intercalate (typeParams.toList.map fun p => s!"{p} extends ToIon")}>"

private meta def typeParamUse (typeParams : Array String) : String :=
  if typeParams.isEmpty then ""
  else s!"<{", ".intercalate typeParams.toList}>"

/-- Generate the toIon method body for a struct (Ion struct with field name keys). -/
private meta def structToIonBody (fields : Array FieldShape) : String :=
  let idents := fieldIdents fields
  let fieldLines := (fields.toList.zip idents.toList).flatMap fun (f, ident) =>
    let accessor := s!"{ident}()"
    match f.typeInfo with
    | .list elem =>
      let inner := serializeExprForInfo elem "e" (depth := 1)
      [s!"        var _l_{ident} = ion.newEmptyList();",
       s!"        for (var e : {accessor}) _l_{ident}.add({inner});",
       s!"        s.put(\"{f.name}\", _l_{ident});"]
    | _ =>
      [s!"        s.put(\"{f.name}\", {serializeExprFor f accessor});"]
  s!"        var s = ion.newEmptyStruct();\n{"\n".intercalate fieldLines}\n        return s;"

/-- Generate the toIon method body for a single-ctor inductive (Ion struct with _0, _1, ... keys). -/
private meta def singleCtorToIonBody (fields : Array FieldShape) : String :=
  let idents := fieldIdents fields
  let fieldLines := (fields.toList.zip idents.toList).zipIdx.flatMap fun ((f, ident), i) =>
    let accessor := s!"{ident}()"
    match f.typeInfo with
    | .list elem =>
      let inner := serializeExprForInfo elem "e" (depth := 1)
      [s!"        var _l{i} = ion.newEmptyList();",
       s!"        for (var e : {accessor}) _l{i}.add({inner});",
       s!"        s.put(\"_{i}\", _l{i});"]
    | _ =>
      [s!"        s.put(\"_{i}\", {serializeExprFor f accessor});"]
  s!"        var s = ion.newEmptyStruct();\n{"\n".intercalate fieldLines}\n        return s;"

private meta def multiCtorToIonBody (shortName : String) (fields : Array FieldShape) : String :=
  let idents := fieldIdents fields
  let fieldLines := (fields.toList.zip idents.toList).zipIdx.flatMap fun ((f, ident), i) =>
    let accessor := s!"{ident}()"
    match f.typeInfo with
    | .list elem =>
      let inner := serializeExprForInfo elem "e" (depth := 1)
      [s!"        var _l{i} = ion.newEmptyList();",
       s!"        for (var e : {accessor}) _l{i}.add({inner});",
       s!"        sexp.add(_l{i});"]
    | _ =>
      [s!"        sexp.add({serializeExprFor f accessor});"]
  s!"        var sexp = ion.newEmptySexp();\n        sexp.add(ion.newSymbol(\"{shortName}\"));\n{"\n".intercalate fieldLines}\n        return sexp;"

private meta def generateRecord (interfaceName : String) (recordName : String)
    (fields : Array FieldShape) (toIonBody : String) (tpDecl : String := "") : String :=
  let params := recordParams fields
  s!"    public record {recordName}{tpDecl}({params}) implements {interfaceName} \{
        @Override
        public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIonBody}
        }
    }"

private meta def generateTypeFile (package : String) (shape : TypeShape) : String :=
  match shape with
  | .struct typeName fields typeParams =>
    let javaName := javaClassName typeName
    let toIon := structToIonBody fields
    let params := recordParams fields
    let tpDecl := typeParamDecl typeParams
    s!"package {package};

public record {javaName}{tpDecl}({params}) implements ToIon \{
    public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIon}
    }
}
"
  | .singleCtor typeName ctor typeParams =>
    let javaName := javaClassName typeName
    let toIon := singleCtorToIonBody ctor.fields
    let params := recordParams ctor.fields
    let tpDecl := typeParamDecl typeParams
    s!"package {package};

public record {javaName}{tpDecl}({params}) implements ToIon \{
    public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIon}
    }
}
"
  | .multiCtor typeName ctors typeParams =>
    let javaName := javaClassName typeName
    let tpDecl := typeParamDecl typeParams
    let tpUse := typeParamUse typeParams
    -- Names are disambiguated once, up front, so the `permits` clause and the
    -- record definitions below cannot disagree about a renamed constructor.
    let recNames := disambiguateAll
      (ctors.toList.map fun ctor => escapeJavaName (toPascalCase ctor.shortName))
    let recordDefs := (ctors.toList.zip recNames).map fun (ctor, recName) =>
      -- The Ion tag stays `ctor.shortName`: renaming is a Java-identifier
      -- concern and must not change the wire encoding.
      let toIon := multiCtorToIonBody ctor.shortName ctor.fields
      generateRecord (s!"{javaName}{tpUse}") recName ctor.fields toIon tpDecl
    -- A zero-constructor inductive has nothing to permit. Both `sealed` and
    -- `permits` have to go in that case: `permits` with an empty list is not
    -- valid Java, and a `sealed` interface with no permitted subtype is
    -- rejected too (`sealed class must have subclasses`). Dropping only
    -- `permits` would swap one uncompilable form for another.
    let sealedKw := if recNames.isEmpty then "" else "sealed "
    let permits := if recNames.isEmpty then ""
      else " permits " ++ ", ".intercalate (recNames.map fun n => s!"{javaName}.{n}")
    s!"package {package};

public {sealedKw}interface {javaName}{tpDecl} extends ToIon{permits} \{
    com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion);

{"\n\n".intercalate recordDefs}
}
"

private meta def generateForType (env : Environment) (package : String) (rootName : Name) :
    MetaM GeneratedFiles := do
  let nestedTypes ← collectNestedTypes env rootName
  let mut files := #[]
  -- Emit the ToIon interface used by type-parameter fields
  let toIonInterface := s!"package {package};\n\npublic interface ToIon \{\n    com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion);\n}\n"
  files := files.push ("ToIon.java", toIonInterface)
  -- Guard against two Lean types mapping to one Java file. `writeJavaFiles`
  -- just loops `IO.FS.writeFile`, so a duplicate would silently overwrite the
  -- earlier one and emit a tree that disagrees with the Lean AST. Fail at
  -- generation time instead, naming both culprits.
  let mut seen : Std.HashMap String Name := {}
  for typeName in nestedTypes do
    let shape ← analyzeType env typeName
    let fileName := s!"{javaClassName typeName}.java"
    if let some prior := seen[fileName]? then
      throwError "getIonSerializer%: {prior} and {typeName} both map to \
                  '{fileName}'. Rename one of the Lean types, or extend \
                  `javaClassName` to distinguish them."
    seen := seen.insert fileName typeName
    let content := generateTypeFile package shape
    files := files.push (fileName, content)
  return { files }

/-! ## Elaborator -/

public section

/--
`getIonSerializer%` generates Java source files for a Lean type.
The result has type `Strata.Java.GeneratedFiles`.

Usage: `getIonSerializer% MyType "com.example.pkg"`
-/
syntax (name := getIonSerializerStx) "getIonSerializer%" ident str : term

@[term_elab getIonSerializerStx]
meta def getIonSerializerElab : TermElab := fun stx _expectedType? => do
  match stx with
  | `(getIonSerializer% $typeId $pkgStr) => do
    let typeName ← resolveGlobalConstNoOverload typeId
    let env ← getEnv
    let package := pkgStr.getString
    let result ← generateForType env package typeName
    let filesArr ← result.files.mapM fun (name, content) => do
      let nameLit : TSyntax `str := ⟨Syntax.mkStrLit name⟩
      let contentLit : TSyntax `str := ⟨Syntax.mkStrLit content⟩
      `(($nameLit, $contentLit))
    let arrStx ← `(#[$[$filesArr],*])
    let resultStx ← `(Strata.Java.GeneratedFiles.mk $arrStx)
    elabTerm resultStx _expectedType?
  | _ => throwUnsupportedSyntax

end

end Strata.Java
