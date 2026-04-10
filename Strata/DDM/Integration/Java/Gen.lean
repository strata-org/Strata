/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public meta import Init.Data.String.Legacy

open Lean Meta Elab Term

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

`Nat`, `Int`, `Float`, `String`, `Bool`
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

private meta def toPascalCase (s : String) : String :=
  s.splitOn "_"
  |>.filter (!·.isEmpty)
  |>.map (fun part => match part.toList with
    | [] => ""
    | c :: cs => .ofList (c.toUpper :: cs))
  |> String.intercalate ""

/-! ## Leaf type detection and mapping -/

private meta def isLeafTypeName (name : Name) : Bool :=
  name == ``Nat || name == ``Int || name == ``String || name == ``Bool || name == ``Float

private meta def leafJavaType (name : Name) : Option String :=
  match name with
  | ``Nat => some "long"
  | ``Int => some "long"
  | ``Float => some "double"
  | ``String => some "java.lang.String"
  | ``Bool => some "boolean"
  | _ => none

private meta def leafSerializeExpr (name : Name) (accessor : String) : Option String :=
  match name with
  | ``Nat => some s!"ion.newInt({accessor})"
  | ``Int => some s!"ion.newInt({accessor})"
  | ``Float => some s!"ion.newFloat({accessor})"
  | ``String => some s!"ion.newString({accessor})"
  | ``Bool => some s!"ion.newBool({accessor})"
  | _ => none

/-! ## Type info extraction -/

private structure FieldInfo where
  name : String
  typeName : Name
  isCompound : Bool

private meta instance : Inhabited FieldInfo := ⟨{ name := "", typeName := `unknown, isCompound := false }⟩

private structure CtorInfo' where
  name : Name
  shortName : String
  fields : Array FieldInfo

private meta instance : Inhabited CtorInfo' := ⟨{ name := `unknown, shortName := "", fields := #[] }⟩

private inductive TypeShape where
  | struct (name : Name) (javaName : String) (fields : Array FieldInfo)
  | singleCtor (name : Name) (javaName : String) (ctor : CtorInfo')
  | multiCtor (name : Name) (javaName : String) (ctors : Array CtorInfo')

private meta def isCompoundType (env : Environment) (name : Name) : Bool :=
  !isLeafTypeName name &&
    ((getStructureInfo? env name).isSome ||
      match env.find? name with | some (.inductInfo _) => true | _ => false)

private meta def getFieldTypeName (ty : Expr) : MetaM Name := do
  let origName := ty.getAppFn.constName?
  let ty ← whnf ty
  let name := origName <|> ty.getAppFn.constName?
  return name.getD `unknown

private meta def extractCtorFields (env : Environment) (ctorName : Name)
    (fieldNames? : Option (Array Name) := none) : MetaM (Array FieldInfo) := do
  let some (.ctorInfo ci) := env.find? ctorName
    | throwError "Cannot find constructor {ctorName}"
  let mut ty := ci.type
  for _ in List.range ci.numParams do
    match ty with | .forallE _ _ b _ => ty := b | _ => break
  let mut fields := #[]
  for i in List.range ci.numFields do
    match ty with
    | .forallE n t b _ =>
      let typeName ← getFieldTypeName t
      let name := match fieldNames? with
        | some names => names[i]!.toString (escape := false)
        | none =>
          -- Use actual binder name for Java record fields
          let s := n.toString (escape := false)
          if s.startsWith "_" && s.length > 1 then s!"field{i}" else s
      fields := fields.push { name, typeName, isCompound := isCompoundType env typeName }
      ty := b
    | _ => break
  return fields

private meta def analyzeType (env : Environment) (typeName : Name) : MetaM TypeShape := do
  let javaName := escapeJavaName (toPascalCase (typeName.getString!))
  if let some sinfo := getStructureInfo? env typeName then
    let fields ← extractCtorFields env (sinfo.structName ++ `mk) (some sinfo.fieldNames)
    return .struct typeName javaName fields
  let some (.inductInfo indInfo) := env.find? typeName
    | throwError "{typeName} is not an inductive or structure type"
  let ctors ← indInfo.ctors.toArray.mapM fun ctorName => do
    let fields ← extractCtorFields env ctorName
    return { name := ctorName, shortName := ctorName.getString!, fields : CtorInfo' }
  if ctors.size == 1 then
    return .singleCtor typeName javaName ctors[0]!
  return .multiCtor typeName javaName ctors

private meta def collectNestedTypes (env : Environment) (rootName : Name) : MetaM (Array Name) := do
  let mut visited : Std.HashSet Name := {}
  let mut queue := #[rootName]
  let mut result := #[]
  while h : queue.size > 0 do
    let name := queue[0]
    queue := queue.extract 1 queue.size
    if visited.contains name then continue
    visited := visited.insert name
    result := result.push name
    let ctors := if let some sinfo := getStructureInfo? env name then
      [sinfo.structName ++ `mk]
    else match env.find? name with
      | some (.inductInfo indInfo) => indInfo.ctors
      | _ => []
    for ctorName in ctors do
      let some (.ctorInfo ci) := env.find? ctorName | continue
      let mut ty := ci.type
      for _ in List.range ci.numParams do
        match ty with | .forallE _ _ b _ => ty := b | _ => break
      for _ in List.range ci.numFields do
        match ty with
        | .forallE _ t b _ =>
          let t ← whnf t
          if let some fieldTypeName := t.getAppFn.constName? then
            if !visited.contains fieldTypeName && isCompoundType env fieldTypeName then
              queue := queue.push fieldTypeName
          ty := b
        | _ => break
  return result

/-! ## Java Code Generation -/

private meta def javaTypeFor (f : FieldInfo) : String :=
  if f.isCompound then escapeJavaName (toPascalCase (f.typeName.getString!))
  else (leafJavaType f.typeName).getD "java.lang.Object"

private meta def serializeExprFor (f : FieldInfo) (accessor : String) : String :=
  if f.isCompound then s!"{accessor}.toIon(ion)"
  else (leafSerializeExpr f.typeName accessor).getD s!"ion.newNull()"

private meta def recordParams (fields : Array FieldInfo) : String :=
  ", ".intercalate (fields.toList.map fun f => s!"{javaTypeFor f} {escapeJavaName f.name}")

/-- Generate the toIon method body for a struct (Ion struct with field name keys). -/
private meta def structToIonBody (fields : Array FieldInfo) : String :=
  let fieldLines := fields.toList.map fun f =>
    let accessor := s!"{escapeJavaName f.name}()"
    s!"        s.put(\"{f.name}\", {serializeExprFor f accessor});"
  s!"        var s = ion.newEmptyStruct();
{"\n".intercalate fieldLines}
        return s;"

/-- Generate the toIon method body for a single-ctor inductive (Ion struct with _0, _1, ... keys). -/
private meta def singleCtorToIonBody (fields : Array FieldInfo) : String :=
  let fieldLines := (List.range fields.size).map fun i =>
    let f := fields[i]!
    let accessor := s!"{escapeJavaName f.name}()"
    s!"        s.put(\"_{i}\", {serializeExprFor f accessor});"
  s!"        var s = ion.newEmptyStruct();
{"\n".intercalate fieldLines}
        return s;"

private meta def multiCtorToIonBody (shortName : String) (fields : Array FieldInfo) : String :=
  let fieldLines := fields.toList.map fun f =>
    let accessor := s!"{escapeJavaName f.name}()"
    s!"        sexp.add({serializeExprFor f accessor});"
  s!"        var sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol(\"{shortName}\"));
{"\n".intercalate fieldLines}
        return sexp;"

private meta def generateRecord (interfaceName : String) (recordName : String)
    (fields : Array FieldInfo) (toIonBody : String) : String :=
  let params := recordParams fields
  s!"    public record {recordName}({params}) implements {interfaceName} \{
        @Override
        public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIonBody}
        }
    }"

private meta def generateTypeFile (package : String) (shape : TypeShape) : String :=
  match shape with
  | .struct _ javaName fields =>
    let toIon := structToIonBody fields
    let params := recordParams fields
    s!"package {package};

public record {javaName}({params}) \{
    public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIon}
    }
}
"
  | .singleCtor _ javaName ctor =>
    let toIon := singleCtorToIonBody ctor.fields
    let params := recordParams ctor.fields
    s!"package {package};

public record {javaName}({params}) \{
    public com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion) \{
{toIon}
    }
}
"
  | .multiCtor _ javaName ctors =>
    let recordDefs := ctors.toList.map fun ctor =>
      let recName := escapeJavaName (toPascalCase ctor.shortName)
      let toIon := multiCtorToIonBody ctor.shortName ctor.fields
      generateRecord javaName recName ctor.fields toIon
    let permits := ", ".intercalate (ctors.toList.map fun ctor =>
      s!"{javaName}.{escapeJavaName (toPascalCase ctor.shortName)}")
    s!"package {package};

public sealed interface {javaName} permits {permits} \{
    com.amazon.ion.IonValue toIon(com.amazon.ion.IonSystem ion);

{"\n\n".intercalate recordDefs}
}
"

private meta def generateForType (env : Environment) (package : String) (rootName : Name) :
    MetaM GeneratedFiles := do
  let nestedTypes ← collectNestedTypes env rootName
  let mut files := #[]
  for typeName in nestedTypes do
    let shape ← analyzeType env typeName
    let javaName := match shape with
      | .struct _ n _ | .singleCtor _ n _ | .multiCtor _ n _ => n
    let content := generateTypeFile package shape
    files := files.push (s!"{javaName}.java", content)
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
