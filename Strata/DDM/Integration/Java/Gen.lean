/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.DDM.Integration.Categories

namespace Strata.Java

open Strata (Dialect OpDecl ArgDecl ArgDeclKind QualifiedIdent SyntaxCat)
open Strata.DDM.Integration (primitiveCategories forbiddenCategories abstractCategories)

/-! # Java Code Generator for DDM Dialects

Generates Java source files from DDM dialect definitions:
- Sealed interfaces for categories with operators
- Non-sealed stub interfaces for abstract categories (e.g., Init.Expr)
- Record classes for operators
- Static factory methods for ergonomic AST construction
- Ion serializer for Lean interop

All names are disambiguated to avoid collisions with Java reserved words,
base classes (Node, SourceRange), and each other.
-/

/-! ## Name Utilities -/

def javaReservedWords : Std.HashSet String := Std.HashSet.ofList [
  -- Reserved keywords
  "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
  "class", "const", "continue", "default", "do", "double", "else", "enum",
  "extends", "final", "finally", "float", "for", "goto", "if", "implements",
  "import", "instanceof", "int", "interface", "long", "native", "new",
  "package", "private", "protected", "public", "return", "short", "static",
  "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
  "transient", "try", "void", "volatile", "while",
  -- Contextual keywords (restricted in some contexts)
  "exports", "module", "non-sealed", "open", "opens", "permits", "provides",
  "record", "sealed", "to", "transitive", "uses", "var", "when", "with", "yield",
  -- Literals (cannot be used as identifiers)
  "true", "false", "null",
  -- Underscore (Java 9+)
  "_"
]

def escapeJavaName (name : String) : String :=
  -- Remove invalid characters (like ?)
  let cleaned := String.ofList (name.toList.filter (fun c => c.isAlphanum || c == '_'))
  let cleaned := if cleaned.isEmpty then "field" else cleaned
  -- Add suffix if reserved word
  if javaReservedWords.contains cleaned then cleaned ++ "_" else cleaned

def toPascalCase (s : String) : String :=
  s.splitOn "_"
  |>.filter (!·.isEmpty)
  |>.map (fun part => match part.toList with
    | [] => ""
    | c :: cs => .ofList (c.toUpper :: cs))
  |> String.intercalate ""

/-- Generate unique name by adding suffix if collision detected -/
partial def disambiguate (base : String) (usedNames : Std.HashSet String) : String × Std.HashSet String :=
  let rec findUnused (n : Nat) : String :=
    let suffix := if n == 0 then "" else if n == 1 then "_" else s!"_{n}"
    let candidate := base ++ suffix
    if usedNames.contains candidate.toLower then findUnused (n + 1) else candidate
  let name := findUnused 0
  (name, usedNames.insert name.toLower)

/-! ## Type Mapping -/

inductive JavaType where
  | simple (name : String) (boxed : Option String := none)
  | array (elem : JavaType)
  | optional (elem : JavaType)
  | list (elem : JavaType)
  deriving Inhabited

mutual
def JavaType.toJava : JavaType → String
  | .simple name _ => name
  | .array elem => elem.toJava ++ "[]"
  | .optional elem => s!"java.util.Optional<{elem.toJavaBoxed}>"
  | .list elem => s!"java.util.List<{elem.toJavaBoxed}>"

def JavaType.toJavaBoxed : JavaType → String
  | .simple _ (some boxed) => boxed
  | t => t.toJava
end

/-- Maps a primitive Init category to its Java type. -/
def primitiveJavaType (qid : QualifiedIdent) : JavaType :=
  match qid with
  | q`Init.Ident => .simple "java.lang.String"
  | q`Init.Num => .simple "java.math.BigInteger"
  | q`Init.Decimal => .simple "java.math.BigDecimal"
  | q`Init.Str => .simple "java.lang.String"
  | q`Init.ByteArray => .array (.simple "byte" (some "java.lang.Byte"))
  | q`Init.Bool => .simple "boolean" (some "java.lang.Boolean")
  | _ => panic! s!"Not a primitive category: {qid.dialect}.{qid.name}"

/-- Maps an abstract Init category to its Java interface name. -/
def abstractJavaName (qid : QualifiedIdent) : String :=
  match qid with
  | q`Init.Expr => "Expr"
  | q`Init.Type => "Type_"
  | q`Init.TypeP => "TypeP"
  | _ => panic! s!"Not an abstract category: {qid.dialect}.{qid.name}"

partial def syntaxCatToJavaType (cat : SyntaxCat) : JavaType :=
  if forbiddenCategories.contains cat.name then
    panic! s!"{cat.name.dialect}.{cat.name.name} is internal DDM machinery"
  else if primitiveCategories.contains cat.name then
    primitiveJavaType cat.name
  else if abstractCategories.contains cat.name then
    .simple (abstractJavaName cat.name)
  else match cat.name with
  | ⟨"Init", "Option"⟩ =>
    match cat.args[0]? with
    | some inner => .optional (syntaxCatToJavaType inner)
    | none => panic! "Init.Option requires a type argument"
  | ⟨"Init", "Seq"⟩ | ⟨"Init", "CommaSepBy"⟩ =>
    match cat.args[0]? with
    | some inner => .list (syntaxCatToJavaType inner)
    | none => panic! "Init.Seq/CommaSepBy requires a type argument"
  | ⟨"Init", _⟩ => panic! s!"Unknown Init category: {cat.name.name}"
  | ⟨_, name⟩ => .simple (escapeJavaName (toPascalCase name))

def argDeclKindToJavaType : ArgDeclKind → JavaType
  | .type _ => .simple "Expr"
  | .cat c => syntaxCatToJavaType c

/-- Extract the QualifiedIdent for categories that need Java interfaces, or none for primitives. -/
partial def syntaxCatToQualifiedName (cat : SyntaxCat) : Option QualifiedIdent :=
  if primitiveCategories.contains cat.name then none
  else if abstractCategories.contains cat.name then some cat.name
  else match cat.name with
  | ⟨"Init", "Option"⟩ | ⟨"Init", "Seq"⟩ | ⟨"Init", "CommaSepBy"⟩ =>
    cat.args[0]?.bind syntaxCatToQualifiedName
  | ⟨"Init", _⟩ => none
  | qid => some qid

/-! ## Java Structures -/

structure JavaField where
  name : String
  type : JavaType

structure JavaRecord where
  name : String
  operationName : QualifiedIdent
  implements : String
  fields : Array JavaField

structure JavaInterface where
  name : String
  permits : Array String

/-- All generated Java source files for a dialect. -/
structure GeneratedFiles where
  sourceRange : String
  node : String
  interfaces : Array (String × String)  -- (filename, content)
  records : Array (String × String)
  builders : String × String  -- (filename, content)
  serializer : String
  deriving Inhabited

/-- Mapping from DDM names to disambiguated Java identifiers. -/
structure NameAssignments where
  categories : Std.HashMap QualifiedIdent String
  operators : Std.HashMap (QualifiedIdent × String) String
  stubs : Std.HashMap QualifiedIdent String
  builders : String

/-! ## Code Generation -/

def argDeclToJavaField (decl : ArgDecl) : JavaField :=
  { name := escapeJavaName decl.ident
    type := argDeclKindToJavaType decl.kind }

def JavaField.toParam (f : JavaField) : String :=
  s!"{f.type.toJava} {f.name}"

def JavaRecord.toJava (package : String) (r : JavaRecord) : String :=
  let params := String.intercalate ", " (r.fields.toList.map JavaField.toParam)
  let opName := s!"{r.operationName.dialect}.{r.operationName.name}"
s!"package {package};

public record {r.name}(
    SourceRange sourceRange{if r.fields.isEmpty then "" else ",\n    " ++ params}
) implements {r.implements} \{
    @Override
    public java.lang.String operationName() \{ return \"{opName}\"; }
}
"

def JavaInterface.toJava (package : String) (i : JavaInterface) : String :=
  let permits := if i.permits.isEmpty then ""
    else " permits " ++ String.intercalate ", " i.permits.toList
s!"package {package};

public sealed interface {i.name} extends Node{permits} \{}
"

def templatePackage := "com.strata.template"

def sourceRangeTemplate : String := include_str "templates/SourceRange.java"
def nodeTemplate : String := include_str "templates/Node.java"
def serializerTemplate : String := include_str "templates/IonSerializer.java"

def generateSourceRange (package : String) : String :=
  sourceRangeTemplate.replace templatePackage package

def generateNodeInterface (package : String) (categories : List String) : String :=
  let base := nodeTemplate.replace templatePackage package
  if categories.isEmpty then base
  else
    let permits := " permits " ++ String.intercalate ", " categories
    base.replace "sealed interface Node" s!"sealed interface Node{permits}"

/-- Generate non-sealed stub interface for a category with no operators -/
def generateStubInterface (package : String) (name : String) : String × String :=
  (s!"{name}.java", s!"package {package};\n\npublic non-sealed interface {name} extends Node \{}\n")

def generateSerializer (package : String) : String :=
  serializerTemplate.replace templatePackage package

/-- Assign unique Java names to all generated types -/
def assignAllNames (d : Dialect) : NameAssignments :=
  let baseNames : Std.HashSet String := Std.HashSet.ofList ["node", "sourcerange", "ionserializer"]

  -- Collect unique categories and referenced types
  let init : Array QualifiedIdent × Std.HashSet QualifiedIdent := (#[], {})
  let (cats, refs) := d.declarations.foldl (init := init) fun (cats, refs) decl =>
    match decl with
    | .op op =>
      let cats := if cats.contains op.category then cats else cats.push op.category
      let refs := op.argDecls.toArray.foldl (init := refs) fun refs arg =>
        match arg.kind with
        | .type _ => refs.insert ⟨"Init", "Expr"⟩
        | .cat c => match syntaxCatToQualifiedName c with
          | some qid => refs.insert qid
          | none => refs
      (cats, refs)
    | _ => (cats, refs)

  -- All QualifiedIdents that need Java names (categories + refs)
  let allQids := cats ++ refs.toArray.filter (!cats.contains ·)

  -- Count name occurrences to detect collisions
  let nameCounts : Std.HashMap String Nat := allQids.foldl (init := {}) fun m qid =>
    m.alter qid.name (fun v => some (v.getD 0 + 1))

  -- Assign Java names, prefixing with dialect when there's a collision
  let assignName (used : Std.HashSet String) (qid : QualifiedIdent) : String × Std.HashSet String :=
    let base := if nameCounts.getD qid.name 0 > 1
                then escapeJavaName (toPascalCase s!"{qid.dialect}_{qid.name}")
                else escapeJavaName (toPascalCase qid.name)
    disambiguate base used

  -- Assign category names
  let catInit : Std.HashMap QualifiedIdent String × Std.HashSet String := ({}, baseNames)
  let (categoryNames, used) := cats.foldl (init := catInit) fun (map, used) cat =>
    let (name, newUsed) := assignName used cat
    (map.insert cat name, newUsed)

  -- Assign operator names
  let opInit : Std.HashMap (QualifiedIdent × String) String × Std.HashSet String := ({}, used)
  let (operatorNames, used) := d.declarations.foldl (init := opInit) fun (map, used) decl =>
    match decl with
    | .op op =>
      let base := escapeJavaName (toPascalCase op.name)
      let (name, newUsed) := disambiguate base used
      (map.insert (op.category, op.name) name, newUsed)
    | _ => (map, used)

  -- Assign stub names (referenced types not in this dialect's categories)
  let stubInit : Std.HashMap QualifiedIdent String × Std.HashSet String := ({}, used)
  let (stubNames, used) := refs.toArray.foldl (init := stubInit) fun (map, used) ref =>
    if categoryNames.contains ref then (map, used)
    else
      let (name, newUsed) := assignName used ref
      (map.insert ref name, newUsed)

  let (buildersName, _) := disambiguate d.name used

  { categories := categoryNames, operators := operatorNames, stubs := stubNames, builders := buildersName }

/-- Group operators by their target category -/
def groupOpsByCategory (d : Dialect) (names : NameAssignments)
    : Std.HashMap QualifiedIdent (Array String) :=
  d.declarations.foldl (init := {}) fun acc decl =>
    match decl with
    | .op op =>
      let javaName := names.operators[(op.category, op.name)]!
      acc.alter op.category (fun ops? => some ((ops?.getD #[]).push javaName))
    | _ => acc

def opDeclToJavaRecord (dialectName : String) (names : NameAssignments) (op : OpDecl)
    : JavaRecord :=
  { name := names.operators[(op.category, op.name)]!
    operationName := ⟨dialectName, op.name⟩
    implements := names.categories[op.category]!
    fields := op.argDecls.toArray.map argDeclToJavaField }

def generateBuilders (package : String) (dialectName : String) (d : Dialect) (names : NameAssignments) : String :=
  let method (op : OpDecl) :=
    let fields := op.argDecls.toArray.map argDeclToJavaField
    let (ps, as) := fields.foldl (init := (#[], #[])) fun (ps, as) f =>
      match f.type with
      | .simple "java.math.BigInteger" _ => (ps.push s!"long {f.name}", as.push s!"java.math.BigInteger.valueOf({f.name})")
      | .simple "java.math.BigDecimal" _ => (ps.push s!"double {f.name}", as.push s!"java.math.BigDecimal.valueOf({f.name})")
      | t => (ps.push s!"{t.toJava} {f.name}", as.push f.name)
    let methodName := escapeJavaName op.name
    s!"    public static {names.categories[op.category]!} {methodName}({", ".intercalate ps.toList}) \{ return new {names.operators[(op.category, op.name)]!}(SourceRange.NONE{if as.isEmpty then "" else ", " ++ ", ".intercalate as.toList}); }"
  let methods := d.declarations.filterMap fun | .op op => some (method op) | _ => none
  s!"package {package};\n\npublic class {dialectName} \{\n{"\n".intercalate methods.toList}\n}\n"

def generateDialect (d : Dialect) (package : String) : Except String GeneratedFiles := do
  let names := assignAllNames d
  let opsByCategory := groupOpsByCategory d names

  -- Check for unsupported declarations
  for decl in d.declarations do
    match decl with
    | .type t => throw s!"type declaration '{t.name}' is not supported in Java generation"
    | .function f => throw s!"function declaration '{f.name}' is not supported in Java generation"
    | _ => pure ()

  -- Categories with operators get sealed interfaces with permits clauses
  let sealedInterfaces := opsByCategory.toList.map fun (cat, ops) =>
    let name := names.categories[cat]!
    let iface : JavaInterface := { name, permits := ops }
    (s!"{name}.java", iface.toJava package)

  -- Stub interfaces for referenced types without operators
  let stubInterfaces := names.stubs.toList.map fun (_, name) =>
    generateStubInterface package name

  -- Generate records for operators
  let records := d.declarations.toList.filterMap fun decl =>
    match decl with
    | .op op =>
      let name := names.operators[(op.category, op.name)]!
      some (s!"{name}.java", (opDeclToJavaRecord d.name names op).toJava package)
    | _ => none

  -- All interface names for Node permits clause
  let allInterfaceNames := (sealedInterfaces ++ stubInterfaces).map (·.1.dropRight 5)

  return {
    sourceRange := generateSourceRange package
    node := generateNodeInterface package allInterfaceNames
    interfaces := sealedInterfaces.toArray ++ stubInterfaces.toArray
    records := records.toArray
    builders := (s!"{names.builders}.java", generateBuilders package names.builders d names)
    serializer := generateSerializer package
  }

/-! ## File Output -/

def packageToPath (package : String) : System.FilePath :=
  let parts := package.splitOn "."
  ⟨String.intercalate "/" parts⟩

def writeJavaFiles (baseDir : System.FilePath) (package : String) (files : GeneratedFiles) : IO Unit := do
  let dir := baseDir / packageToPath package
  IO.FS.createDirAll dir

  IO.FS.writeFile (dir / "SourceRange.java") files.sourceRange
  IO.FS.writeFile (dir / "Node.java") files.node
  IO.FS.writeFile (dir / "IonSerializer.java") files.serializer
  IO.FS.writeFile (dir / files.builders.1) files.builders.2

  for (filename, content) in files.interfaces do
    IO.FS.writeFile (dir / filename) content

  for (filename, content) in files.records do
    IO.FS.writeFile (dir / filename) content

end Strata.Java
