/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
import Strata.DDM.Ion
import Strata.DDM.Integration.Categories

namespace Strata.Java.DDM

open Strata (Dialect OpDecl ArgDecl ArgDeclKind QualifiedIdent SyntaxCat)
open Strata.DDM.Integration (primitiveCategories forbiddenCategories abstractCategories)

/-! # Java Code Generator for DDM Dialects

Generates Java source files from DDM dialect definitions:
- Sealed interfaces for categories, with operator records as nested types
- Non-sealed stub interfaces for abstract categories (e.g., Init.Expr)
- Generated `toIon` methods on each record for serialization
- Static factory methods for ergonomic AST construction
- Slim Ion serializer with helper methods (no reflection)

All names are disambiguated to avoid collisions with Java reserved words,
base classes (Node, SourceRange, IonSerializer), and each other.
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
  "exports", "module", "open", "opens", "permits", "provides",
  "record", "sealed", "to", "transitive", "uses", "var", "when", "with", "yield",
  -- Literals (cannot be used as identifiers)
  "true", "false", "null",
  -- Underscore (Java 9+)
  "_",
  -- Common java.lang classes that would cause ambiguity
  "String", "Object", "Integer", "Boolean", "Long", "Double", "Float", "Character", "Byte", "Short"
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
  | q`Init.Option =>
    match cat.args[0]? with
    | some inner => .optional (syntaxCatToJavaType inner)
    | none => panic! "Init.Option requires a type argument"
  | q`Init.Seq | q`Init.CommaSepBy | q`Init.NewlineSepBy | q`Init.SpaceSepBy | q`Init.SpacePrefixSepBy | q`Init.SemicolonSepBy =>
    match cat.args[0]? with
    | some inner => .list (syntaxCatToJavaType inner)
    | none => panic! "List category requires a type argument"
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
  | q`Init.Option | q`Init.Seq | q`Init.CommaSepBy
  | q`Init.NewlineSepBy | q`Init.SpaceSepBy | q`Init.SpacePrefixSepBy | q`Init.SemicolonSepBy =>
    cat.args[0]?.bind syntaxCatToQualifiedName
  | ⟨"Init", _⟩ => none
  | qid => some qid

/-! ## Serialization Code Generation -/

/-- Maps a primitive Init category to its serializer method name, or none for non-primitives. -/
def primitiveSerializerMethod (qid : QualifiedIdent) : Option String :=
  match qid with
  | q`Init.Ident => some "serializeIdent"
  | q`Init.Str => some "serializeStrlit"
  | q`Init.Num => some "serializeNum"
  | q`Init.Decimal => some "serializeDecimal"
  | q`Init.Bool => some "serializeBool"
  | q`Init.ByteArray => some "serializeBytes"
  | _ => .none

/-- Get the serializer method reference for a SyntaxCat's inner type (used in Option/List). -/
def serializerFnRef (c : SyntaxCat) : String :=
  match primitiveSerializerMethod c.name with
  | some method => s!"$s::{method}"
  | none => "$s::serialize"

/-- Generate the serialization expression for a single field. -/
def serializeFieldExpr (kind : ArgDeclKind) (fieldName : String) : String :=
  match kind with
  | .type _ => s!"$s.serialize({fieldName})"
  | .cat c =>
    match primitiveSerializerMethod c.name with
    | some method => s!"$s.{method}({fieldName})"
    | none =>
      if abstractCategories.contains c.name then s!"$s.serialize({fieldName})"
      else match c.name with
      | q`Init.Option =>
        let inner := c.args[0]!
        s!"$s.serializeOption({fieldName}, {serializerFnRef inner})"
      | q`Init.Seq | q`Init.CommaSepBy | q`Init.NewlineSepBy | q`Init.SpaceSepBy
      | q`Init.SpacePrefixSepBy | q`Init.SemicolonSepBy =>
        let inner := c.args[0]!
        let sep := (SepFormat.fromCategoryName? c.name).get!.toIonName
        s!"$s.serializeSeq({fieldName}, \"{sep}\", {serializerFnRef inner})"
      | _ => s!"$s.serialize({fieldName})"

/-! ## Java Structures -/

structure JavaField where
  name : String
  type : JavaType

/-- A nested record within a category interface. -/
structure JavaCategoryRecord where
  name : String
  operationName : QualifiedIdent
  fields : Array JavaField
  argDecls : Array ArgDecl  -- original DDM arg declarations for toIon generation

/-- All generated Java source files for a dialect. -/
public structure GeneratedFiles where
  sourceRange : String
  node : String
  categories : Array (String × String)  -- (filename, content)
  stubs : Array (String × String)       -- (filename, content) for stub interfaces
  builders : String × String            -- (filename, content)
  serializer : String
  deriving Inhabited

/-- Mapping from DDM names to disambiguated Java identifiers. -/
structure NameAssignments where
  categories : Std.HashMap QualifiedIdent String
  /-- Maps (category, opName) to the nested record name within that category -/
  operators : Std.HashMap (QualifiedIdent × String) String
  stubs : Std.HashMap QualifiedIdent String
  builders : String

/-! ## Code Generation -/

def argDeclToJavaField (decl : ArgDecl) : JavaField :=
  { name := escapeJavaName decl.ident, type := argDeclKindToJavaType decl.kind }

def JavaField.toParam (f : JavaField) : String :=
  s!"{f.type.toJava} {f.name}"

/-- Group operators by their target category, preserving declaration order. -/
def groupOpsByCategory (d : Dialect) : Std.HashMap QualifiedIdent (Array OpDecl) :=
  d.declarations.foldl (init := {}) fun acc decl =>
    match decl with
    | .op op => acc.alter op.category (fun ops? => some ((ops?.getD #[]).push op))
    | _ => acc

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

/-- Generate a nested record definition within a category interface. -/
def generateRecord (catName : String) (r : JavaCategoryRecord) : String :=
  let params := ", ".intercalate (r.fields.toList.map JavaField.toParam)
  let opName := s!"{r.operationName.dialect}.{r.operationName.name}"
  let fieldSerializations := r.argDecls.toList.map fun arg =>
    let fieldName := escapeJavaName arg.ident
    s!"            sexp.add({serializeFieldExpr arg.kind (fieldName ++ "()")});"
  let toIonBody := "\n".intercalate
    (s!"            var sexp = $s.newOp(\"{opName}\", sourceRange());"
     :: fieldSerializations ++ ["            return sexp;"])
  s!"    public record {r.name}(
        SourceRange sourceRange{if r.fields.isEmpty then "" else ",\n        " ++ params}
    ) implements {catName} \{
        @Override
        public java.lang.String operationName() \{ return \"{opName}\"; }

        @Override
        public com.amazon.ion.IonSexp toIon(IonSerializer $s) \{
{toIonBody}
        }
    }"

/-- Generate a category file with sealed interface and nested records. -/
def generateCategoryFile (package : String) (catName : String) (records : Array JavaCategoryRecord) : String :=
  let permits := if records.isEmpty then ""
    else " permits " ++ ", ".intercalate (records.toList.map fun r => s!"{catName}.{r.name}")
  let body := "\n\n".intercalate (records.toList.map (generateRecord catName))
  s!"package {package};

public sealed interface {catName} extends Node{permits} \{
{body}
}
"

/-- Assign unique Java names to all generated types.
    Operator names are scoped within their category (nested records). -/
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
        | .type _ => refs.insert q`Init.Expr
        | .cat c => match syntaxCatToQualifiedName c with
          | some qid => refs.insert qid
          | none => refs
      (cats, refs)
    | _ => (cats, refs)

  -- All QualifiedIdents that need Java names (categories + refs)
  let allQids := cats ++ refs.toArray.filter (!cats.contains ·)

  -- Count name occurrences to detect collisions across categories
  let nameCounts : Std.HashMap String Nat := allQids.foldl (init := {}) fun m qid =>
    m.alter qid.name (fun v => some (v.getD 0 + 1))

  -- Assign Java names, prefixing with dialect when there's a collision
  let assignName (used : Std.HashSet String) (qid : QualifiedIdent) : String × Std.HashSet String :=
    let base := if nameCounts.getD qid.name 0 > 1
                then escapeJavaName (toPascalCase s!"{qid.dialect}_{qid.name}")
                else escapeJavaName (toPascalCase qid.name)
    disambiguate base used

  -- Assign category names (top-level, must be globally unique)
  let catInit : Std.HashMap QualifiedIdent String × Std.HashSet String := ({}, baseNames)
  let (categoryNames, used) := cats.foldl (init := catInit) fun (map, used) cat =>
    let (name, newUsed) := assignName used cat
    (map.insert cat name, newUsed)

  -- Assign operator names (nested within category, must be unique within category + not collide with category name)
  let opsByCategory := groupOpsByCategory d

  let operatorNames := opsByCategory.toList.foldl (init := ({})) fun opNames (cat, ops) =>
    let catName := categoryNames[cat]!
    -- Within each category, operator names must be unique and not collide with the category name
    let localUsed : Std.HashSet String := Std.HashSet.ofList [catName.toLower]
    let (opNames, _) := ops.foldl (init := (opNames, localUsed)) fun (opNames, localUsed) op =>
      let base := escapeJavaName (toPascalCase op.name)
      -- For single-op categories where the op name matches the category, use "Of"
      let base := if ops.size == 1 && base.toLower == catName.toLower then "Of" else base
      let (name, newLocalUsed) := disambiguate base localUsed
      (opNames.insert (op.category, op.name) name, newLocalUsed)
    opNames

  -- Assign stub names (referenced types not in this dialect's categories)
  let stubInit : Std.HashMap QualifiedIdent String × Std.HashSet String := ({}, used)
  let (stubNames, used) := refs.toArray.foldl (init := stubInit) fun (map, used) ref =>
    if categoryNames.contains ref then (map, used)
    else
      let (name, newUsed) := assignName used ref
      (map.insert ref name, newUsed)

  let (buildersName, _) := disambiguate (escapeJavaName (toPascalCase d.name)) used

  { categories := categoryNames, operators := operatorNames, stubs := stubNames, builders := buildersName }

def generateBuilders (package : String) (dialectName : String) (d : Dialect) (names : NameAssignments) : String :=
  let methods (op : OpDecl) :=
    let (ps, as, checks) := op.argDecls.toArray
        |>.foldl (init := (#[], #[], #[])) fun (ps, as, checks) decl =>
      let name := escapeJavaName decl.ident
      let cat := decl.kind.categoryOf.name
      if cat == q`Init.Num then
        (ps.push s!"long {name}",
         as.push s!"java.math.BigInteger.valueOf({name})",
         checks.push s!"if ({name} < 0) throw new IllegalArgumentException(\"{name} must be non-negative\");")
      else if cat == q`Init.Decimal then
        (ps.push s!"double {name}",
         as.push s!"java.math.BigDecimal.valueOf({name})",
         checks)
      else
        let t := (argDeclKindToJavaType decl.kind).toJava
        (ps.push s!"{t} {name}", as.push name, checks)
    let methodName := escapeJavaName op.name
    let returnType := names.categories[op.category]!
    let recordName := s!"{returnType}.{names.operators[(op.category, op.name)]!}"
    let checksStr := if checks.isEmpty then "" else " ".intercalate checks.toList ++ " "
    let argsStr := if as.isEmpty then "" else ", " ++ ", ".intercalate as.toList
    let paramsStr := ", ".intercalate ps.toList
    let srParams := if ps.isEmpty then "SourceRange sourceRange" else s!"SourceRange sourceRange, {paramsStr}"
    let withSR := s!"    public static {returnType} {methodName}({srParams}) \{ {checksStr}return new {recordName}(sourceRange{argsStr}); }"
    let withoutSR := s!"    public static {returnType} {methodName}({paramsStr}) \{ {checksStr}return new {recordName}(SourceRange.NONE{argsStr}); }"
    s!"{withSR}\n{withoutSR}"
  let allMethods := d.declarations.filterMap fun | .op op => some (methods op) | _ => none
  s!"package {package};\n\npublic class {dialectName} \{\n{"\n\n".intercalate allMethods.toList}\n}\n"

public def generateDialect (d : Dialect) (package : String) : Except String GeneratedFiles := do
  let names := assignAllNames d

  -- Check for unsupported declarations
  for decl in d.declarations do
    match decl with
    | .type t => throw s!"type declaration '{t.name}' is not supported in Java generation"
    | .function f => throw s!"function declaration '{f.name}' is not supported in Java generation"
    | _ => pure ()

  -- Group operators by category (preserving declaration order)
  let opsByCategory := groupOpsByCategory d

  -- Generate category files (sealed interface + nested records)
  let categoryFiles := opsByCategory.toList.map fun (cat, ops) =>
    let catName := names.categories[cat]!
    let records := ops.map fun op =>
      let recName := names.operators[(op.category, op.name)]!
      { name := recName
        operationName := ⟨d.name, op.name⟩
        fields := op.argDecls.toArray.map argDeclToJavaField
        argDecls := op.argDecls.toArray : JavaCategoryRecord }
    (s!"{catName}.java", generateCategoryFile package catName records)

  -- Stub interfaces for referenced types without operators
  let stubFiles := names.stubs.toList.map fun (_, name) =>
    generateStubInterface package name

  -- All type names for Node permits clause
  let allTypeNames := categoryFiles.map (·.1.dropEnd 5 |>.toString)
    ++ stubFiles.map (·.1.dropEnd 5 |>.toString)

  return {
    sourceRange := generateSourceRange package
    node := generateNodeInterface package allTypeNames
    categories := categoryFiles.toArray
    stubs := stubFiles.toArray
    builders := (s!"{names.builders}.java", generateBuilders package names.builders d names)
    serializer := generateSerializer package
  }

/-! ## File Output -/

public def packageToPath (package : String) : System.FilePath :=
  let parts := package.splitOn "."
  ⟨String.intercalate "/" parts⟩

public def writeJavaFiles (baseDir : System.FilePath) (package : String) (files : GeneratedFiles) : IO Unit := do
  let dir := baseDir / packageToPath package
  IO.FS.createDirAll dir

  IO.FS.writeFile (dir / "SourceRange.java") files.sourceRange
  IO.FS.writeFile (dir / "Node.java") files.node
  IO.FS.writeFile (dir / "IonSerializer.java") files.serializer
  IO.FS.writeFile (dir / files.builders.1) files.builders.2

  for (filename, content) in files.categories do
    IO.FS.writeFile (dir / filename) content

  for (filename, content) in files.stubs do
    IO.FS.writeFile (dir / filename) content

end Strata.Java.DDM
