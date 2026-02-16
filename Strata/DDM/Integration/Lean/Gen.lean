/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Strata.DDM.AST
public meta import Strata.DDM.BuiltinDialects.Init
meta import        Strata.DDM.BuiltinDialects.StrataDDL
public meta import Strata.DDM.Integration.Categories
public meta import Strata.DDM.Integration.Lean.Env
import             Strata.DDM.Integration.Lean.GenTrace
public meta import Strata.DDM.Integration.Lean.OfAstM
public meta import Strata.DDM.Util.Graph.Tarjan
meta import        Strata.Util.DecideProp

/-!
Implements the `#strata_gen` command, which reads a dialect definition and
generates Lean inductive types, `toAst`, and `ofAst` functions for each
category used by the dialect.
-/

open Lean (Command Name Ident Term TSyntax getEnv logError profileitM quote
  withTraceNode mkIdentFrom)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand)
open Lean.MonadOptions (getOptions)
open Lean.MonadResolveName (getCurrNamespace)
open Lean.Parser.Command (ctor)
open Lean.Parser.Term (bracketedBinderF doSeqItem matchAltExpr)
open Lean.Parser.Termination (terminationBy suffix)
open Lean.Syntax (mkApp mkCApp mkStrLit)

meta section
namespace Strata

namespace Lean

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def mkScopedIdent (scope : Name) (subName : Lean.Name) : Ident :=
  let fullName := scope ++ subName
  let nameStr := toString subName
  .mk (.ident .none nameStr.toRawSubstring subName [.decl fullName []])

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def currScopedIdent {m} [Monad m] [Lean.MonadResolveName m]
    (subName : Lean.Name) : m Ident := do
  (mkScopedIdent · subName) <$> getCurrNamespace

end Lean

open Lean (currScopedIdent)

def arrayLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#[ $as:term,* ] : Array _) )

def vecLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#v[ $as:term,* ] : Vector _ $(quote as.size)) )

abbrev LeanCategoryName := Lean.Name

structure GenContext where
  -- Syntax for #strata_gen for source location purposes.
  src : Lean.Syntax
  categoryNameMap : Std.HashMap QualifiedIdent String

abbrev GenM := ReaderT GenContext CommandElabM

def runCmd {α} (act : CommandElabM α) : GenM α := fun _ => act

/-- Creates a fresh, unique Lean name using macro scopes to prevent
name capture in generated code. -/
def genFreshLeanName (s : String) : GenM Name := do
  let fresh ← modifyGet fun s =>
    (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  let n : Name := .anonymous |>.str s
  return Lean.addMacroScope (← getEnv).mainModule n fresh

/--
Creates a pair of identifiers with the same underlying name: one canonical
(for patterns) and one regular (for use in terms).
-/
def genFreshIdentPair (s : String) : GenM (Ident × Ident) := do
  let name ← genFreshLeanName s
  let src := (←read).src
  return (mkIdentFrom src name true, mkIdentFrom src name)

/-- Create a canonical identifier. -/
def mkCanIdent (src : Lean.Syntax) (val : Name) : Ident :=
  mkIdentFrom src val true

/-- Create a identifier from a name. -/
def genIdentFrom (name : Name) (canonical : Bool := false) : GenM Ident := do
  return mkIdentFrom (←read).src name canonical

/-!
## Category Classification

The generator classifies Init categories into several sets that control how
code is generated:

- `declaredCategories` — Primitive Init categories (e.g., `Init.Num`, `Init.Ident`)
  that map directly to existing Lean types (e.g., `Nat`, `String`).  No inductive
  type is generated for these; they appear as-is in constructor fields.

- `forbiddenCategories` — Internal machinery categories (e.g., `Init.BindingType`,
  `StrataDDL.Binding`) that dialects must not reference in generated code.  An
  error is reported if a dialect operation uses one.

- `abstractCategories` — The abstract extension points `Init.Expr`, `Init.Type`,
  and `Init.TypeP`.  Init-defined operators for these are ignored; instead they
  are populated via `fn`/`type` declarations and augmented with builtin
  constructors (see `makeBuiltinCtors`).  Non-Init dialects are prevented from
  adding operators to these categories by the check in `addDecl`.

- `reservedCategories` — Category names that would shadow Lean keywords (currently
  just `"Type"`).  These are prefixed with the dialect name in generated identifiers.
-/

def reservedCategories : Std.HashSet String := { "Type" }

structure OrderedSet (α : Type _) [BEq α] [Hashable α] where
  set : Std.HashSet α
  values : Array α

namespace OrderedSet

def empty [BEq α] [Hashable α] : OrderedSet α := { set := {}, values := #[]}

partial def addAtom {α} [BEq α] [Hashable α] (s : OrderedSet α) (a : α)
    : OrderedSet α :=
  if a ∈ s.set then
    s
  else
    { set := s.set.insert a, values := s.values.push a }

/--
Add element `e` and its transitive closure under `next` in post-order
(dependencies before dependents).
-/
partial def addPostTC {α} [BEq α] [Hashable α] (next : α → Array α)
    (s : OrderedSet α) (e : α) : OrderedSet α :=
  if e ∈ s.set then
    s
  else
    let succs := next e
    let s := { s with set := s.set.insert e }
    let s := succs.foldl (init := s) (addPostTC next)
    { s with values := s.values.push e }

end OrderedSet

/--
Computes the transitive closure of dialect dependencies, returning all
dialects that the given dialect depends on (including itself).
-/
def generateDependentDialects (lookup : String → Option Dialect)
    (name : DialectName) : Array DialectName :=
  let s : OrderedSet DialectName := .empty
  let s := s.addAtom initDialect.name
  let next (name : DialectName) : Array DialectName :=
      match lookup name with
      | some d => d.imports
      | none => #[]
  s.addPostTC next name |>.values

def resolveDialects (lookup : String → Option Dialect)
    (dialects : Array DialectName) : Except String (Array Dialect) := do
  dialects.mapM fun name =>
    match lookup name with
    | none => throw s!"Unknown dialect {name}"
    | some d => pure d

abbrev CategoryName := QualifiedIdent

def forbiddenCategories : Std.HashSet CategoryName :=
  DDM.Integration.forbiddenCategories

def forbiddenWellDefined : Bool :=
  forbiddenCategories.all fun nm =>
    match nm.dialect with
    | "Init" => nm.name ∈ initDialect
    | "StrataDDL" => nm.name ∈ StrataDDL
    | _ => false

#guard "BindingType" ∈ initDialect.cache
#guard "Binding" ∈ StrataDDL.cache
#guard forbiddenWellDefined

/-- Abstract categories (`Init.Expr`, `Init.Type`, `Init.TypeP`)
extended via `fn`/`type` rather than `op`. -/
def abstractCategories : Std.HashSet CategoryName :=
  DDM.Integration.abstractCategories

/--
Argument declaration for code generation.
-/
structure GenArgDecl where
  name : String
  cat : SyntaxCat
  addAnn : Bool := true

/--
A constructor in a generated datatype.

This could be from the dialect or it could be a builtin constructor.
-/
structure DefaultCtor where
  /--
  The Lean name for the constructor.

  This is guaranteed to be unique for the category.
  -/
  leanNameStr : String
  /--
  The name in the Strata dialect for this constructor.  If `none`, then
  this must be an auto generated constructor.
  -/
  strataName : Option QualifiedIdent
  argDecls : Array GenArgDecl

def DefaultCtor.leanName (c : DefaultCtor) : Name :=
  .str .anonymous c.leanNameStr

/--
An operation at the category level.
-/
structure CatOp where
  name : QualifiedIdent
  argDecls : Array GenArgDecl

namespace CatOp

partial def checkCat (op : QualifiedIdent) (c : SyntaxCat)
    : Except String Unit := do
  c.args.forM (checkCat op)
  let f := c.name
  if f ∈ forbiddenCategories then
    throw s!"{op.fullName} refers to unsupported category {f.fullName}."

def ofArgDecl (op : QualifiedIdent) (d : ArgDecl)
    : Except String GenArgDecl := do
  let cat ←
    match d.kind with
    | .type tp =>
      pure <| .atom tp.ann q`Init.Expr
    | .cat c =>
      checkCat op c
      pure c
  -- Check if unwrap metadata is present (addAnn has reversed polarity)
  let addAnn := !(q`StrataDDL.unwrap ∈ d.metadata)
  pure { name := d.ident, cat, addAnn }

def ofOpDecl (d : DialectName) (o : OpDecl) : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls.toArray |>.mapM (ofArgDecl name)
  return { name, argDecls }

def ofTypeDecl (d : DialectName) (o : TypeDecl) : CatOp := {
  name := ⟨d, o.name⟩
  argDecls := o.argNames |>.map fun anm =>
    { name := anm.val, cat := .atom .none q`Init.Type }
}

def ofFunctionDecl (d : DialectName) (o : FunctionDecl)
    : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls.toArray |>.mapM (ofArgDecl name)
  return { name, argDecls }

end CatOp

/--
This maps names of categories that we are going to declare to
the list of operators in that category.
-/
abbrev CatOpMap := Std.HashMap CategoryName (Array CatOp)

structure CatOpState where
  map : CatOpMap
  errors : Array String := #[]

-- Monad that collects errors from adding declarations.
abbrev CatOpM := StateM CatOpState

def CatOpM.addError (msg : String) : CatOpM Unit :=
  modify fun s => { s with errors := s.errors.push msg }

/-- Creates an identifier prefixed with `_root_` for unambiguous resolution. -/
def mkRootIdent (name : Name) : Ident :=
  let rootName := `_root_ ++ name
  .mk (.ident .none name.toString.toRawSubstring rootName [.decl name []])

/-- Maps primitive Init categories to their Lean types. -/
def declaredCategories : Std.HashMap CategoryName Name := .ofList [
  (q`Init.Ident, ``String),
  (q`Init.Num, ``Nat),
  (q`Init.Decimal, ``Decimal),
  (q`Init.Str, ``String),
  (q`Init.ByteArray, ``ByteArray),
  (q`Init.Bool, ``Bool)
]
#guard declaredCategories.keys.all
  (DDM.Integration.primitiveCategories.contains ·)

namespace CatOpMap

def alterMap (f : CatOpMap → CatOpMap) : CatOpM Unit := do
  modify fun s => { s with map := f s.map }

def addOp (m : CatOpMap) (cat : CategoryName) (op : CatOp) : CatOpMap :=
  assert! cat ∈ m
  m.modify cat (fun a => a.push op)

def addOpM (cat : CategoryName) (op : CatOp) : CatOpM Unit := do
  modify fun s => { s with map := s.map.addOp cat op }

def addDecl (d : DialectName) (decl : Decl) : CatOpM Unit :=
  let addCatOp (cat : QualifiedIdent) (act : Except String CatOp) : CatOpM Unit :=
    match act with
    | .ok op =>
      addOpM cat op
    | .error msg => do
      .addError msg
  match decl with
  | .syncat decl => do
    let cat := ⟨d, decl.name⟩
    -- Note: Init.Bool is pre-seeded in `CatOpMap.init` so it won't reach
    -- here from Init; non-Init dialects produce a different qualified name.
    if cat ∉ declaredCategories ∧ cat ∉ forbiddenCategories then
      alterMap <| fun m => m.insert ⟨d, decl.name⟩ #[]
  | .op decl => do
    -- Bool is in `declaredCategories` (mapped to Lean's Bool), so its category
    -- is normally ignored.  However, we still need boolTrue/boolFalse operators
    -- in the CatOpMap so that `toAst`/`ofAst` can convert between `Ann Bool α`
    -- and `OperationF` representations.
    let cat := decl.category
    -- Bool operators (boolTrue/boolFalse) are allowed through even though
    -- Init.Bool is in declaredCategories, because toAst/ofAst need them.
    let isBoolOp := cat == q`Init.Bool &&
      (decl.name == "boolTrue" || decl.name == "boolFalse")
    let extendsFixedCategory :=
      cat ∈ declaredCategories ∨ cat ∈ forbiddenCategories ∨ cat ∈ abstractCategories
    if extendsFixedCategory && !isBoolOp then
      if d ≠ "Init" then
        .addError s!"Skipping operation {decl.name} in {d}: \
          {cat.fullName} cannot be extended."
    else
      addCatOp cat (CatOp.ofOpDecl d decl)
  | .type decl =>
    addOpM q`Init.Type (.ofTypeDecl d decl)
  | .function decl =>
    addCatOp q`Init.Expr (CatOp.ofFunctionDecl d decl)
  | .metadata _ =>
    pure ()

def addDialect (d : Dialect) : CatOpM Unit :=
  d.declarations.forM (addDecl d.name)

/-- `CatOpMap` with only the Init dialect. -/
protected def init : CatOpMap :=
  let act := do
        addDialect initDialect
  let ((), s) := act { map := .ofArray #[(q`Init.Bool, #[])], errors := #[] }
  if s.errors.size > 0 then
    panic! s!"Error in Init dialect {s.errors}"
  else
    s.map

end CatOpMap

/--
Builds the category operation map from an array of dialects, collecting all
operations by category. Returns the map and any errors encountered.
-/
def buildCatOpMap (a : Array Dialect) : CatOpMap × Array String :=
  let act :=
        a.forM fun d =>
          if d.name = "Init" then pure () else CatOpMap.addDialect d
  let ((), s) := act { map := CatOpMap.init, errors := #[] }
  (s.map, s.errors)

/--
A set of categories.
-/
abbrev CategorySet := Std.HashSet CategoryName

namespace SyntaxCatF

/--
Invoke `f` over all atomic (no argument) category names in `c`.
-/
private
def foldOverAtomicCategories {α} (cat : SyntaxCat) (init : α)
    (f : α → QualifiedIdent → α) : α :=
  if cat.args.size = 0 then
    f init cat.name
  else
    cat.args.foldl (init := init) fun v a => foldOverAtomicCategories a v f
decreasing_by
  rw [sizeOf_spec cat]
  decreasing_tactic

end SyntaxCatF

structure WorkSet (α : Type _) [BEq α] [Hashable α] where
  set : Std.HashSet α
  pending : Array α

def WorkSet.ofSet {α} [BEq α] [Hashable α] (set : Std.HashSet α) : WorkSet α where
  set := set
  pending := set.toArray

def WorkSet.add {α} [BEq α] [Hashable α] (s : WorkSet α) (a : α) : WorkSet α :=
  let { set, pending } := s
  let (mem, set) := set.containsThenInsert a
  let pending := if mem then pending else pending.push a
  { set, pending }

def WorkSet.pop {α} [BEq α] [Hashable α] (s : WorkSet α)
    : Option (WorkSet α × α) :=
  let { set, pending } := s
  if p : pending.size > 0 then
    some ({ set, pending := pending.pop }, pending[pending.size -1])
  else
    none

/--
Add all atomic categories in bindings to set.
-/
def addArgCategories (s : CategorySet) (args : ArgDecls) : CategorySet :=
  args.foldl (init := s) fun s b =>
    b.kind.categoryOf.foldOverAtomicCategories (init := s) (·.insert ·)

partial def findUsedCategories.aux (m : CatOpMap)
    (s : WorkSet CategoryName) : CategorySet :=
  match s.pop with
  | none => s.set
  | some (s, c) =>
    match c with
    | q`Init.TypeP =>
      -- TypeP is a tagged union of Type and Expr, so using TypeP
      -- implicitly requires the Type category as well.
      findUsedCategories.aux m (s.add q`Init.Type)
    | _ =>
      let ops := m.getD c #[]
      let addArgs {α:Type} (f : α → CategoryName → α) (a : α)
          (op : CatOp) :=
        op.argDecls.foldl (init := a) fun r arg =>
          arg.cat.foldOverAtomicCategories (init := r) f
      let addName (pa : WorkSet CategoryName) (c : CategoryName) := pa.add c
      let s := ops.foldl (init := s) (addArgs addName)
      findUsedCategories.aux m s

/--
Computes the transitive closure of categories used by a dialect. Starts from
categories declared or referenced in the dialect and follows dependencies.
-/
def findUsedCategories (m : CatOpMap) (d : Dialect) : CategorySet :=
  let dname := d.name
  let cats := d.declarations.foldl (init := {}) fun s decl =>
    match decl with
    | .syncat decl => s.insert ⟨dname, decl.name⟩
    | .op decl =>
      let s := s.insert decl.category
      let s := addArgCategories s decl.argDecls
      s
    | .type _ =>
      s.insert q`Init.Type
    | .function decl =>
      let s := s.insert q`Init.Expr
      let s := addArgCategories s decl.argDecls
      s
    | .metadata _ => s
  findUsedCategories.aux m (.ofSet cats)

/--
Returns builtin constructors for abstract categories like `Init.Expr` and
`Init.Type`. These constructors are hardcoded and correspond to the AST types
`ExprF` and `TypeExprF` respectively.
-/
def makeBuiltinCtors (cat : QualifiedIdent) : Array DefaultCtor :=
  match cat with
  | q`Init.Expr =>
    #[
      .mk "fvar" none #[
        { name := "idx", cat := .atom .none q`Init.Num, addAnn := false }
      ],
      .mk "bvar" none #[
        { name := "idx", cat := .atom .none q`Init.Num, addAnn := false }
      ],
      .mk "app" none #[
        { name := "fn", cat := .atom .none q`Init.Expr, addAnn := false },
        { name := "arg", cat := .atom .none q`Init.Expr, addAnn := false }
      ]
    ]
  | q`Init.Type =>
    #[
      .mk "bvar" none #[
        { name := "idx", cat := .atom .none q`Init.Num, addAnn := false }
      ],
      .mk "tvar" none #[
        { name := "name", cat := .atom .none q`Init.Str, addAnn := false }
      ],
      .mk "fvar" none #[
        { name := "idx", cat := .atom .none q`Init.Num, addAnn := false },
        { name := "args",
          cat := { ann := .none, name := q`Init.Seq,
                   args := #[.atom .none q`Init.Type] },
          addAnn := false }
      ],
      .mk "arrow" none #[
        { name := "arg", cat := .atom .none q`Init.Type, addAnn := false },
        { name := "res", cat := .atom .none q`Init.Type, addAnn := false }
      ]
    ]
  | _ =>
    #[]

partial def genFreshName (s : Std.HashSet String) (base : String) (i : Nat) :=
  let name := s!"{base}_{i}"
  if name ∈ s then
    genFreshName s base (i+1)
  else
    name

/--
Converts a CatOp to a DefaultCtor, generating a unique Lean name if the
operation name conflicts with already-used names. Falls back to
dialect-qualified names (`dialect_name`) or numbered names (`name_0`) to
avoid collisions.
-/
def catOpToDefaultCtor (s : Std.HashSet String) (op : CatOp) : DefaultCtor :=
  let qid := op.name
  let leanName :=
    if qid.name ∈ s then
      let leanName := s!"{qid.dialect}_{qid.name}"
      if leanName ∈ s then
        genFreshName s qid.name 0
      else
        leanName
    else
      qid.name
  {
    leanNameStr := leanName,
    strataName := some op.name,
    argDecls := op.argDecls
  }

/--
Filters the category map to only include categories actually used by a
dialect, combining builtin and dialect-defined constructors with unique
naming to avoid conflicts.
-/
def CatOpMap.onlyUsedCategories (m : CatOpMap) (d : Dialect)
    : Array (QualifiedIdent × Array DefaultCtor) :=
  let usedSet := findUsedCategories m d
  m.fold (init := #[]) fun a cat ops =>
    if cat ∉ declaredCategories ∧ cat ∈ usedSet then
      let builtinCtors := makeBuiltinCtors cat
      -- Track Lean constructor names from builtins to avoid conflicts
      let usedLeanCtorNames : Std.HashSet String :=
        builtinCtors.foldl (init := {}) fun s c =>
          s.insert c.leanNameStr
      let (allCtors, _) :=
        ops.foldl (init := (builtinCtors, usedLeanCtorNames)) fun (a, s) op =>
            let dOp := catOpToDefaultCtor s op
            (a.push dOp, s.insert dOp.leanNameStr)
      a.push (cat, allCtors)
    else
      a

/-- Returns an identifier from a string. -/
def localIdent (name : String) : Ident :=
  let dName := .anonymous |>.str name
  .mk (.ident .none name.toRawSubstring dName [])

/--
Orders categories into strongly connected component groups using Tarjan's
algorithm. Categories in the same group may be mutually recursive.
-/
def orderedSyncatGroups (categories : Array (QualifiedIdent × Array DefaultCtor))
    : Array (Array (QualifiedIdent × Array DefaultCtor)) :=
  let n := categories.size
  let g : OutGraph n := OutGraph.empty n
  let identIndexMap : Std.HashMap QualifiedIdent (Fin n) :=
        n.fold (init := {}) fun i p m =>
          m.insert categories[i].fst ⟨i, p⟩
  let getIndex (nm : QualifiedIdent) : Option (Fin n) :=
        identIndexMap[nm]?
  let addArgIndices (cat : QualifiedIdent) (opName : String) (c : SyntaxCat)
      (init : OutGraph n) (resIdx : Fin n) : OutGraph n :=
        c.foldOverAtomicCategories (init := init) fun g q =>
          if q ∈ declaredCategories then
            g
          else
            match getIndex q with
            | some i => g.addEdge i resIdx
            | none =>
              panic! s!"{opName} in {cat} has unknown category {q.fullName}"
  let g : OutGraph n :=
        categories.foldl (init := g) fun g (cat, ops) => Id.run do
          let some resIdx := getIndex cat
            | panic! s!"Unknown category {cat}"
          match cat with
          | q`Init.TypeP =>
            let some typeIdx := getIndex q`Init.Type
              | panic! s!"Unknown category Init.Type."
            g.addEdge typeIdx resIdx
          | _ =>
            ops.foldl (init := g) fun g op =>
              op.argDecls.foldl (init := g) fun g arg =>
                addArgIndices cat op.leanNameStr arg.cat g resIdx
  let indices := OutGraph.tarjan g
  indices.map (·.map (categories[·]))

/--
Produce an identifier for `name` that is relative to `scope`.

Walks the fully-qualified `name` from the leaf toward the root, collecting
components.  When the remaining prefix matches `scope`, the collected
components form a relative identifier that resolves correctly inside the
current namespace.  If `scope` is never found, falls back to a `_root_`-
prefixed absolute identifier.
-/
def mkCategoryIdent (scope : Name) (name : Name) : Ident :=
  let mkDeclName (comp : List Name) : Ident :=
    let subName := comp.foldl (init := .anonymous) fun r nm => r ++ nm
    let sName := toString subName
    .mk (.ident .none sName.toRawSubstring subName [.decl name []])

  let rec aux : Name → List Name → Ident
    | .anonymous, _ => mkRootIdent name
    | n@(.num p' v), r =>
      if scope == n then
        mkDeclName r
      else
        aux p' (.num .anonymous v :: r)
    | n@(.str p' v), r =>
      if scope == n then
        mkDeclName r
      else
        aux p' (.str .anonymous v :: r)
  aux name []

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def scopedIdent (scope subName : Lean.Name) : Ident :=
  let name := scope ++ subName
  let nameStr := toString subName
  .mk (.ident .none nameStr.toRawSubstring subName [.decl name []])

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def mkScopedIdent {m} [Monad m] [Lean.MonadResolveName m]
    (subName : Lean.Name) : m Ident :=
  (scopedIdent · subName) <$> getCurrNamespace

/--
Returns the Lean name for a category, looking it up in the context's
category name map which handles naming conflicts.
-/
def getCategoryScopedName (cat : QualifiedIdent) : GenM Name := do
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return .mkSimple catName
  | none =>
    return panic! s!"getCategoryScopedName given {cat}"

/--
Returns a Lean identifier for a category type, either a builtin type name
or a generated category name.
-/
def getCategoryIdent (cat : QualifiedIdent) : GenM Ident := do
  if let some nm := declaredCategories[cat]? then
    return mkRootIdent nm
  currScopedIdent (← getCategoryScopedName cat)

/-- Returns a Lean term for a category type applied to the annotation type. -/
def getCategoryTerm (cat : QualifiedIdent) (annType : Ident) : GenM Term := do
  let catIdent ← mkScopedIdent (← getCategoryScopedName cat)
  return Lean.Syntax.mkApp catIdent #[annType]

/-- Returns a scoped identifier for a constructor in a category. -/
def getCategoryOpIdent (cat : QualifiedIdent) (name : Name) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ name

/--
Generates a Lean type term for a `SyntaxCat`, recursing into parameterized
categories. When `addAnn` is true, wraps primitive types in `Ann`.
-/
partial def genCatTypeTerm (annType : Ident) (c : SyntaxCat)
    (addAnn : Bool) : GenM Term := do
  let args ← c.args.mapM (genCatTypeTerm annType · true)
  match c.name, eq : args.size with
  | q`Init.CommaSepBy, 1 =>
    let inner := mkCApp ``Array #[args[0]]
    return if addAnn then mkCApp ``Ann #[inner, annType] else inner
  | q`Init.SpaceSepBy, 1 =>
    let inner := mkCApp ``Array #[args[0]]
    return if addAnn then mkCApp ``Ann #[inner, annType] else inner
  | q`Init.SpacePrefixSepBy, 1 =>
    let inner := mkCApp ``Array #[args[0]]
    return if addAnn then mkCApp ``Ann #[inner, annType] else inner
  | q`Init.Option, 1 =>
    let inner := mkCApp ``Option #[args[0]]
    return if addAnn then mkCApp ``Ann #[inner, annType] else inner
  | q`Init.Seq, 1 =>
    let inner := mkCApp ``Array #[args[0]]
    return if addAnn then mkCApp ``Ann #[inner, annType] else inner
  | cat, 0 =>
    match declaredCategories[cat]? with
    | some nm =>
      -- When `addAnn` is false (the argument has `@[unwrap]` metadata), use the
      -- bare Lean type (e.g., `Nat`).  Otherwise wrap in `Ann` to carry source
      -- annotations (e.g., `Ann Nat α`).
      if addAnn = false then
        pure <| mkRootIdent nm
      else
        pure <| mkCApp ``Ann #[mkRootIdent nm, annType]
    | none => do
      getCategoryTerm cat annType
  | f, _ => throwError "Unsupported {f.fullName}"

/-- Generates a Lean type term for a `SyntaxCat`, always wrapping in `Ann`. -/
partial def genCatTypeTermAnn (annType : Ident) (c : SyntaxCat) : GenM Term := do
  genCatTypeTerm annType c true

/--
Elaborates an array of commands, wrapping them in a mutual block if there
are multiple commands (for mutual recursion).
-/
def elabCommands (commands : Array Command) : CommandElabM Unit := do
  -- Record the message count before elaboration so we can detect whether
  -- elaboration produced any new non-trace diagnostics (errors/warnings).
  let messageCount := (← get).messages.unreported.size
  match p : commands.size with
  | 0 =>
    pure ()
  | 1 =>
    let i := commands[0]
    elabCommand =<< `($i:command)
  | _ =>
    elabCommand =<< `(command|
      mutual
      $commands:command*
      end
    )
  let unexpectedMessage b m :=
        if b.isSome then
          b
        else if m.kind = `trace then
          none
        else
          some m
  let hasNewMessage : Option Lean.Message :=
    (← get).messages.unreported.foldl (init := none)
      (start := messageCount) unexpectedMessage
  match hasNewMessage with
  | none => pure ()
  | some m =>
    logError m!"Command elaboration reported messages:\n {commands}\n  {m.kind}"

abbrev BracketedBinder := TSyntax ``Lean.Parser.Term.bracketedBinder

def explicitBinder (name : String) (typeStx : Term)
    : CommandElabM BracketedBinder := do
  let nameStx := localIdent name
  `(bracketedBinderF| ($nameStx : $typeStx))

/--
Generates Lean syntax for a single inductive constructor, including the
annotation parameter and all argument binders.
-/
def genCtorSyntax (annType : Ident) (op : DefaultCtor)
    : GenM (TSyntax ``ctor) := do
  let ctorId : Ident := localIdent op.leanNameStr
  let binders ← op.argDecls.mapM fun arg => do
        explicitBinder arg.name (← genCatTypeTerm annType arg.cat arg.addAnn)
  `(ctor| | $ctorId:ident (ann : $annType) $binders:bracketedBinder* )

/--
Generates an inductive type definition for a category, including builtin
constructors (for Init.Expr and Init.TypeP) and all dialect-defined
constructors.
-/
def genInductiveDef (cat : QualifiedIdent) (ctors : Array DefaultCtor)
    : GenM Command := do
  assert! cat ∉ declaredCategories
  let ident ← mkScopedIdent (← getCategoryScopedName cat)
  trace[Strata.generator] "Generating {ident}"
  let annType := localIdent "α"
  let builtinCtors : Array (TSyntax ``ctor) ←
        match cat with
        | q`Init.TypeP => do
          let typeIdent ← getCategoryTerm q`Init.Type annType
          pure #[
              ← `(ctor| | $(localIdent "expr"):ident (tp : $typeIdent)),
              ← `(ctor| | $(localIdent "type"):ident (tp : $annType))
          ]
        | _ =>
          pure #[]
  `(inductive $ident ($annType : Type) : Type where
    $builtinCtors:ctor*
    $(← ctors.mapM (genCtorSyntax annType)):ctor*
    deriving Repr)

/--
Maps a category to its corresponding AST type (ExprF, TypeExprF, ArgF, or
OperationF) for use in type signatures.
-/
def categoryToAstTypeIdent (cat : QualifiedIdent) (annType : Term) : Term :=
  let ident :=
    match cat with
    | q`Init.Expr => ``Strata.ExprF
    | q`Init.Type => ``Strata.TypeExprF
    | q`Init.TypeP => ``Strata.ArgF
    | _ => ``Strata.OperationF
  Lean.Syntax.mkApp (mkRootIdent ident) #[annType]

/-- Returns the identifier for a category's toAst function. -/
def toAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `toAst

/-- Returns the identifier for a category's ofAst function. -/
def ofAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst

/-- Wraps a value with an `Ann`-extracted annotation into an AST argument. -/
def mkAnnWithTerm (argCtor : Name) (annTerm v : Term) : Term :=
  mkCApp argCtor #[mkCApp ``Ann.ann #[annTerm], v]

/-- Destructures an `Ann` value into an AST argument with annotation and value. -/
def annToAst (argCtor : Name) (annTerm : Term) : Term :=
  mkCApp argCtor #[mkCApp ``Ann.ann #[annTerm], mkCApp ``Ann.val #[annTerm]]

mutual

/-- Generates `toAst` code for a sequence argument (maps over elements). -/
partial def toAstApplyArgSeq (v : Ident) (cat : SyntaxCat)
    (sepFormat : Name) : GenM Term := do
  assert! cat.args.size = 1
  let c := cat.args[0]!
  let e ← genFreshLeanName "e"
  let canE ← genIdentFrom e (canonical := true)
  let t ← toAstApplyArg e c
  let args := mkCApp ``Array.map #[
        ←`(fun ⟨$canE, _⟩ => $t),
        mkCApp ``Array.attach #[mkCApp ``Ann.val #[v]]
  ]
  let sepExpr := mkCApp sepFormat #[]
  return mkCApp ``ArgF.seq #[mkCApp ``Ann.ann #[v], sepExpr, args]

/-- Generates `toAst` conversion code for a single constructor argument. -/
partial def toAstApplyArg (vn : Name) (cat : SyntaxCat)
    (addAnn : Bool := true) : GenM Term := do
  let v := mkIdentFrom (←read).src vn
  match cat.name with
  | q`Init.Num =>
    if !addAnn then
      ``(ArgF.num default $v)
    else
      return annToAst ``ArgF.num v
  | q`Init.Bool => do
    if !addAnn then
      -- When unwrapped, v is a plain Bool. Create OperationF directly based on the value.
      let defaultAnn ← ``(default)
      let emptyArray ← ``(#[])
      let trueOp := mkCApp ``OperationF.mk #[defaultAnn, quote q`Init.boolTrue, emptyArray]
      let falseOp := mkCApp ``OperationF.mk #[defaultAnn, quote q`Init.boolFalse, emptyArray]
      let opExpr ← ``(if $v then $trueOp else $falseOp)
      ``(ArgF.op $opExpr)
    else
      -- When wrapped, v is already Ann Bool α
      let boolToAst := mkCApp ``Strata.OfAstM.toAstBool #[v]
      return mkCApp ``ArgF.op #[boolToAst]
  | q`Init.Ident =>
    if !addAnn then
      ``(ArgF.ident default $v)
    else
      return annToAst ``ArgF.ident v
  | q`Init.Str =>
    if !addAnn then
      ``(ArgF.strlit default $v)
    else
      return annToAst ``ArgF.strlit v
  | q`Init.Decimal =>
    if !addAnn then
      ``(ArgF.decimal default $v)
    else
      return annToAst ``ArgF.decimal v
  | q`Init.ByteArray =>
    if !addAnn then
      ``(ArgF.bytes default $v)
    else
      return annToAst ``ArgF.bytes v
  | cid@q`Init.Expr => do
    let toAst ← toAstIdentM cid
    return mkCApp ``ArgF.expr #[mkApp toAst #[v]]
  | q`Init.Type => do
    let toAst ← toAstIdentM cat.name
    ``(ArgF.type ($toAst $v))
  | q`Init.TypeP => do
    let toAst ← toAstIdentM cat.name
    ``($toAst $v)
  | q`Init.CommaSepBy => do
    toAstApplyArgSeq v cat ``SepFormat.comma
  | q`Init.SpaceSepBy => do
    toAstApplyArgSeq v cat ``SepFormat.space
  | q`Init.SpacePrefixSepBy => do
    toAstApplyArgSeq v cat ``SepFormat.spacePrefix
  | q`Init.Seq => do
    toAstApplyArgSeq v cat ``SepFormat.none
  | q`Init.Option => do
    assert! cat.args.size = 1
    let c := cat.args[0]!
    let e ← genFreshLeanName "e"
    let canE ← genIdentFrom e (canonical := true)
    let t ← toAstApplyArg e c
    let args := mkCApp ``Option.map #[
          ←`(fun ⟨$canE, _⟩ => $t),
          mkCApp ``Option.attach #[mkCApp ``Ann.val #[v]]
    ]
    return mkAnnWithTerm ``ArgF.option v args
  | qid => do
    assert! cat.args.size = 0
    let toAst ← toAstIdentM qid
    ``(ArgF.op ($toAst $v))

end

abbrev MatchAlt := TSyntax ``Lean.Parser.Term.matchAlt

/--
Generates pattern match cases for builtin constructors that should be
handled specially in toAst (Init.TypeP).
-/
def toAstBuiltinMatches (cat : QualifiedIdent) : GenM (Array MatchAlt) := do
  let src := (←read).src
  match cat with
  | q`Init.TypeP => do
    let (annC, annI) ← genFreshIdentPair "ann"
    let typeC ← getCategoryOpIdent cat `type
    let typeP : Term := mkApp typeC #[annC]
    let typeCat := Lean.Syntax.mkCApp ``SyntaxCatF.atom #[annI, quote q`Init.Type]
    let typeRhs := Lean.Syntax.mkCApp ``ArgF.cat #[typeCat]
    let typeN ← genFreshLeanName "type"
    let exprP := mkApp (← getCategoryOpIdent cat `expr) #[mkCanIdent src typeN]
    let exprRhs ← toAstApplyArg typeN (.atom .none q`Init.Type)
    return #[
      ← `(matchAltExpr| | $typeP => $typeRhs),
      ← `(matchAltExpr| | $exprP => $exprRhs)
    ]
  | _ =>
    return #[]

/--
Generates a pattern match case for converting a constructor to AST.

For `Init.Expr`, dialect-defined constructors are encoded as a chain of
`ExprF.fn` (the function head) followed by `ExprF.app` for each argument.
For example, `Expr.add ann x y` becomes
`ExprF.app ann (ExprF.app ann (ExprF.fn ann "add") x) y`.
The inverse `ofAst` function normalizes via HNF to recover the flat argument list.

For `Init.Type`, dialect-defined constructors are encoded as `TypeExprF.ident`
with an array of type arguments.

For general categories, constructors are encoded as `OperationF.mk` with an
array of `ArgF` values.

All three cases also handle builtin constructors (fvar, bvar, etc.) which map
directly to their corresponding AST node.
-/
def toAstMatch (cat : QualifiedIdent) (op : DefaultCtor) : GenM MatchAlt := do
  match cat with
  | q`Init.Expr =>
    let src := (←read).src
    let argDecls := op.argDecls
    let (annC, annI) ← genFreshIdentPair "ann"
    let ctor : Ident ← getCategoryOpIdent cat op.leanName
    -- Fresh Lean names for each constructor argument, used in generated code.
    let argLeanNames : Vector Lean.Name argDecls.size ← Vector.ofFnM fun i => do
          genFreshLeanName (argDecls[i]).name
    -- Canonical identifiers for pattern matching on the constructor arguments.
    let argTerms : Array Term :=
      argLeanNames.toArray.map fun nm => (mkCanIdent src nm : Term)
    let pat : Term ← ``($ctor $annC $argTerms:term*)
    let rhs ← match op.strataName with
    | some nm =>
      -- Dialect-defined expression constructor
      let init := mkCApp ``ExprF.fn #[annI, quote nm]
      Fin.foldlM argDecls.size (init := init) fun a ⟨i, ilt⟩ => do
        have h : i < argLeanNames.size := by omega
        let e ← toAstApplyArg argLeanNames[i] argDecls[i].cat argDecls[i].addAnn
        return Lean.Syntax.mkCApp ``ExprF.app #[annI, a, e]
    | none =>
      -- Builtin expression constructor (fvar, bvar, app)
      -- All builtin constructors defined in makeBuiltinCtors have addAnn := false
      match op.leanNameStr with
      -- Free variable reference: Expr.fvar ann idx → ExprF.fvar ann idx
      | "fvar" =>
        let isTrue _ := decideProp (argDecls.size = 1)
          | panic! "fvar expects 1 argument"
        pure <| mkCApp ``ExprF.fvar #[annI, mkIdentFrom src argLeanNames[0]]
      -- Bound variable reference: Expr.bvar ann idx → ExprF.bvar ann idx
      | "bvar" =>
        let isTrue _ := decideProp (argDecls.size = 1)
          | panic! "bvar expects 1 argument"
        pure <| mkCApp ``ExprF.bvar #[annI, mkIdentFrom src argLeanNames[0]]
      -- Function application: Expr.app ann fn arg →
      --   ExprF.app ann (toAst fn) (ArgF.expr (toAst arg))
      | "app" =>
        let isTrue _ := decideProp (argDecls.size = 2)
          | panic! "app expects 2 arguments"
        let toAst ← toAstIdentM q`Init.Expr
        let fnTerm := mkApp toAst #[mkIdentFrom src argLeanNames[0]]
        let argTerm :=
          mkCApp ``ArgF.expr #[mkApp toAst #[mkIdentFrom src argLeanNames[1]]]
        pure <| mkCApp ``ExprF.app #[annI, fnTerm, argTerm]
      | lname =>
        return panic! s!"Unknown builtin expression constructor: {lname}"
    `(matchAltExpr| | $pat => $rhs)
  | q`Init.Type =>
    let src := (←read).src
    let argDecls := op.argDecls
    let (annC, annI) ← genFreshIdentPair "ann"
    let ctor : Ident ← getCategoryOpIdent cat op.leanName
    let args ← argDecls.mapM fun arg => do
      return (← genFreshLeanName arg.name, arg.cat, arg.addAnn)
    let argTerms : Array Term := args.map fun p => mkCanIdent src p.fst
    let pat : Term ← ``($ctor $annC $argTerms:term*)
    let rhs ← match op.strataName with
    | some nm =>
      -- Dialect-defined type constructor
      let toAst ← toAstIdentM cat
      let argTerms ← arrayLit <| args.map fun (v, c, _addAnn) =>
        assert! c.isType
        Lean.Syntax.mkApp toAst #[mkIdentFrom src v]
      pure <| Lean.Syntax.mkCApp ``TypeExprF.ident #[annI, quote nm, argTerms]
    | none =>
      -- Builtin type constructor (bvar, tvar, fvar, arrow)
      -- All builtin constructors defined in makeBuiltinCtors have addAnn := false
      match op.leanNameStr with
      | "bvar" =>
        assert! args.size == 1
        let (indexV, _, _) := args[0]!
        pure <| mkCApp ``TypeExprF.bvar #[annI, mkIdentFrom src indexV]
      | "tvar" =>
        assert! args.size == 1
        let (nameV, _, _) := args[0]!
        pure <| mkCApp ``TypeExprF.tvar #[annI, mkIdentFrom src nameV]
      | "fvar" =>
        assert! args.size == 2
        let (fvarV, _, _) := args[0]!
        let (argsV, _, _) := args[1]!
        let toAst ← toAstIdentM cat
        let e ← genFreshLeanName "e"
        let canE ← genIdentFrom e (canonical := true)
        let argsExpr := mkCApp ``Array.map #[
          ← `(fun ⟨$canE, _⟩ => $(mkApp toAst #[mkIdentFrom src e])),
          mkCApp ``Array.attach #[mkIdentFrom src argsV]
        ]
        pure <| mkCApp ``TypeExprF.fvar #[annI, mkIdentFrom src fvarV, argsExpr]
      | "arrow" =>
        assert! args.size == 2
        let (argV, _, _) := args[0]!
        let (resV, _, _) := args[1]!
        let toAst ← toAstIdentM cat
        -- For arrow, both arg and res are Type, so recursively call toAst
        let argTerm := mkApp toAst #[mkIdentFrom src argV]
        let resTerm := mkApp toAst #[mkIdentFrom src resV]
        pure <| mkCApp ``TypeExprF.arrow #[annI, argTerm, resTerm]
      | lname =>
        return panic! s!"Unknown builtin type constructor: {lname}"
    `(matchAltExpr| | $pat => $rhs)
  | _ =>
    let src := (←read).src
    let argDecls := op.argDecls
    let (annC, annI) ← genFreshIdentPair "ann"
    let ctor : Ident ← getCategoryOpIdent cat op.leanName
    let args ← argDecls.mapM fun arg => do
      return (← genFreshLeanName arg.name, arg.cat, arg.addAnn)
    let argTerms : Array Term := args.map fun p => mkCanIdent src p.fst
    let pat : Term ← ``($ctor $annC $argTerms:term*)
    let mName ←
      match op.strataName with
      | some n => pure n
      | none => throwError s!"Internal: Operation requires strata name"
    let argTerms : Array Term ←
      args.mapM fun (nm, tp, addAnn) => toAstApplyArg nm tp addAnn
    let rhs := mkCApp ``OperationF.mk #[annI, quote mName, ← arrayLit argTerms]
    `(matchAltExpr| | $pat => $rhs)

/--
Generates the `toAst` function that converts from the generated category type
to the standard AST representation (ExprF, TypeExprF, OperationF, or ArgF).
-/
def generateToAstFunction (cat : QualifiedIdent)
    (ops : Array DefaultCtor) : GenM Command := do
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  let astType : Term := categoryToAstTypeIdent cat annType
  let cases ← toAstBuiltinMatches cat
  let cases : Array MatchAlt := cases ++ (← ops.mapM (toAstMatch cat))
  let toAst ← toAstIdentM cat
  trace[Strata.generator] "Generating {toAst}"
  let src := (←read).src
  let v ← genFreshLeanName "v"
  `(partial def $toAst {$annType : Type} [Inhabited $annType]
      ($(mkCanIdent src v) : $catTerm) : $astType :=
      match $(mkIdentFrom src v):ident with $cases:matchAlt*)

mutual

/-- Generates `ofAst` parsing code for an argument, always annotated. -/
partial def genOfAstArgTermAnn (varName : String) (cat : SyntaxCat) (e : Term)
    : GenM Term := do
  genOfAstArgTerm varName cat true e

/-- Generates `ofAst` parsing code for an argument with configurable annotation. -/
partial def genOfAstArgTerm (varName : String) (cat : SyntaxCat)
    (addAnn : Bool) (e : Term) : GenM Term := do
  match cat.name with
  | q`Init.Num =>
    if addAnn then
      ``(OfAstM.ofAnnNumM $e)
    else
      ``(OfAstM.ofNumM $e)
  | q`Init.Ident =>
    if addAnn then
      ``(OfAstM.ofAnnIdentM $e)
    else
      ``(OfAstM.ofIdentM $e)
  | q`Init.Str =>
    if addAnn then
      ``(OfAstM.ofAnnStrlitM $e)
    else
      ``(OfAstM.ofStrlitM $e)
  | q`Init.Decimal =>
    if addAnn then
      ``(OfAstM.ofAnnDecimalM $e)
    else
      ``(OfAstM.ofDecimalM $e)
  | q`Init.ByteArray =>
    if addAnn then
      ``(OfAstM.ofAnnBytesM $e)
    else
      ``(OfAstM.ofBytesM $e)
  | q`Init.Bool =>
    if addAnn then
      ``(OfAstM.ofAnnBoolM $e)
    else
      ``(OfAstM.ofBoolM $e)
  | cid@q`Init.Expr => do
    let (vc, vi) ← genFreshIdentPair <| varName ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofExpressionM $e fun $vc _ => $ofAst $vi)
  | cid@q`Init.Type => do
    let (vc, vi) ← genFreshIdentPair varName
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofTypeM $e fun $vc _ => $ofAst $vi)
  | cid@q`Init.TypeP => do
    let ofAst ← ofAstIdentM cid
    pure <| mkApp ofAst #[e]
  | q`Init.CommaSepBy => do
    genOfAstSeqArgTerm varName cat e ``SepFormat.comma
  | q`Init.SpaceSepBy => do
    genOfAstSeqArgTerm varName cat e ``SepFormat.space
  | q`Init.SpacePrefixSepBy => do
    genOfAstSeqArgTerm varName cat e ``SepFormat.spacePrefix
  | q`Init.Seq => do
    genOfAstSeqArgTerm varName cat e ``SepFormat.none
  | q`Init.Option => do
    let c := cat.args[0]!
    let (vc, vi) ← genFreshIdentPair varName
    let body ← genOfAstArgTermAnn varName c vi
    ``(OfAstM.ofOptionM $e fun $vc _ => $body)
  | cid => do
    assert! cat.args.isEmpty
    let (vc, vi) ← genFreshIdentPair varName
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofOperationM $e fun $vc _ => $ofAst $vi)

where
  genOfAstSeqArgTerm (varName : String) (cat : SyntaxCat) (e : Term)
      (sepFormat : Name) : GenM Term := do
    let c := cat.args[0]!
    let (vc, vi) ← genFreshIdentPair varName
    let body ← genOfAstArgTermAnn varName c vi
    let sepFormatTerm := mkCApp sepFormat #[]
    ``(OfAstM.ofSeqM $sepFormatTerm $e fun $vc _ => $body)

end

/--
Generates code to parse arguments from an ArgF array, returning the parsed
identifiers and the do-notation statements that bind them.
-/
def ofAstArgs (argDecls : Array GenArgDecl) (argsVar : Ident)
    : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let arg := argDecls[i]
    let (vc, vi) ← genFreshIdentPair <| arg.name ++ "_bind"
    let av ← ``($argsVar[$(quote i)])
    let rhs ← genOfAstArgTerm arg.name arg.cat arg.addAnn av
    let stmt ← `(doSeqItem| let $vc ← $rhs:term)
    return (vi, stmt)
  return args.unzip

/--
Generates a pattern match case for the name index lookup in ofAst.
Maps operation names to numeric indices for efficient matching.
-/
def ofAstMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat)
    (op : DefaultCtor) (rhs : Term) : GenM MatchAlt := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanNameStr}"
  let some nameIndex := nameIndexMap[name]?
    | return panic! s!"Unbound operator name {name}"
  `(matchAltExpr| | Option.some $(quote nameIndex) => $rhs)

/--
Generates the right-hand side of a match case for parsing an Init.Expr
operation from AST, including argument count checking and parsing.
-/
def ofAstExprMatchRhs (cat : QualifiedIdent) (annI argsVar : Ident)
    (op : DefaultCtor) : GenM Term:= do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let some nm := op.strataName
    | return panic! s!"Missing name for {op.leanName}"
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  let checkExpr ←
    ``(OfAstM.checkArgCount $(quote nm) $(quote argCount) $(argsVar))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    pure ($ctorIdent $annI $parsedArgs:term*))

/--
Generates a complete match case for parsing an Init.Expr operation,
combining name index matching with argument parsing.
-/
def ofAstExprMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat)
      (cat : QualifiedIdent) (annI : Ident) (argsVar : Ident)
      (op : DefaultCtor) : GenM MatchAlt := do
  let rhs ← ofAstExprMatchRhs cat annI argsVar op
  ofAstMatch nameIndexMap op rhs

/--
Generates code to parse type arguments (which are always Init.Type) from
an array, recursively calling the Type ofAst function.
-/
def ofAstTypeArgs (argDecls : Array GenArgDecl) (argsVar : Ident)
    : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let ofAst ← ofAstIdentM q`Init.Type
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let arg := argDecls[i]
    let v ← genFreshLeanName arg.name
    let src := (←read).src
    let rhs ← ``($ofAst $argsVar[$(quote i)])
    let stmt ← `(doSeqItem| let $(mkIdentFrom src v true) ← $rhs:term)
    return (mkIdentFrom src v, stmt)
  return args.unzip

/--
Generates the right-hand side for parsing an Init.Type constructor,
checking argument count and parsing type arguments.
-/
def ofAstTypeMatchRhs (cat : QualifiedIdent) (ann argsVar : Ident)
    (op : DefaultCtor) : GenM Term := do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let (parsedArgs, stmts) ← ofAstTypeArgs argDecls argsVar
  let checkExpr ←
    ``(OfAstM.checkTypeArgCount $(quote argDecls.size) $(argsVar))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    pure <| $ctorIdent $ann $parsedArgs:term*)

/--
Generates the right-hand side for parsing a general operation (non-Expr,
non-Type), checking argument count and parsing arbitrary arguments.
-/
def ofAstOpMatchRhs (cat : QualifiedIdent) (annI argsVar : Ident)
    (op : DefaultCtor) : GenM Term := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanNameStr}"
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let checkExpr ←
    ``(OfAstM.checkArgCount $(quote name) $(quote argCount) $argsVar)
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    return $ctorIdent $annI $parsedArgs:term*)

/--
Creates a mapping from qualified operation names to numeric indices for
efficient pattern matching in ofAst. Returns the map, the identifier for
the generated constant, and the definition command.
-/
def createNameIndexMap (cat : QualifiedIdent) (ops : Array DefaultCtor)
    : GenM (Std.HashMap QualifiedIdent Nat × Ident × Command) := do
  let nameIndexMap := ops.foldl (init := {}) fun map op =>
    match op.strataName with
    | none => map  -- Skip operators without a name
    | some name => map.insert name map.size  -- Assign the next available index
  let ofAstNameMap ←
    currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst.nameIndexMap
  let cmd ← `(def $ofAstNameMap : Std.HashMap Strata.QualifiedIdent Nat :=
    Std.HashMap.ofList $(quote nameIndexMap.toList))
  pure (nameIndexMap, ofAstNameMap, cmd)

/--
Wraps an ofAst function body in the appropriate function definition with
correct type signature and constraints.
-/
def mkOfAstDef (cat : QualifiedIdent) (ofAst : Ident) (v : Name)
    (rhs : Term) : GenM Command := do
  let src := (←read).src
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  `(partial def $ofAst {$annType : Type} [Inhabited $annType]
      [Repr $annType]
      ($(mkCanIdent src v) : $(categoryToAstTypeIdent cat annType))
      : OfAstM $catTerm := $rhs)

/--
Generates the `ofAst` function that converts from the standard AST
representation back to the generated category type. Returns auxiliary
commands (like name index maps) and the main ofAst definition.
-/
def generateOfAstFunction (cat : QualifiedIdent) (ops : Array DefaultCtor)
    : GenM (Array Command × Command) := do
  let src := (←read).src
  let ofAst ← ofAstIdentM cat
  trace[Strata.generator] "Generating {ofAst}"
  match cat with
  | q`Init.Expr =>
    let v ← genFreshLeanName "v"
    let (annC, annI) ← genFreshIdentPair "ann"
    -- `argsVar` is the Name used in pattern position (canonical) to bind the
    -- HNF argument array (`vnf.args.val`).  `argsIdent` is the corresponding
    -- term-side Ident used to reference those arguments in match RHS code.
    let argsVar ← genFreshLeanName "args"
    let argsIdent := mkIdentFrom src argsVar
    -- Filter to only dialect-defined expressions (with strataName)
    let dialectOps := ops.filter (·.strataName.isSome)
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat dialectOps
    let bvarCtor ← getCategoryOpIdent cat `bvar
    let fvarCtor ← getCategoryOpIdent cat `fvar
    let appCtor ← getCategoryOpIdent cat `app
    let cases : Array MatchAlt ←
      dialectOps.mapM (ofAstExprMatch nameIndexMap cat annI argsIdent)
    -- `toAst` encodes expressions as nested ExprF.app chains.  Here we
    -- normalize the input to head-normal form (HNF): a head (fn/bvar/fvar)
    -- plus a flat argument array.  For dialect-defined functions we look up
    -- the head name in a precomputed index map.  For builtin heads
    -- (bvar/fvar) we reconstruct the generated constructor, then fold any
    -- remaining HNF arguments back into Expr.app chains (this handles
    -- partial application of builtins).
    let foldArgs ← `(fun init =>
      ($argsIdent).foldlM (init := init) fun acc arg =>
        match arg with
        | .expr e => do
          let e' ← $ofAst:ident e
          pure ($appCtor default acc e')
        | _ => OfAstM.throwExpectedExpr arg)
    let rhs ←
      `(let vnf := ($(mkIdentFrom src v)).hnf
        let $(mkCanIdent src argsVar) := vnf.args.val
        let foldArgs := $foldArgs
        match (vnf.fn) with
        | Strata.ExprF.bvar ann idx => do
          foldArgs ($bvarCtor ann idx)
        | Strata.ExprF.fvar ann i => do
          foldArgs ($fvarCtor ann i)
        | Strata.ExprF.fn $annC fnId =>
          (match ($ofAstNameMap[fnId]?) with
          $cases:matchAlt*
          | _ => OfAstM.throwUnknownIdentifier $(quote cat) fnId)
        | _ => pure (panic! "Unexpected argument"))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs)
  | q`Init.Type =>
    let v ← genFreshLeanName "v"
    let (argsC, argsI) ← genFreshIdentPair "args"
    let (annC, annI) ← genFreshIdentPair "ann"
    -- Filter to only dialect-defined types (with strataName)
    let dialectOps := ops.filter (·.strataName.isSome)
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat dialectOps
    let cases : Array MatchAlt ← dialectOps.mapM fun op =>
      ofAstMatch nameIndexMap op =<< ofAstTypeMatchRhs cat annI argsI op
    -- Generate constructors for builtin type constructors
    let bvarCtor ← getCategoryOpIdent cat `bvar
    let tvarCtor ← getCategoryOpIdent cat `tvar
    let fvarCtor ← getCategoryOpIdent cat `fvar
    let arrowCtor ← getCategoryOpIdent cat `arrow
    let ofAst ← ofAstIdentM cat
    -- Builtin constructors defined in makeBuiltinCtors all have addAnn := false
    let rhs ←
      `(match ($(mkIdentFrom src v)) with
        | .ident $annC typeIdent $argsC =>
          (match ($ofAstNameMap[typeIdent]?) with
          $cases:matchAlt*
          | _ => OfAstM.throwUnknownIdentifier $(quote cat) typeIdent)
        | .bvar ann index => pure ($bvarCtor ann index)
        | .tvar ann name => pure ($tvarCtor ann name)
        | .fvar ann fvar args => do
          let args ← args.mapM fun arg => $ofAst:ident arg
          pure ($fvarCtor ann fvar args)
        | .arrow ann arg res => do
          let arg ← $ofAst:ident arg
          let res ← $ofAst:ident res
          pure ($arrowCtor ann arg res))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs)
  | q`Init.TypeP =>
    let v ← genFreshLeanName "v"
    let catCtor ← getCategoryOpIdent cat `type
    let exprCtor ← getCategoryOpIdent cat `expr
    let typeOfAst ← ofAstIdentM q`Init.Type
    let vIdent := mkIdentFrom src v
    let rhs ← ``(
      OfAstM.matchTypeParamOrType $vIdent $catCtor
        (fun tp => $exprCtor <$> $typeOfAst tp)
    )
    pure (#[], ← mkOfAstDef cat ofAst v rhs)
  | _ =>
    let v ← genFreshLeanName "v"
    let (annC, annI) ← genFreshIdentPair "ann"
    let vi := mkIdentFrom src v
    let (argsC, argsI) ← genFreshIdentPair "args"
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let cases : Array MatchAlt ← ops.mapM fun op =>
      ofAstMatch nameIndexMap op =<< ofAstOpMatchRhs cat annI argsI op
    let rhs ← `(
      let $argsC := OperationF.args $vi
      let $annC := OperationF.ann $vi
      match ($ofAstNameMap[OperationF.name $vi]?) with
      $cases:matchAlt*
      | _ => OfAstM.throwUnknownIdentifier $(quote cat) (OperationF.name $vi))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs)

abbrev InhabitedSet := Std.HashSet QualifiedIdent

/--
Generates an `Inhabited` instance for a category if possible, and adds it to the inhabited set.

This function attempts to find a constructor whose arguments are all inhabited types.
A type is considered inhabited if:
- It's a sequence type (`Init.Seq`, `Init.CommaSepBy`, `Init.SpaceSepBy`, `Init.SpacePrefixSepBy`)
  which are always inhabited via empty arrays
- It's an `Init.Option` type which is always inhabited via `none`
- It's already in the `InhabitedSet` from previous processing

When a suitable constructor is found, this generates:
```lean
instance [Inhabited α] : Inhabited (CategoryName α) where
  default := constructor default default ...
```

The function short-circuits on the first viable constructor found.

If the category is already in the inhabited set, this function does nothing.
-/
def tryMakeInhabited (cat : QualifiedIdent) (ops : Array DefaultCtor)
    : StateT InhabitedSet GenM Unit := do
  if cat ∈ (←get) then
    return ()
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  for op in ops do
    let inhabited ← get
    let argsInhabited := op.argDecls.all fun arg =>
        match arg.cat.name with
        | q`Init.Seq => true
        | q`Init.CommaSepBy => true
        | q`Init.SpaceSepBy => true
        | q`Init.SpacePrefixSepBy => true
        | q`Init.Option => true
        | c => c ∈ inhabited
    if !argsInhabited then
      continue
    let ctor : Term ← getCategoryOpIdent cat op.leanName
    let d := Lean.mkCIdent ``default
    let e := Lean.Syntax.mkApp ctor (Array.replicate (op.argDecls.size + 1) d)
    StateT.lift <| runCmd <|
      elabCommand =<< `(instance [Inhabited $annType] : Inhabited $catTerm where default := $e)
    modify (·.insert cat)
    return
  if cat == q`Init.Expr then
    @panic _ ⟨pure ()⟩ s!"Expr is not inhabited: {ops.size}"

/--
Iteratively generates `Inhabited` instances for all categories in a group that can be inhabited.

This function repeatedly processes the group of categories until no new inhabited instances
can be generated (fixed-point iteration). This is necessary because:

1. Some categories may have constructors that depend on other categories in the same group
2. Once a category becomes inhabited, other categories depending on it may also become inhabitable
3. The order of processing doesn't matter due to the fixed-point approach

The algorithm:
1. Iterate through all categories, calling `tryMakeInhabited` for each
2. If any new category was added to the inhabited set (size increased), repeat
3. Stop when no progress is made (no new inhabited instances generated)

This ensures that all possible inhabited instances are generated for mutually-recursive
or interdependent category groups.
-/
partial def generateInhabitedInstances (group : Array (QualifiedIdent × Array DefaultCtor))
    (s : InhabitedSet) : GenM InhabitedSet := do
  let initSize := s.size
  let sm ← group.foldlM (init := s) fun s (cat, ctors) => do
    let (_, s) ← tryMakeInhabited cat ctors s
    pure s
  let finalSize := sm.size
  if finalSize > initSize then
    generateInhabitedInstances group sm
  else
    pure sm

/--
Generates all code for a list of categories: inductive types, Inhabited
instances, toAst and ofAst functions. Processes categories in topologically
sorted groups to handle dependencies correctly.
-/
def generateCategoryCode
    (categories : Array (QualifiedIdent × Array DefaultCtor))
    : GenM Unit := do
  let mut inhabitedCats : InhabitedSet :=
    Std.HashSet.ofArray
      declaredCategories.keysArray
  for allCtors in orderedSyncatGroups categories do
    let s ←
      withTraceNode `Strata.generator (fun _ =>
        return m!"Declarations group: {allCtors.map (·.fst)}") do
        -- TODO: Currently all toAst/ofAst functions are declared `partial`.
        -- The commented-out code below detects whether a group is actually
        -- recursive, which would allow non-recursive groups to use
        -- non-partial definitions (enabling the Lean kernel to reduce them).
        -- let newCats := Std.HashSet.ofArray <| allCtors.map (·.fst)
        -- let _isRecursive := allCtors.any fun (_, ops) =>
        --       ops.any fun op =>
        --         op.argDecls.any fun (_, c) =>
        --           c.foldOverAtomicCategories (init := false)
        --             fun b qid => b || qid ∈ newCats
        let cats := allCtors.map (·.fst)
        profileitM Lean.Exception s!"Generating inductives {cats}" (← getOptions) do
          let inductives ← allCtors.mapM fun (cat, ctors) => do
            assert! q`Init.Num ≠ cat
            assert! q`Init.Str ≠ cat
            genInductiveDef cat ctors
          runCmd <| elabCommands inductives
        let inhabitedCats2 ←
          profileitM Lean.Exception s!"Generating inhabited {cats}" (← getOptions) do
            generateInhabitedInstances allCtors inhabitedCats
        let inhabitedCats := inhabitedCats2
        profileitM Lean.Exception s!"Generating toAstDefs {cats}" (← getOptions) do
          let toAstDefs ← allCtors.mapM fun (cat, ctors) => do
            generateToAstFunction cat ctors
          runCmd <| elabCommands toAstDefs
        profileitM Lean.Exception s!"Generating ofAstDefs {cats}" (← getOptions) do
          let ofAstDefs ← allCtors.mapM fun (cat, ctors) => do
            let (cmds, d) ← generateOfAstFunction cat ctors
            (cmds.forM elabCommand : CommandElabM Unit)
            pure d
          runCmd <| elabCommands ofAstDefs
        pure inhabitedCats
    inhabitedCats := s

/--
Runs a code generator computation with the appropriate context, including
source location, category name mappings, and eta configuration.
-/
def runGenerator {α} (src : Lean.Syntax) (pref : String)
    (catNames : Array QualifiedIdent) (m : GenM α)
    : CommandElabM α := do
  let catNameCounts : Std.HashMap String Nat :=
    catNames.foldl (init := {}) fun m k =>
      m.alter k.name (fun v => some (v.getD 0 + 1))
  let categoryNameMap := catNames.foldl (init := {}) fun m i =>
    let name :=
          if catNameCounts.getD i.name 0 > 1 then
            s!"{i.dialect}_{i.name}"
          else if i.name ∈ reservedCategories then
            s!"{pref}{i.name}"
          else
            i.name
    m.insert i name
  let ctx : GenContext := {
    src := src
    categoryNameMap := categoryNameMap
  }
  m ctx

/--
`#strata_gen ident` generates an AST for the dialect `ident`.

This includes functions for converting from the standard AST to the generated AST
and back.
-/
syntax (name := strataGenCmd) "#strata_gen" ident : command -- declare the syntax

@[command_elab strataGenCmd]
public def genAstImpl : CommandElab := fun stx =>
  match stx with
  | `(command| #strata_gen $dialectStx) => do
    let .str .anonymous dialectName := dialectStx.getId
      | throwErrorAt dialectStx s!"Expected dialect name"
    let loader := dialectExt.getState (← getEnv) |>.loaded
    let some d := loader.dialects[dialectName]?
      | throwErrorAt dialectStx "Missing dialect {dialectName}"

    let depDialectNames := generateDependentDialects (loader.dialects[·]?) dialectName
    let usedDialects ← depDialectNames.mapM fun nm =>
          match loader.dialects[nm]? with
          | some d => pure d
          | none => panic! s!"Missing dialect {nm}"
    let (cm, errs) := buildCatOpMap usedDialects
    if errs.size > 0 then
      for e in errs do
        logError e
      return
    let cats := cm.onlyUsedCategories d
    let catNames := cats.map (·.fst)
    runGenerator stx dialectName catNames (generateCategoryCode cats)
  | _ =>
    throwUnsupportedSyntax

end Strata
end
