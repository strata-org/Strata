/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Elab.Command
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.GenTrace
import Strata.DDM.Integration.Lean.OfAstM
import Strata.DDM.Integration.Lean.BoolConv
import Strata.DDM.Util.Graph.Tarjan

open Lean (Command Name Ident Term TSyntax addAndCompile getEnv logError)
open Lean (mkApp2 mkApp3 mkAppN mkCIdent mkConst mkIdentFrom)
open Lean (profileitM quote withTraceNode)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand liftCoreM)
open Lean.MonadOptions (getOptions)
open Lean.MonadResolveName (getCurrNamespace)
open Lean.Parser.Command (ctor)
open Lean.Parser.Term (bracketedBinderF doSeqItem matchAltExpr)
open Lean.Parser.Termination (terminationBy suffix)
open Lean.Syntax (mkApp mkCApp mkStrLit)

namespace Strata

namespace Lean

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
private def mkScopedIdent (scope : Name) (subName : Lean.Name) : Ident :=
  let fullName := scope ++ subName
  let nameStr := toString subName
  .mk (.ident .none nameStr.toSubstring subName [.decl fullName []])

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
private def currScopedIdent {m} [Monad m] [Lean.MonadResolveName m] (subName : Lean.Name) : m Ident := do
  (mkScopedIdent · subName) <$> getCurrNamespace

end Lean

open Lean (currScopedIdent)

private def arrayLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#[ $as:term,* ] : Array _) )

private def vecLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#v[ $as:term,* ] : Vector _ $(quote as.size)) )

abbrev LeanCategoryName := Lean.Name

structure GenContext where
  -- Syntax for #strata_gen for source location purposes.
  src : Lean.Syntax
  /--
  Maps category identifiers to their relative Lean name.
  -/
  categoryNameMap : Std.HashMap QualifiedIdent Name
  exprHasEta : Bool

abbrev GenM := ReaderT GenContext CommandElabM

def runCmd {α} (act : CommandElabM α) : GenM α := fun _ => act

/-- Create a fresh name. -/
private def genFreshLeanName (s : String) : GenM Name := do
  let fresh ← modifyGet fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  let n : Name := .anonymous |>.str s
  return Lean.addMacroScope (← getEnv).mainModule n fresh

/-- Create a fresh name. -/
private def genFreshIdentPair (s : String) : GenM (Ident × Ident) := do
  let name ← genFreshLeanName s
  let src := (←read).src
  return (mkIdentFrom (canonical := true) src name, mkIdentFrom src name)

/-- Create a canonical identifier. -/
def mkCanIdent (src : Lean.Syntax) (val : Name) : Ident :=
  mkIdentFrom src val true

/-- Create a identifier from a name. -/
private def genIdentFrom (name : Name) (canonical : Bool := false) : GenM Ident := do
  return mkIdentFrom (←read).src name canonical

def reservedCats : Std.HashSet String := { "Type" }

structure OrderedSet (α : Type _) [BEq α] [Hashable α] where
  set : Std.HashSet α
  values : Array α

namespace OrderedSet

def empty [BEq α] [Hashable α] : OrderedSet α := { set := {}, values := #[]}

partial def addAtom {α} [BEq α] [Hashable α] (s : OrderedSet α) (a : α) : OrderedSet α :=
  if a ∈ s.set then
    s
  else
    { set := s.set.insert a, values := s.values.push a }

partial def addPostTC {α} [BEq α] [Hashable α] (next : α → Array α) (s : OrderedSet α) (a : α) : OrderedSet α :=
  if a ∈ s.set then
    s
  else
    let as := next a
    let s := { s with set := s.set.insert a }
    let s := as.foldl (init := s) (addPostTC next)
    { s with values := s.values.push a }

end OrderedSet

def generateDependentDialects (lookup : String → Option Dialect) (name : DialectName) : Array DialectName :=
  let s : OrderedSet DialectName := .empty
  let s := s.addAtom initDialect.name
  let next (name : DialectName) : Array DialectName :=
      match lookup name with
      | some d => d.imports
      | none => #[]
  s.addPostTC next name |>.values

def resolveDialects (lookup : String → Option Dialect) (dialects : Array DialectName) : Except String (Array Dialect) := do
  dialects.mapM fun name =>
    match lookup name with
    | none => throw s!"Unknown dialect {name}"
    | some d => pure d

abbrev CategoryName := QualifiedIdent

/--
Forbidden categories are categories that
-/
def forbiddenCategories : Std.HashSet CategoryName := {
  q`Init.TypeExpr,
  q`Init.BindingType,
  q`StrataDDL.Binding
}

private def forbiddenWellDefined : Bool :=
  forbiddenCategories.all fun nm =>
    match nm.dialect with
    | "Init" => nm.name ∈ initDialect
    | "StrataDDL" => nm.name ∈ StrataDDL
    | _ => false

#guard "BindingType" ∈ initDialect.cache
#guard "Binding" ∈ StrataDDL.cache
#guard forbiddenWellDefined

/--
Special categories ignore operations introduced in Init, but are populated
with operators via functions/types.
-/
def specialCategories : Std.HashSet CategoryName := {
  q`Init.Expr,
  q`Init.Type,
  q`Init.TypeP
}

/--
Argument declaration for code generation.
-/
structure GenArgDecl where
  name : String
  cat : SyntaxCat
  unwrap : Bool := false

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
  strataName : Option QualifiedIdent := none
  /-- Whether the generated constructor should add the annotation.  -/
  includeAnn : Bool := true
  /--
  Argument declarations
  -/
  argDecls : Array GenArgDecl
  /--
  Either annotations are included or there is a single argument we can get
  the annotation from.
  -/
  includeAnnInvariant :
    includeAnn ∨
      if p : argDecls.size = 1 then
        ¬(argDecls[0]'(p ▸ Nat.zero_lt_one)).unwrap
      else
        false := by simp

def DefaultCtor.leanName (c : DefaultCtor) : Name := .str .anonymous c.leanNameStr

/--
An operation at the category level.
-/
structure CatOp where
  name : QualifiedIdent
  argDecls : Array GenArgDecl

namespace CatOp

partial def checkCat (op : QualifiedIdent) (c : SyntaxCat) : Except String Unit := do
  c.args.forM (checkCat op)
  let f := c.name
  if f ∈ forbiddenCategories then
    throw s!"{op.fullName} refers to unsupported category {f.fullName}."

def ofArgDecl (op : QualifiedIdent) (d : ArgDecl) : Except String GenArgDecl := do
  let cat ←
    match d.kind with
    | .type tp =>
      pure <| .atom tp.ann q`Init.Expr
    | .cat c =>
      checkCat op c
      pure c
  -- Check if unwrap metadata is present
  let unwrap := q`StrataDDL.unwrap ∈ d.metadata
  pure { name := d.ident, cat, unwrap }

def ofOpDecl (d : DialectName) (o : OpDecl) : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls.toArray |>.mapM (ofArgDecl name)
  return { name, argDecls }

def ofTypeDecl (d : DialectName) (o : TypeDecl) : CatOp := {
  name := ⟨d, o.name⟩
  argDecls := o.argNames |>.map fun anm => { name := anm.val, cat := .atom .none q`Init.Type }
}

def ofFunctionDecl (d : DialectName) (o : FunctionDecl) : Except String CatOp := do
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

def mkRootIdent (name : Name) : Ident :=
  let rootName := `_root_ ++ name
  .mk (.ident .none name.toString.toSubstring rootName [.decl name []])

/--
This maps category names in the Init dialect that are already declared
to their fully qualified Lean name.
-/
def declaredCategories : Std.HashMap CategoryName Name := .ofList [
  (q`Init.Ident, ``String),
  (q`Init.Num, ``Nat),
  (q`Init.Decimal, ``Decimal),
  (q`Init.Str, ``String),
  (q`Init.ByteArray, ``ByteArray),
  (q`Init.Bool, ``Bool)
]

def ignoredCategories : Std.HashSet CategoryName :=
  .ofList declaredCategories.keys ∪ forbiddenCategories

namespace CatOpMap

def addCat (m : CatOpMap) (cat : CategoryName) : CatOpMap :=
  -- Allow Init.Bool even though it's in ignoredCategories
  if cat ∈ ignoredCategories && cat ≠ q`Init.Bool then
    m
  else
    m.insert cat #[]

def addOp (m : CatOpMap) (cat : CategoryName) (op : CatOp) : CatOpMap :=
  assert! cat ∈ m
  m.modify cat (fun a => a.push op)

def addCatM (cat : CategoryName) : CatOpM Unit := do
  modify fun s => { s with map := s.map.addCat cat }

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
  | .syncat decl =>
    addCatM ⟨d, decl.name⟩
  | .op decl => do
    -- Allow Init.Bool operators even though Bool is in declaredCategories
    let isBoolOp := decl.category == q`Init.Bool && (decl.name == "boolTrue" || decl.name == "boolFalse")
    if (decl.category ∈ ignoredCategories ∨ decl.category ∈ specialCategories) && !isBoolOp then
      if d ≠ "Init" then
        .addError s!"Skipping operation {decl.name} in {d}: {decl.category.fullName} cannot be extended."
    else
      addCatOp decl.category (CatOp.ofOpDecl d decl)
  | .type decl =>
    addOpM q`Init.Type (.ofTypeDecl d decl)
  | .function decl =>
    addCatOp q`Init.Expr (CatOp.ofFunctionDecl d decl)
  | .metadata _ =>
    pure ()

def addDialect (d : Dialect) : CatOpM Unit :=
  d.declarations.forM (addDecl d.name)

/- `CatopMap` with onl initial dialect-/
protected def init : CatOpMap :=
  let act := do
        addDialect initDialect
  let ((), s) := act { map := {}, errors := #[] }
  if s.errors.size > 0 then
    panic! s!"Error in Init dialect {s.errors}"
  else
    s.map

end CatOpMap

def mkCatOpMap (a : Array Dialect) : CatOpMap × Array String :=
  let act :=
        a.forM fun d => if d.name = "Init" then pure () else CatOpMap.addDialect d
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
def foldOverAtomicCategories {α} (cat : SyntaxCat) (init : α)  (f : α  → QualifiedIdent → α) : α :=
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

def WorkSet.ofSet [BEq α] [Hashable α] (set : Std.HashSet α) : WorkSet α where
  set := set
  pending := set.toArray

def WorkSet.add [BEq α] [Hashable α] (s : WorkSet α) (a : α) : WorkSet α :=
  let { set, pending } := s
  let (mem, set) := set.containsThenInsert a
  let pending := if mem then pending else pending.push a
  { set, pending }

def WorkSet.pop [BEq α] [Hashable α] (s : WorkSet α) : Option (WorkSet α × α) :=
  let { set, pending } := s
  if p : pending.size > 0 then
    some ({ set, pending := pending.pop }, pending[pending.size -1])
  else
    none

/--
Add all atomic categories in bindings to set.
-/
private def addArgCategories (s : CategorySet) (args : ArgDecls) : CategorySet :=
  args.foldl (init := s) fun s b =>
    b.kind.categoryOf.foldOverAtomicCategories (init := s) (·.insert ·)

partial def mkUsedCategories.aux (m : CatOpMap) (s : WorkSet CategoryName) : CategorySet :=
  match s.pop with
  | none => s.set
  | some (s, c) =>
    let ops := m.getD c #[]
    let addArgs {α:Type} (f : α → CategoryName → α) (a : α) (op : CatOp) :=
      op.argDecls.foldl (init := a) fun r arg => arg.cat.foldOverAtomicCategories (init := r) f
    let addName (pa : WorkSet CategoryName) (c : CategoryName) := pa.add c
    let s := ops.foldl (init := s) (addArgs addName)
    mkUsedCategories.aux m s

def mkUsedCategories (m : CatOpMap) (d : Dialect) : CategorySet :=
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
  mkUsedCategories.aux m (.ofSet cats)

def mkStandardCtors (exprHasEta : Bool) (cat : QualifiedIdent) : Array DefaultCtor :=
  match cat with
  | q`Init.Expr =>
    let fvar := {
      leanNameStr := "fvar"
      argDecls := #[{ name := "idx", cat := .atom .none q`Init.Num, unwrap := true}]
    }
    if exprHasEta then
      #[fvar,
        { leanNameStr := "bvar"
          argDecls := #[{ name := "idx", cat := .atom .none q`Init.Num, unwrap := true }]
        },
        {
          leanNameStr := "lambda"
          argDecls := #[
            { name := "var", cat := .atom .none q`Init.Str },
            { name := "type", cat := .atom .none q`Init.Type },
            { name := "fn", cat := .atom .none cat }
          ]
        }
      ]
    else
      #[fvar]
  | q`Init.TypeP =>
    #[
        { leanNameStr := "expr",
          includeAnn := false,
          argDecls := #[{ name := "tp", cat := .atom .none q`Init.Type }]
        },
        { leanNameStr := "type", argDecls := #[] }
      ]
  | _ =>
    #[]

partial def genFreshName (s : Std.HashSet String) (base : String) (i : Nat) :=
  let name := s!"{base}_{i}"
  if name ∈ s then
    genFreshName s base (i+1)
  else
    name

def toDefaultOp (s : Std.HashSet String) (op : CatOp) : DefaultCtor :=
  let name := op.name
  let leanName :=
    if name.name ∈ s then
      let leanName := s!"{name.dialect}_{name.name}"
      if leanName ∈ s then
        genFreshName s name.name 0
      else
        leanName
    else
      name.name
  {
    leanNameStr := leanName,
    strataName := some op.name,
    argDecls := op.argDecls
  }

def CatOpMap.onlyUsedCategories (m : CatOpMap) (d : Dialect) (exprHasEta : Bool) : Array (QualifiedIdent × Array DefaultCtor) :=
  let usedSet := mkUsedCategories m d
  m.fold (init := #[]) fun a cat ops =>
    if cat ∉ declaredCategories ∧ cat ∈ usedSet then
      let usedNames : Std.HashSet String := {}
      let standardCtors := mkStandardCtors exprHasEta cat
      let usedNames : Std.HashSet String :=
        standardCtors.foldl (init := usedNames) fun m c =>
          assert! c.leanNameStr ∉ m
          m.insert c.leanNameStr
      let (allCtors, _) := ops.foldl (init := (standardCtors, usedNames)) fun (a, s) op =>
            let dOp := toDefaultOp s op
            (a.push dOp, s.insert dOp.leanNameStr)
      a.push (cat, allCtors)
    else
      a

/- Returns an identifier from a string. -/
def localIdent (name : String) : Ident :=
  let dName := .anonymous |>.str name
  .mk (.ident .none name.toSubstring dName [])

def orderedSyncatGroups (categories : Array (QualifiedIdent × Array DefaultCtor)) : Array (Array (QualifiedIdent × Array DefaultCtor)) :=
  let n := categories.size
  let g : OutGraph n := OutGraph.empty n
  let identIndexMap : Std.HashMap QualifiedIdent (Fin n) :=
        n.fold (init := {}) fun i p m =>
          m.insert categories[i].fst ⟨i, p⟩
  let getIndex (nm : QualifiedIdent) : Option (Fin n) :=
        identIndexMap[nm]?
  let addArgIndices (cat : QualifiedIdent) (opName : String) (c : SyntaxCat) (init : OutGraph n) (resIdx : Fin n) : OutGraph n :=
        c.foldOverAtomicCategories (init := init) fun g q =>
          if q ∈ declaredCategories then
            g
          else
            match getIndex q with
            | some i => g.addEdge i resIdx
            | none => panic! s!"{opName} in {cat} has unknown category {q.fullName}"
  let g : OutGraph n :=
        categories.foldl (init := g) fun g (cat, ops) => Id.run do
          let some resIdx := getIndex cat
            | panic! s!"Unknown category {cat}"
          ops.foldl (init := g) fun g op =>
            op.argDecls.foldl (init := g) fun g arg =>
              addArgIndices cat op.leanNameStr arg.cat g resIdx
  let indices := OutGraph.tarjan g
  indices.map (·.map (categories[·]))

def mkCategoryIdent (scope : Name) (name : Name) : Ident :=
  let mkDeclName (comp : List Name) : Ident :=
    let subName := comp.foldl (init := .anonymous) fun r nm => r ++ nm
    let sName := toString subName
    .mk (.ident .none sName.toSubstring subName [.decl name []])

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
  .mk (.ident .none nameStr.toSubstring subName [.decl name []])

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def mkScopedIdent {m} [Monad m] [Lean.MonadResolveName m] (subName : Lean.Name) : m Ident :=
  (scopedIdent · subName) <$> getCurrNamespace

/-- Return identifier for operator with given name to Lean name. -/
def getCategoryScopedName (cat : QualifiedIdent) : GenM Name := do
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return catName
  | none =>
    return panic! s!"getCategoryScopedName given {cat}"

/-- Return identifier for type that implements given category. -/
def getCategoryIdent (cat : QualifiedIdent) : GenM Ident := do
  if let some nm := declaredCategories[cat]? then
    return mkRootIdent nm
  currScopedIdent (← getCategoryScopedName cat)

/--
`getCategoryTerm cat annType` returns
-/
def getCategoryTerm (cat : QualifiedIdent) (annType : Ident) : GenM Term := do
  let catIdent ← mkScopedIdent (← getCategoryScopedName cat)
  return mkApp catIdent #[annType]

/-- Return identifier for operator with given name to suport category. -/
def getCategoryOpIdent (cat : QualifiedIdent) (name : Name) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ name

/--
Maps builtin polymorphic categories to their Lean representation
-/
def polymorphicBuiltinCategories : Std.HashMap QualifiedIdent Name :=
  .ofList [
    (q`Init.CommaSepBy, `Array),
    (q`Init.Option, ``Option),
    (q`Init.Seq, `Array),
  ]


def polyCatMap : Std.HashMap QualifiedIdent Lean.Expr := .ofList [
  (q`Init.CommaSepBy, .const ``Array [0]),
  (q`Init.Option, .const ``Option [0]),
  (q`Init.Seq, .const ``Array [0]),
]

private def annTypeExpr (base ann : Lean.Expr) := mkApp2 (mkConst ``Ann) base ann

/--
`getCategoryTerm cat annType` returns
-/
def getCategoryExpr (cat : QualifiedIdent) (annType : Lean.Expr) : GenM Lean.Expr := do
  let relName ← getCategoryScopedName cat
  let catName := (← getCurrNamespace) ++ relName
  let catType : Lean.Expr := mkConst catName
  return .app catType annType

def mkCatExpr (annType : Lean.Expr) (c : SyntaxCat) (unwrap : Bool) : GenM Lean.Expr := do
  let args ← c.args.attach.mapM (fun ⟨sc, _⟩ => mkCatExpr annType sc false)
  if let some nm := polymorphicBuiltinCategories[c.name]? then
    assert! args.size == 1
    return annTypeExpr (mkAppN (.const nm [0]) args) annType
  assert! args.size == 0
  match declaredCategories[c.name]? with
  | some nm =>
    -- Check if unwrap is specified
    if unwrap then
      return mkConst nm  -- Return unwrapped type
    else
      return annTypeExpr (mkConst nm) annType
  | none => do
    getCategoryExpr c.name annType
termination_by c
decreasing_by
  cases c
  decreasing_tactic

/--
Convert a category to a Lean term.
-/
partial def ppCat (annType : Ident) (c : SyntaxCat) (wrap : Bool) : GenM Term := do
  let args ← c.args.mapM (ppCat annType (wrap := true))
  let cat := c.name
  if let some tp := polymorphicBuiltinCategories[cat]? then
    let isTrue _ := inferInstanceAs (Decidable (args.size = 1))
      | throwError s!"internal: {cat} expects a single argument."
    return mkCApp ``Ann #[mkCApp tp #[args[0]], annType]
  if args.size ≠ 0 then
    throwError "internal: Expected no arguments to {cat}."
  if let some nm := declaredCategories[cat]? then
    -- Check if unwrap is specified
    let t := mkRootIdent nm
    return if wrap then mkCApp ``Ann #[t, annType] else t
  getCategoryTerm cat annType

def elabCommands (commands : Array Command) : CommandElabM Unit := do
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
  let hasNewMessage : Option Lean.Message := (← get).messages.unreported.foldl (init := none) (start := messageCount) unexpectedMessage
  match hasNewMessage with
  | none => pure ()
  | some m =>
    logError m!"Command elaboration reported messages:\n {commands}\n  {m.kind}"

abbrev BracketedBinder := TSyntax ``Lean.Parser.Term.bracketedBinder

def explicitBinder (name : String) (typeStx : Term) : CommandElabM BracketedBinder := do
  let nameStx := localIdent name
  `(bracketedBinderF| ($nameStx : $typeStx))

def genCtor (annType : Ident) (op : DefaultCtor) : GenM (TSyntax ``ctor) := do
  let ctorId : Ident := localIdent op.leanNameStr
  let ann ←
    if op.includeAnn then do
      pure #[← `(bracketedBinder| (ann : $annType))]
    else
      pure #[]
  let binders ← op.argDecls.mapM fun arg => do
        explicitBinder arg.name (← ppCat annType arg.cat (wrap := !arg.unwrap))
  `(ctor| | $ctorId:ident $ann:bracketedBinder* $binders:bracketedBinder*)

def mkInductive (cat : QualifiedIdent) (ctors : Array DefaultCtor) : GenM Command := do
  assert! cat ∉ declaredCategories
  let ident ← mkScopedIdent (← getCategoryScopedName cat)
  trace[Strata.generator] "Generating {ident}"
  let annType := localIdent "α"
  `(inductive $ident ($annType : Type) : Type where
    $(← ctors.mapM (genCtor annType)):ctor*
    deriving Repr)

def categoryToAstTypeIdent (cat : QualifiedIdent) (annType : Term) : Term :=
  let ident :=
    match cat with
    | q`Init.Expr => ``Strata.ExprF
    | q`Init.Type => ``Strata.TypeExprF
    | q`Init.TypeP => ``Strata.ArgF
    | _ => ``Strata.OperationF
  mkApp (mkRootIdent ident) #[annType]

structure ToOp where
  name : String
  argDecls : Array (String × SyntaxCat)

def toAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `toAst

def ofAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst

def mkAnnWithTerm (argCtor : Name) (annTerm v : Term) : Term :=
  mkApp (mkCIdent argCtor) #[mkCApp ``Ann.ann #[annTerm], v]

def annToAst' (argCtor : Name) (term : Term) (unwrap : Bool) : Term :=
  if unwrap then
    mkApp (mkCIdent argCtor) #[mkCApp ``default #[], term]
  else
    mkAnnWithTerm argCtor term (mkCApp ``Ann.val #[term])

partial def annArg (c : SyntaxCat) (unwrap : Bool) : GenM Ident := do
  let cat := c.name
  if cat ∈ polyCatMap then
    assert! c.args.size == 1
    return mkIdentFrom (←read).src ``Ann.ann
  assert! c.args.size == 0
  if cat ∈ declaredCategories then
    assert! not unwrap
    return mkIdentFrom (←read).src ``Ann.ann
  getCategoryOpIdent cat `ann

mutual

partial def toAstApplyArg (vn : Name) (cat : SyntaxCat) (unwrap : Bool := false) : GenM Term := do
  let v := mkIdentFrom (←read).src vn
  match cat.name with
  | q`Init.Num =>
    return annToAst' ``ArgF.num v unwrap
  | q`Init.Bool => do
    return mkCApp ``ArgF.op #[annToAst' ``OperationF.ofBool v unwrap]
  | q`Init.Ident =>
    return annToAst' ``ArgF.ident v unwrap
  | q`Init.Str =>
    return annToAst' ``ArgF.strlit v unwrap
  | q`Init.Decimal =>
    return annToAst' ``ArgF.decimal v unwrap
  | q`Init.ByteArray =>
    return annToAst' ``ArgF.bytes v unwrap
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
    assert! cat.args.size = 1
    let c := cat.args[0]!
    let e ← genFreshLeanName "e"
    let canE ← genIdentFrom e (canonical := true)
    let t ← toAstApplyArg e c
    let args := mkCApp ``Array.map #[
          ←`(fun ⟨$canE, _⟩ => $t),
          mkCApp ``Array.attach #[mkCApp ``Ann.val #[v]]
    ]
    return mkAnnWithTerm ``ArgF.commaSepList v args
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
  | q`Init.Seq => do
    assert! cat.args.size = 1
    let c := cat.args[0]!
    let e ← genFreshLeanName "e"
    let canE ← genIdentFrom e (canonical := true)
    let t ← toAstApplyArg e c
    let args := mkCApp ``Array.map #[
          ←`(fun ⟨$canE, _⟩ => $t),
          mkCApp ``Array.attach #[mkCApp ``Ann.val #[v]]
    ]
    return mkAnnWithTerm ``ArgF.seq v args
  | qid => do
    assert! cat.args.size = 0
    let toAst ← toAstIdentM qid
    ``(ArgF.op ($toAst $v))

end

abbrev MatchAlt := TSyntax ``Lean.Parser.Term.matchAlt

def toAstExprMatch (op : DefaultCtor) (annT : Term) (args : Array GenArgDecl) (names : Vector Name args.size) : GenM Term := do
  let lname := op.leanNameStr
  if lname == "fvar" then
    let .isTrue arg_size_eq := inferInstanceAs (Decidable (args.size = 1))
      | return panic! s!"fvar expected 1 argument"
    let src := (←read).src
    return mkCApp ``ExprF.fvar #[annT, mkIdentFrom src names[0]]
  let some nm := op.strataName
    | return panic! s!"Unexpected builtin expression {lname}"
  let init := mkCApp ``ExprF.fn #[annT, quote nm]
  Fin.foldlM args.size (init := init) fun a i => do
    let nm := names[i]
    let d := args[i]
    let e ← toAstApplyArg nm d.cat d.unwrap
    return Lean.Syntax.mkCApp ``ExprF.app #[annT, a, e]

def toAstMatch (cat : QualifiedIdent) (op : DefaultCtor) : GenM MatchAlt := do
  let src := (←read).src
  let argDecls := op.argDecls
  let ctor : Ident ← getCategoryOpIdent cat op.leanName
  let argc := argDecls.size
  let argNames : Vector Name argc ← Vector.ofFnM fun (i : Fin argc) =>
    genFreshLeanName argDecls[i].name
  let ((patArgs, annT) : Array Term × Term) ←
    if h : op.includeAnn then
      let (annC, annI) ← genFreshIdentPair "ann"
      pure (#[(annC : Term)], (annI : Term))
    else
      let argc1 : op.argDecls.size = 1 := by
        have inv := op.includeAnnInvariant
        grind
      let d : GenArgDecl := op.argDecls[0]
      let annF : Ident ← annArg d.cat d.unwrap
      pure (#[], mkApp annF #[mkIdentFrom src argNames[0]])
  let pat :=
    let argTerms : Array Ident := argNames.map (mkCanIdent src) |>.toArray
    mkApp ctor (patArgs ++ argTerms)
  let rhs : Term ←
        match cat with
        | q`Init.Expr =>
          toAstExprMatch op annT argDecls argNames
        | q`Init.Type => do
          let some nm := op.strataName
            | return panic! "Expected type name"
          let toAst ← toAstIdentM cat
          let argTerms ← arrayLit <| Array.ofFn fun (i : Fin argc) =>
            assert! argDecls[i].cat.isType
            mkApp toAst #[mkIdentFrom src argNames[i]]
          pure <| mkApp (mkCIdent ``TypeExprF.ident) #[annT, quote nm, argTerms]
        | q`Init.TypeP => do
          match op.leanNameStr with
          | "expr" =>
            let toAst ← toAstIdentM q`Init.Type
            let .isTrue p := inferInstanceAs (Decidable (argc = 1))
              | return panic! "Expected one argument."
            assert! argDecls[0].cat.isType
            let a := mkApp toAst #[mkIdentFrom src argNames[0]]
            pure <| mkCApp ``ArgF.type #[a]
          | "type" =>
            let c := mkCApp ``SyntaxCatF.atom #[annT, quote q`Init.Type]
            pure <| mkCApp ``ArgF.cat #[c]
          | _ =>
            return panic! "Unknown typeP op"
        | _ =>
          let mName ←
            match op.strataName with
            | some n => pure n
            | none => throwError s!"Internal: Operation {op.leanName} in {cat} requires strata name"
          let argTerms : Array Term ← Array.ofFnM fun (i : Fin argc) =>
            let nm := argNames[i]
            let d := argDecls[i]
            toAstApplyArg nm d.cat d.unwrap
          pure <| mkCApp ``OperationF.mk #[annT, quote mName, ← arrayLit argTerms]
  `(matchAltExpr| | $pat => $rhs)

def genToAst (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM Command := do
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  let astType : Term := categoryToAstTypeIdent cat annType
  let cases : Array MatchAlt ← ops.mapM_off (toAstMatch cat)
  let toAst ← toAstIdentM cat
  trace[Strata.generator] "Generating {toAst}"
  let src := (←read).src
  let v ← genFreshLeanName "v"
  `(partial def $toAst {$annType : Type} [Inhabited $annType] ($(mkCanIdent src v) : $catTerm) : $astType :=
      match $(mkIdentFrom src v):ident with $cases:matchAlt*)

private def addAnn (act : Name) (e : Term) (unwrap : Bool) : Term :=
    let t := mkApp (mkCIdent act) #[e]
    if unwrap then
      t
    else
      mkCApp ``Functor.map #[mkCApp ``Ann.mk #[mkCApp ``ArgF.ann #[e]], t]

partial def getOfIdentArg (varName : String) (cat : SyntaxCat) (e : Term) (unwrap : Bool := false) : GenM Term := do
  match cat.name with
  | q`Init.Num =>
    return addAnn ``OfAstM.ofNumM e unwrap
  | q`Init.Ident =>
    return addAnn ``OfAstM.ofIdentM e unwrap
  | q`Init.Str =>
    return addAnn ``OfAstM.ofStrlitM e unwrap
  | q`Init.Decimal =>
    return addAnn ``OfAstM.ofDecimalM e unwrap
  | q`Init.ByteArray =>
    return addAnn ``OfAstM.ofBytesM e unwrap
  | q`Init.Bool => do
    return addAnn ``Strata.Bool.ofAst e unwrap
  | cid@q`Init.Expr => do
    let ofAst ← ofAstIdentM cid
    let (vc, vi) ← genFreshIdentPair <| varName ++ "_inner"
    return mkCApp ``OfAstM.ofExpressionM #[e, ←``(fun $vc _ => $ofAst $vi)]
  | cid@q`Init.Type => do
    let ofAst ← ofAstIdentM cid
    let (vc, vi) ← genFreshIdentPair varName
    return mkCApp ``OfAstM.ofTypeM #[e, ←``(fun $vc _ => $ofAst $vi)]
  | q`Init.CommaSepBy => do
    let c := cat.args[0]!
    let (vc, vi) ← genFreshIdentPair varName
    let body ← getOfIdentArg varName c vi
    ``(OfAstM.ofCommaSepByM $e fun $vc _ => $body)
  | q`Init.Option => do
    let c := cat.args[0]!
    let (vc, vi) ← genFreshIdentPair varName
    let body ← getOfIdentArg varName c vi
    ``(OfAstM.ofOptionM $e fun $vc _ => $body)
  | q`Init.Seq => do
    let c := cat.args[0]!
    let (vc, vi) ← genFreshIdentPair varName
    let body ← getOfIdentArg "e" c vi
    ``(OfAstM.ofSeqM $e fun $vc _ => $body)
  | cid@q`Init.TypeP => do
    let ofAst ← ofAstIdentM cid
    pure <| mkApp ofAst #[e]
  | cid => do
    assert! cat.args.isEmpty
    let (vc, vi) ← genFreshIdentPair varName
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofOperationM $e fun $vc _ => $ofAst $vi)

def ofAstArgs (argDecls : Array GenArgDecl) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let arg := argDecls[i]
    let (vc, vi) ← genFreshIdentPair <| arg.name ++ "_bind"
    let av ← ``($argsVar[$(quote i)])
    let rhs ← getOfIdentArg arg.name arg.cat av (unwrap := arg.unwrap)
    let stmt ← `(doSeqItem| let $vc ← $rhs:term)
    return (vi, stmt)
  return args.unzip

def ofAstMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat) (op : DefaultCtor) (rhs : Term) : GenM MatchAlt := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanNameStr}"
  let some nameIndex := nameIndexMap[name]?
    | return panic! s!"Unbound operator name {name}"
  `(matchAltExpr| | Option.some $(quote nameIndex) => $rhs)

def ofAstExprMatchRhs (cat : QualifiedIdent) (annI argsVar : Ident) (op : DefaultCtor) : GenM Term := do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let some nm := op.strataName
    | return panic! s!"Missing name for {op.leanName}"
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  let checkExpr ← ``(OfAstM.checkArgCount $(quote nm) $(quote argCount) $(argsVar))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    pure ($ctorIdent $annI $parsedArgs:term*))

def ofAstExprMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat)
      (cat : QualifiedIdent) (annI : Ident) (argsVar : Ident) (op : DefaultCtor) : GenM MatchAlt := do
  let rhs ← ofAstExprMatchRhs cat annI argsVar op
  ofAstMatch nameIndexMap op rhs

def ofAstTypeArgs (argDecls : Array GenArgDecl) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
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

def ofAstTypeMatchRhs (cat : QualifiedIdent) (ann argsVar : Ident) (op : DefaultCtor) : GenM Term := do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let (parsedArgs, stmts) ← ofAstTypeArgs argDecls argsVar
  let checkExpr ← ``(OfAstM.checkTypeArgCount $(quote argDecls.size) $(argsVar))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    pure <| $ctorIdent $ann $parsedArgs:term*)

def ofAstOpMatchRhs (cat : QualifiedIdent) (annI argsVar : Ident) (op : DefaultCtor) : GenM Term := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanNameStr}"
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let checkExpr ← ``(OfAstM.checkArgCount $(quote name) $(quote argCount) $argsVar)
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    return $ctorIdent $annI $parsedArgs:term*)

/--
Creates a mapping from operation names (QualifiedIdent) to unique natural numbers.
This is used to pattern match in the generated code.
-/
def createNameIndexMap (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM (Std.HashMap QualifiedIdent Nat × Ident × Command) := do
  let nameIndexMap := ops.foldl (init := {}) fun map op =>
    match op.strataName with
    | none => map  -- Skip operators without a name
    | some name => map.insert name map.size  -- Assign the next available index
  let ofAstNameMap ← currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst.nameIndexMap
  let cmd ← `(def $ofAstNameMap : Std.HashMap Strata.QualifiedIdent Nat := Std.HashMap.ofList $(quote nameIndexMap.toList))
  pure (nameIndexMap, ofAstNameMap, cmd)

def mkOfAstDef (cat : QualifiedIdent) (ofAst : Ident) (v : Name) (rhs : Term) : GenM Command := do
  let src := (←read).src
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  `(partial def $ofAst {$annType : Type} [Inhabited $annType] [Repr $annType] ($(mkCanIdent src v) : $(categoryToAstTypeIdent cat annType)) : OfAstM $catTerm := $rhs)

def matchTypeParamOrType {Ann α} [Repr Ann] (a : ArgF Ann) (onTypeParam : Ann → α) (onType : TypeExprF Ann → OfAstM α) : OfAstM α :=
  match a with
  | .cat (.atom ann q`Init.Type) => pure (onTypeParam ann)
  | .type tp => onType tp
  | _ => .throwExpected "Type parameter or type expression" a

def genOfAst (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM (Array Command × Command) := do
  let src := (←read).src
  let ofAst ← ofAstIdentM cat
  trace[Strata.generator] "Generating {ofAst}"
  match cat with
  | q`Init.Expr =>
    let v ← genFreshLeanName "v"
    let argsVar ← genFreshLeanName "args"
    let (annC, annI) ← genFreshIdentPair "ann"
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let fvarCtorIdent ← getCategoryOpIdent cat `fvar
    let cases : Array MatchAlt ← ops.filterMapM fun op =>
      if op.leanNameStr == "fvar" then
        pure none
      else
        some <$> ofAstExprMatch nameIndexMap cat annI (mkIdentFrom src argsVar) op
    let rhs ←
      `(let vnf := ($(mkIdentFrom src v)).hnf
        let $(mkCanIdent src argsVar) := vnf.args.val
        match (vnf.fn) with
        | Strata.ExprF.fvar ann i => pure ($fvarCtorIdent ann i)
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
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let cases : Array MatchAlt ← ops.mapM fun op =>
      ofAstMatch nameIndexMap op =<< ofAstTypeMatchRhs cat annI argsI op
    let rhs ←
      `(match ($(mkIdentFrom src v)) with
        | Strata.TypeExprF.ident $annC typeIdent $argsC =>
          (match ($ofAstNameMap[typeIdent]?) with
          $cases:matchAlt*
          | _ => OfAstM.throwUnknownIdentifier $(quote cat) typeIdent)
        | _ => OfAstM.throwExpected "Expected type" (ArgF.type $(mkIdentFrom src v)))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs)
  | q`Init.TypeP =>
    let v ← genFreshLeanName "v"
    let catCtorIdent ← getCategoryOpIdent cat `type
    let exprCtorIdent ← getCategoryOpIdent cat `expr
    let typeOfAst ← ofAstIdentM q`Init.Type
    let rhs ← ``(
      matchTypeParamOrType $(mkIdentFrom src v) $catCtorIdent (fun tp => $exprCtorIdent <$> $typeOfAst tp)
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

def checkInhabited (cat : QualifiedIdent) (ops : Array DefaultCtor) : StateT InhabitedSet GenM Unit := do
  if cat ∈ (←get) then
    return ()
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  for op in ops do
    let inhabited ← get
    let isInhabited := op.argDecls.all fun arg =>
        match arg.cat.name with
        | q`Init.Seq => true
        | q`Init.CommaSepBy => true
        | q`Init.Option => true
        | c => c ∈ inhabited
    if !isInhabited then
      continue
    let ctor : Term ← getCategoryOpIdent cat op.leanName
    let d := Lean.mkCIdent ``default
    let argc := if op.includeAnn then 1 else 0
    let argc := argc + op.argDecls.size
    let e := mkApp ctor (Array.replicate argc d)
    StateT.lift <| runCmd <|
      elabCommand =<< `(instance [Inhabited $annType] : Inhabited $catTerm where default := $e)
    modify (·.insert cat)
    break

partial def addInhabited (group : Array (QualifiedIdent × Array DefaultCtor)) (s : InhabitedSet) : GenM InhabitedSet := do
  let initSize := s.size
  let sm ← group.foldlM (init := s) fun s (cat, ctors) => do
    let (_, s) ← checkInhabited cat ctors s
    pure s
  let finalSize := sm.size
  if finalSize > initSize then
    addInhabited group sm
  else
    pure sm

partial def annExpr (c : SyntaxCat) (unwrap : Bool) : GenM Name := do
  let cat := c.name
  if cat ∈ polyCatMap then
    assert! c.args.size == 1
    return ``Ann.ann
  if cat ∈ declaredCategories then
    assert! c.args.size == 0
    assert! not unwrap
    return ``Ann.ann

  assert! c.args.size == 0
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return (← getCurrNamespace) ++ catName ++ `ann
  | none =>
    return panic! s!"annExpr given {cat}"


def annRecursor (c : DefaultCtor) : GenM Lean.Expr := do
  let argc := c.argDecls.size
  let (inner_off, ann) ←
    if h : c.includeAnn then
      pure (2, Lean.Expr.bvar argc)
    else
      have ne : c.argDecls.size > 0 := by
        have p := c.includeAnnInvariant
        grind
      let d := c.argDecls[0]
      let annFn ← annExpr d.cat d.unwrap
      pure (1, Lean.mkApp2 (.const annFn []) (.bvar (argc+1)) (.bvar (argc - 1)))
  let inner : Lean.Expr ← Fin.foldrM argc (init := ann) fun i e => do
    let a := c.argDecls[i]
    let argType ← mkCatExpr (.bvar (inner_off + i)) a.cat a.unwrap
    return .lam (.mkSimple a.name) argType (binderInfo := .default) e
  if c.includeAnn then
    return .lam `ann (.bvar 1) (binderInfo := .default) inner
  else
    return inner

def genAnnFunctions (cat : QualifiedIdent) (ctors : Array DefaultCtor) : GenM Unit := do
  let relName ← getCategoryScopedName cat

  let catName := (← getCurrNamespace) ++ relName
  let catType : Lean.Expr := mkConst catName
  let defName := catName ++ `ann
  let type : Lean.Expr :=
        .forallE `α (.sort 1) (binderInfo := .implicit) <|
          .forallE `_ (.app catType (.bvar 0)) (binderInfo := .default) <|
            .bvar 1
  let motive : Lean.Expr := .lam `_ (.app catType (.bvar 1)) (binderInfo := .default) (.bvar 2)
  let term : Lean.Expr := mkApp3 (.const (catName ++ `casesOn) [1]) (.bvar 1) motive (.bvar 0)
  let term : Lean.Expr ← ctors.foldlM (init := term) fun f c =>
          return .app f (← annRecursor c)
  --let term := mkApp2 (mkConst ``sorryAx [1]) (.bvar 1) (mkConst ``true)
  let value : Lean.Expr :=
    .lam `α (.sort 1) (binderInfo := .implicit) <|
      .lam `a (.app catType (.bvar 0)) (binderInfo := .default) <|
        term
  liftCoreM <| addAndCompile <| .defnDecl {
    name := defName
    levelParams := []
    type := type
    value := value
    hints := .opaque
    safety := .safe
    all := [defName]
  }

def gen (categories : Array (QualifiedIdent × Array DefaultCtor)) : GenM Unit := do
  let mut inhabitedCats : InhabitedSet :=
    Std.HashSet.ofArray
      declaredCategories.keysArray
  for allCtors in orderedSyncatGroups categories do
    let s ←
      withTraceNode `Strata.generator (fun _ =>
        return m!"Declarations group: {allCtors.map (·.fst)}") do
        -- Check if the toAst/ofAst definitions will be recursive by looking for
        -- categories that are not already in inhabited set.
        -- N.B. This is not used as we use partial functions, but
        -- kept as we want to eventually switch back
        -- let newCats := Std.HashSet.ofArray <| allCtors.map (·.fst)
        --let _isRecursive := allCtors.any fun (_, ops) =>
        --      ops.any fun op =>
        --        op.argDecls.any fun (_, c) =>
        --          c.foldOverAtomicCategories (init := false)
        --            fun b qid => b || qid ∈ newCats
        let cats := allCtors.map (·.fst)
        profileitM Lean.Exception s!"Generating inductives {cats}" (← getOptions) do
          let inductives ← allCtors.mapM fun (cat, ctors) => do
            assert! q`Init.Num ≠ cat
            assert! q`Init.Str ≠ cat
            mkInductive cat ctors
          runCmd <| elabCommands inductives
        let inhabitedCats2 ←
          profileitM Lean.Exception s!"Generating inhabited {cats}" (← getOptions) do
            addInhabited allCtors inhabitedCats
        let inhabitedCats := inhabitedCats2
        profileitM Lean.Exception s!"Generating ann functions {cats}" (← getOptions) do
          allCtors.forM fun (cat, ctors) => do
            genAnnFunctions cat ctors
        profileitM Lean.Exception s!"Generating toAstDefs {cats}" (← getOptions) do
          let toAstDefs ← allCtors.mapM fun (cat, ctors) => do
            genToAst cat ctors
          runCmd <| elabCommands toAstDefs
        profileitM Lean.Exception s!"Generating ofAstDefs {cats}" (← getOptions) do
          let ofAstDefs ← allCtors.mapM fun (cat, ctors) => do
            let (cmds, d) ← genOfAst cat ctors
            (cmds.forM elabCommand : CommandElabM Unit)
            pure d
          runCmd <| elabCommands ofAstDefs
        pure inhabitedCats
    inhabitedCats := s

def runGenM {α} (src : Lean.Syntax) (pref : String) (catNames : Array QualifiedIdent) (exprHasEta : Bool) (m : GenM α) : CommandElabM α := do
  let catNameCounts : Std.HashMap String Nat :=
    catNames.foldl (init := {}) fun m k =>
      m.alter k.name (fun v => some (v.getD 0 + 1))
  let categoryNameMap := catNames.foldl (init := {}) fun m i =>
    let name :=
          if catNameCounts.getD i.name 0 > 1 then
            .mkSimple s!"{i.dialect}_{i.name}"
          else if i.name ∈ reservedCats then
            .mkSimple s!"{pref}{i.name}"
          else
            .mkSimple i.name
    m.insert i name
  let ctx : GenContext := {
    src := src
    categoryNameMap := categoryNameMap
    exprHasEta := exprHasEta
  }
  m ctx

/--
`#strata_gen ident` generates an AST for the dialect `ident`.

This includes functions for converting from the standard AST to the generated AST
and back.
-/
syntax (name := strataGenCmd) "#strata_gen" ident : command -- declare the syntax

@[command_elab strataGenCmd]
def genAstImpl : CommandElab := fun stx =>
  match stx with
  | `(#strata_gen $dialectStx) => do
    let .str .anonymous dialectName := dialectStx.getId
      | throwErrorAt dialectStx s!"Expected dialect name"
    let loader := dialectExt.getState (← getEnv) |>.loaded
    let depDialectNames := generateDependentDialects (loader.dialects.map[·]?) dialectName
    let usedDialects ← depDialectNames.mapM fun nm =>
          match loader.dialects[nm]? with
          | some d => pure d
          | none => panic! s!"Missing dialect {nm}"
    let some d := loader.dialects[dialectName]?
      | throwErrorAt dialectStx "Missing dialect"
    let (cm, errs) := mkCatOpMap usedDialects
    if errs.size > 0 then
      for e in errs do
        logError e
      return
    let exprHasEta := false -- FIXME
    let cats := cm.onlyUsedCategories d exprHasEta
    let catNames := cats.map (·.fst)
    runGenM stx dialectName catNames exprHasEta (gen cats)
  | _ =>
    throwUnsupportedSyntax

end Strata
