/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Elab.Command
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.GenTrace
import Strata.DDM.Integration.Lean.OfAstM
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Util.Graph.Tarjan

open Lean (Command Name Ident Term TSyntax getEnv logError profileitM quote withTraceNode mkIdentFrom)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand)
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
def mkScopedIdent (scope : Name) (subName : Lean.Name) : Ident :=
  let fullName := scope ++ subName
  let nameStr := toString subName
  .mk (.ident .none nameStr.toSubstring subName [.decl fullName []])

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
def currScopedIdent {m} [Monad m] [Lean.MonadResolveName m] (subName : Lean.Name) : m Ident := do
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
  categoryNameMap : Std.HashMap QualifiedIdent String
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
  return (mkIdentFrom src name true, mkIdentFrom src name)

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
  argDecls : Array (String × SyntaxCat)

def DefaultCtor.leanName (c : DefaultCtor) : Name := .str .anonymous c.leanNameStr

/--
An operation at the category level.
-/
structure CatOp where
  name : QualifiedIdent
  argDecls : Array (String × SyntaxCat)

namespace CatOp

partial def checkCat (op : QualifiedIdent) (c : SyntaxCat) : Except String Unit := do
  c.args.forM (checkCat op)
  let f := c.name
  if f ∈ forbiddenCategories then
    throw s!"{op.fullName} refers to unsupported category {f.fullName}."

def ofArgDecl (op : QualifiedIdent) (d : ArgDecl) : Except String (String × SyntaxCat) := do
  let cat ←
    match d.kind with
    | .type tp =>
      pure <| .atom tp.ann q`Init.Expr
    | .cat c =>
      checkCat op c
      pure c
  pure ⟨d.ident, cat⟩

def ofOpDecl (d : DialectName) (o : OpDecl) : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls.toArray |>.mapM (ofArgDecl name)
  return { name, argDecls }

def ofTypeDecl (d : DialectName) (o : TypeDecl) : CatOp := {
  name := ⟨d, o.name⟩
  argDecls := o.argNames |>.map fun anm => ⟨anm.val, .atom .none q`Init.Type⟩
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
This maps category names in the Init that are already declared to their
representation.
-/
def declaredCategories : Std.HashMap CategoryName Name := .ofList [
  (q`Init.Ident, ``String),
  (q`Init.Num, ``Nat),
  (q`Init.Decimal, ``Decimal),
  (q`Init.Str, ``String),
  (q`Init.ByteArray, ``ByteArray)
]

def ignoredCategories : Std.HashSet CategoryName :=
  .ofList declaredCategories.keys ∪ forbiddenCategories

namespace CatOpMap

def addCat (m : CatOpMap) (cat : CategoryName) : CatOpMap :=
  if cat ∈ ignoredCategories then
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
    if decl.category ∈ ignoredCategories ∨ decl.category ∈ specialCategories then
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
    match c with
    | q`Init.TypeP =>
      mkUsedCategories.aux m (s.add q`Init.Type)
    | _ =>
      let ops := m.getD c #[]
      let addArgs {α:Type} (f : α → CategoryName → α) (a : α) (op : CatOp) :=
        op.argDecls.foldl (init := a) fun r (_, c) => c.foldOverAtomicCategories (init := r) f
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
    if exprHasEta then
      #[
        .mk "bvar" none #[("idx", .atom .none q`Init.Num)],
        .mk "lambda" none #[
          ("var", .atom .none q`Init.Str),
          ("type", .atom .none q`Init.Type),
          ("fn", .atom .none cat)
        ]
      ]
    else
      #[]
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
      let usedNames : Std.HashSet String :=
            match cat with
            | q`Init.Expr => { "fvar" }
            | _ => {}
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
          match cat with
          | q`Init.TypeP =>
            let some typeIdx := getIndex q`Init.Type
              | panic! s!"Unknown category Init.Type."
            g.addEdge typeIdx resIdx
          | _ =>
            ops.foldl (init := g) fun g op =>
              op.argDecls.foldl (init := g) fun g (_, c) =>
                addArgIndices cat op.leanNameStr c g resIdx
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

/-- Return identifier for operator with given name to suport category. -/
def getCategoryScopedName (cat : QualifiedIdent) : GenM Name := do
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return .mkSimple catName
  | none =>
    return panic! s!"getCategoryScopedName given {cat}"

/-- Return identifier for type that implements given category. -/
def getCategoryIdent (cat : QualifiedIdent) : GenM Ident := do
  if let some nm := declaredCategories[cat]? then
    return mkRootIdent nm
  currScopedIdent (← getCategoryScopedName cat)

def getCategoryTerm (cat : QualifiedIdent) (annType : Ident) : GenM Term := do
  let catIdent ← mkScopedIdent (← getCategoryScopedName cat)
  return Lean.Syntax.mkApp catIdent #[annType]

/-- Return identifier for operator with given name to suport category. -/
def getCategoryOpIdent (cat : QualifiedIdent) (name : Name) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ name

partial def ppCat (annType : Ident) (c : SyntaxCat) : GenM Term := do
  let args ← c.args.mapM (ppCat annType)
  match c.name, eq : args.size with
  | q`Init.CommaSepBy, 1 =>
    return mkCApp ``Ann #[mkCApp ``Array #[args[0]], annType]
  | q`Init.Option, 1 =>
    return mkCApp ``Ann #[mkCApp ``Option #[args[0]], annType]
  | q`Init.Seq, 1 =>
    return mkCApp ``Ann #[mkCApp ``Array #[args[0]], annType]
  | cat, 0 =>
    match declaredCategories[cat]? with
    | some nm =>
      pure <| mkCApp ``Ann #[mkRootIdent nm, annType]
    | none => do
      getCategoryTerm cat annType
  | f, _ => throwError "Unsupported {f.fullName}"

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
  let binders ← op.argDecls.mapM fun (name, tp) => do
        explicitBinder name (← ppCat annType tp)
  `(ctor| | $ctorId:ident (ann : $annType) $binders:bracketedBinder* )

def mkInductive (cat : QualifiedIdent) (ctors : Array DefaultCtor) : GenM Command := do
  assert! cat ∉ declaredCategories
  let ident ← mkScopedIdent (← getCategoryScopedName cat)
  trace[Strata.generator] "Generating {ident}"
  let annType := localIdent "α"
  let builtinCtors : Array (TSyntax ``ctor) ←
        match cat with
        | q`Init.Expr => do
            pure #[
              ← `(ctor| | $(localIdent "fvar"):ident (ann : $annType) (idx : Nat))
            ]
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
    $(← ctors.mapM (genCtor annType)):ctor*
    deriving Repr)

def categoryToAstTypeIdent (cat : QualifiedIdent) (annType : Term) : Term :=
  let ident :=
    match cat with
    | q`Init.Expr => ``Strata.ExprF
    | q`Init.Type => ``Strata.TypeExprF
    | q`Init.TypeP => ``Strata.ArgF
    | _ => ``Strata.OperationF
  Lean.Syntax.mkApp (mkRootIdent ident) #[annType]

structure ToOp where
  name : String
  argDecls : Array (String × SyntaxCat)

def toAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `toAst

def ofAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst

def mkAnnWithTerm (argCtor : Name) (annTerm v : Term) : Term :=
  mkCApp argCtor #[mkCApp ``Ann.ann #[annTerm], v]

def annToAst (argCtor : Name) (annTerm : Term) : Term :=
  mkCApp argCtor #[mkCApp ``Ann.ann #[annTerm], mkCApp ``Ann.val #[annTerm]]

partial def toAstApplyArg (vn : Name) (cat : SyntaxCat) : GenM Term := do
  let v := mkIdentFrom (←read).src vn
  match cat.name with
  | q`Init.Expr => do
    let toAst ← toAstIdentM cat.name
    return mkCApp ``ArgF.expr #[mkApp toAst #[v]]
  | q`Init.Ident =>
    return annToAst ``ArgF.ident v
  | q`Init.Num =>
    return annToAst ``ArgF.num v
  | q`Init.Decimal =>
    return annToAst ``ArgF.decimal v
  | q`Init.Str =>
    return annToAst ``ArgF.strlit v
  | q`Init.ByteArray =>
    return annToAst ``ArgF.bytes v
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

abbrev MatchAlt := TSyntax ``Lean.Parser.Term.matchAlt

def toAstBuiltinMatches (cat : QualifiedIdent) : GenM (Array MatchAlt) := do
  let src := (←read).src
  match cat with
  | q`Init.Expr =>
    let (annC, annI) ← genFreshIdentPair "ann"
    let ctor ← getCategoryOpIdent cat `fvar
    let pat : Term := mkApp ctor #[annC, mkCanIdent src `idx]
    let rhs := mkCApp ``ExprF.fvar #[annI, mkIdentFrom src `idx]
    return #[← `(matchAltExpr| | $pat => $rhs)]
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

def toAstMatch (cat : QualifiedIdent) (op : DefaultCtor) : GenM MatchAlt := do
  let src := (←read).src
  let argDecls := op.argDecls
  let (annC, annI) ← genFreshIdentPair "ann"
  let ctor : Ident ← getCategoryOpIdent cat op.leanName
  let args : Array (Name × SyntaxCat) ← argDecls.mapM fun (nm, c) =>
    return (← genFreshLeanName nm, c)
  let argTerms : Array Term := args.map fun p => mkCanIdent src p.fst
  let pat : Term ← ``($ctor $annC $argTerms:term*)
  let rhs : Term ←
        match cat with
        | q`Init.Expr =>
          let lname := op.leanNameStr
          let some nm := op.strataName
            | return panic! s!"Unexpected builtin expression {lname}"
          let init := mkCApp ``ExprF.fn #[annI, quote nm]
          args.foldlM (init := init) fun a (nm, tp) => do
            let e ← toAstApplyArg nm tp
            return Lean.Syntax.mkCApp ``ExprF.app #[annI, a, e]
        | q`Init.Type => do
          let some nm := op.strataName
            | return panic! "Expected type name"
          let toAst ← toAstIdentM cat
          let argTerms ← arrayLit <| args.map fun (v, c) =>
            assert! c.isType
            Lean.Syntax.mkApp toAst #[mkIdentFrom src v]
          pure <| Lean.Syntax.mkCApp ``TypeExprF.ident #[annI, quote nm, argTerms]
        | _ =>
          let mName ←
            match op.strataName with
            | some n => pure n
            | none => throwError s!"Internal: Operation requires strata name"
          let argTerms : Array Term ← args.mapM fun (nm, tp) => toAstApplyArg nm tp
          pure <| mkCApp ``OperationF.mk #[annI, quote mName, ← arrayLit argTerms]
  `(matchAltExpr| | $pat => $rhs)

def genToAst (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM Command := do
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  let astType : Term := categoryToAstTypeIdent cat annType
  let cases ← toAstBuiltinMatches cat
  let cases : Array MatchAlt ← ops.mapM_off (init := cases) (toAstMatch cat)
  let toAst ← toAstIdentM cat
  trace[Strata.generator] "Generating {toAst}"
  let src := (←read).src
  let v ← genFreshLeanName "v"
  `(partial def $toAst {$annType : Type} [Inhabited $annType] ($(mkCanIdent src v) : $catTerm) : $astType :=
      match $(mkIdentFrom src v):ident with $cases:matchAlt*)

partial def getOfIdentArg (varName : String) (cat : SyntaxCat) (e : Term) : GenM Term := do
  match cat.name with
  | cid@q`Init.Expr => do
    let (vc, vi) ← genFreshIdentPair <| varName ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofExpressionM $e fun $vc _ => $ofAst $vi)
  | q`Init.Ident => do
    ``(OfAstM.ofIdentM $e)
  | q`Init.Num => do
    ``(OfAstM.ofNumM $e)
  | q`Init.Decimal => do
    ``(OfAstM.ofDecimalM $e)
  | q`Init.Str => do
    ``(OfAstM.ofStrlitM $e)
  | q`Init.ByteArray => do
    ``(OfAstM.ofBytesM $e)
  | cid@q`Init.Type => do
    let (vc, vi) ← genFreshIdentPair varName
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofTypeM $e fun $vc _ => $ofAst $vi)
  | cid@q`Init.TypeP => do
    let ofAst ← ofAstIdentM cid
    pure <| mkApp ofAst #[e]
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
  | cid => do
    assert! cat.args.isEmpty
    let (vc, vi) ← genFreshIdentPair varName
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofOperationM $e fun $vc _ => $ofAst $vi)

def ofAstArgs (argDecls : Array (String × SyntaxCat)) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let (vnm, c) := argDecls[i]
    let (vc, vi) ← genFreshIdentPair <| vnm ++ "_bind"
    let av ← ``($argsVar[$(quote i)])
    let rhs ← getOfIdentArg vnm c av
    let stmt ← `(doSeqItem| let $vc ← $rhs:term)
    return (vi, stmt)
  return args.unzip

def ofAstMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat) (op : DefaultCtor) (rhs : Term) : GenM MatchAlt := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanNameStr}"
  let some nameIndex := nameIndexMap[name]?
    | return panic! s!"Unbound operator name {name}"
  `(matchAltExpr| | Option.some $(quote nameIndex) => $rhs)

def ofAstExprMatchRhs (cat : QualifiedIdent) (annI argsVar : Ident) (op : DefaultCtor) : GenM Term:= do
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

def ofAstTypeArgs (argDecls : Array (String × SyntaxCat)) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let ofAst ← ofAstIdentM q`Init.Type
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let (vnm, _) := argDecls[i]
    let v ← genFreshLeanName vnm
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
    let cases : Array MatchAlt ← ops.mapM (ofAstExprMatch nameIndexMap cat annI (mkIdentFrom src argsVar))
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
    let isInhabited := op.argDecls.all fun (_, c) =>
        match c.name with
        | q`Init.Seq => true
        | q`Init.CommaSepBy => true
        | q`Init.Option => true
        | c => c ∈ inhabited
    if !isInhabited then
      continue
    let ctor : Term ← getCategoryOpIdent cat op.leanName
    let d := Lean.mkCIdent ``default
    let e := Lean.Syntax.mkApp ctor (Array.replicate (op.argDecls.size + 1) d)
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

def runGenM (src : Lean.Syntax) (pref : String) (catNames : Array QualifiedIdent) (exprHasEta : Bool) (m : GenM α) : CommandElabM α := do
  let catNameCounts : Std.HashMap String Nat :=
    catNames.foldl (init := {}) fun m k =>
      m.alter k.name (fun v => some (v.getD 0 + 1))
  let categoryNameMap := catNames.foldl (init := {}) fun m i =>
    let name :=
          if catNameCounts.getD i.name 0 > 1 then
            s!"{i.dialect}_{i.name}"
          else if i.name ∈ reservedCats then
            s!"{pref}{i.name}"
          else
            i.name
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
