/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Elab.Command
import Strata.DDM.BuiltinDialects.StrataDD
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.GenTrace
import Strata.DDM.Integration.Lean.OfAstM
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Util.Graph.Tarjan

open Lean (Command Name Ident Term TSyntax getEnv logError profileitM quote withTraceNode)
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand)
open Lean.Elab.Term (mkFreshIdent)
open Lean.MonadOptions (getOptions)
open Lean.MonadResolveName (getCurrNamespace)
open Lean.Parser.Command (ctor)
open Lean.Parser.Term (bracketedBinderF doSeqItem matchAltExpr)
open Lean.Parser.Termination (terminationBy suffix)
open Lean.Syntax (mkStrLit)

namespace Strata

private def arrayLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#[ $as:term,* ] : Array _) )

private def vecLit [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#v[ $as:term,* ] : Vector _ $(quote as.size)) )

abbrev LeanCategoryName := Lean.Name

structure GenContext where
  categoryNameMap : Std.HashMap QualifiedIdent String
  exprHasEta : Bool

abbrev GenM := ReaderT GenContext CommandElabM

def runCmd {α} (act : CommandElabM α) : GenM α := fun _ => act

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
  q`StrataDD.Binding
}

private def forbiddenWellDefined : Bool :=
  forbiddenCategories.all fun nm =>
    match nm.dialect with
    | "Init" => nm.name ∈ initDialect
    | "StrataDD" => nm.name ∈ strataDialect
    | _ => false

#guard "BindingType" ∈ initDialect.cache
#guard "Binding" ∈ strataDialect.cache
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
  leanName : String
  /--
  The name in the Strata dialect for this constructor.  If `none`, then
  this must be an auto generated constructor.
  -/
  strataName : Option QualifiedIdent
  argDecls : Array (String × SyntaxCat)

/--
An operation at the category level.
-/
structure CatOp where
  name : QualifiedIdent
  argDecls : Array (String × SyntaxCat)

namespace CatOp

partial def checkCat (op : QualifiedIdent) (c : SyntaxCat) : Except String Unit := do
  c.args.forM (checkCat op)
  let f := c.head
  if f ∈ forbiddenCategories then
    throw s!"{op.fullName} refers to unsupported category {f.fullName}."

def ofDeclBinding (op : QualifiedIdent) (b : DeclBinding) : Except String (String × SyntaxCat) := do
  let cat ←
    match b.kind with
    | .expr _ =>
      pure <| .atom q`Init.Expr
    | .cat c =>
      checkCat op c
      pure c
  pure ⟨b.ident, cat⟩

def ofOpDecl (d : DialectName) (o : OpDecl) : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls |>.mapM (ofDeclBinding name)
  return { name, argDecls }

end CatOp

def CatOp.ofTypeDecl (d : DialectName) (o : TypeDecl) : CatOp := {
  name := ⟨d, o.name⟩
  argDecls := o.argNames |>.map fun nm => ⟨nm, .atom q`Init.Type⟩
}

def CatOp.ofFunctionDecl (d : DialectName) (o : FunctionDecl) : Except String CatOp := do
  let name := ⟨d, o.name⟩
  let argDecls ← o.argDecls |>.mapM (ofDeclBinding name)
  return { name, argDecls }

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
    if d = "Init" ∧ decl.name = "TypeP" then do
      let cat := q`Init.TypeP
      addCatM ⟨d, decl.name⟩
      addOpM cat { name := q`Init.type, argDecls := #[] }
      addOpM cat { name := q`Init.expr, argDecls := #[("type", .atom q`Init.Type)] }
    else
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

namespace SyntaxCat

/--
Invoke `f` over all atomic (no argument) category names in `c`.
-/
private
def foldOverAtomicCategories {α} (c : SyntaxCat) (init : α)  (f : α  → QualifiedIdent → α) : α := aux c init false
  where aux (c : SyntaxCat) (init : α) (hasArg : Bool) :=
          match c with
          | .atom i => if hasArg then init else f init i
          | .app d e => aux d (aux e init false) true

end SyntaxCat

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
private def addArgCategories (s : CategorySet) (bs : DeclBindings) : CategorySet :=
  bs.foldl (init := s) fun s b =>
    b.kind.categoryOf.foldOverAtomicCategories (init := s) (·.insert ·)

partial def mkUsedCategories.aux (m : CatOpMap) (s : WorkSet CategoryName) : CategorySet :=
  match s.pop with
  | none => s.set
  | some (s, c) =>
    let ops := m.getD c #[]
    let addArgs {α:Type} (f : α → CategoryName → α) (a : α) (op : CatOp) :=
      op.argDecls.foldl (init := a) fun r (_, c) => c.foldOverAtomicCategories (init := r) f
    let addName (pa : WorkSet CategoryName) c := pa.add c
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
    let fvarCtor : DefaultCtor := .mk "fvar" none #[("idx", .atom q`Init.Num)]
    if exprHasEta then
      #[
        fvarCtor,
        .mk "bvar" none #[("idx", .atom q`Init.Num)],
        .mk "lambda" none #[
          ("var", .atom q`Init.Str),
          ("type", .atom q`Init.Type),
          ("fn", .atom cat)
        ]
      ]
    else
      #[
        fvarCtor
      ]
      /-
  | q`Init.TypeP =>
    #[ .mk "type" none #[],
       .mk "expr" none #[("type", .atom q`Init.Type)]
    ]-/
  | _ =>
    #[]

def countSimilar {α} {β} [BEq β] [Hashable β] (as : Array α) (init : Std.HashMap β Nat := {}) (f : α → β) : Std.HashMap β Nat :=
  as.foldl (init := init) fun m a =>
    m.alter (f a) (fun old => some (old.getD 0 + 1))

def mkOpGroups (standardCtors : Array DefaultCtor) (ops : Array CatOp) : Std.HashMap String Nat :=
  let opGroups : Std.HashMap String Nat :=
        standardCtors.foldl (init := {}) fun m c =>
          assert! c.leanName ∉ m
          m.insert c.leanName 1
  countSimilar ops (init := opGroups) (·.name.name)

def toDefaultOp (disambiguateCtor : String → Bool) (op : CatOp) : DefaultCtor :=
  let name := op.name
  let leanName :=
        if disambiguateCtor name.name then
          -- FIXME: We should ensure this is actually unique.
          s!"{name.dialect}_{name.name}"
        else
          name.name
  {
    leanName := leanName,
    strataName := some name,
    argDecls := op.argDecls
  }


def mkCategoryCtors (standardCtors : Array DefaultCtor) (ops : Array CatOp) : Array DefaultCtor :=
  let opGroups := mkOpGroups standardCtors ops
  standardCtors ++ ops.map (toDefaultOp (opGroups.getD · 0 > 1))

def mkCategories (catMap : CatOpMap) (exprHasEta : Bool) : Array (QualifiedIdent × Array DefaultCtor) :=
  catMap.fold (init := #[]) fun a cat ops =>
    if cat ∈ declaredCategories then
      a
    else
      let standardCtors := mkStandardCtors exprHasEta cat
      let allCtors := mkCategoryCtors standardCtors ops
      a.push (cat, allCtors)

def CatOpMap.onlyUsedCategories (m : CatOpMap) (d : Dialect) (exprHasEta : Bool) : Array (QualifiedIdent × Array DefaultCtor) :=
  let usedSet := mkUsedCategories m d
  m.fold (init := #[]) fun a cat ops =>
    if cat ∉ declaredCategories ∧ cat ∈ usedSet then
      let standardCtors := mkStandardCtors exprHasEta cat
      let allCtors := mkCategoryCtors standardCtors ops
      a.push (cat, allCtors)
    else
      a

/- Creates a local variable name from a string -/
def mkLocalIdent (name : String) : Ident :=
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
            | panic! s!"Unknown category {cat.fullName}"
          ops.foldl (init := g) fun g op =>
            op.argDecls.foldl (init := g) fun g (_, c) =>
              addArgIndices cat op.leanName c g resIdx
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
def mkScopedIdent (subName : Lean.Name) : CommandElabM Ident := do
  let scope ← getCurrNamespace
  let name := scope ++ subName
  let nameStr := toString subName
  return .mk (.ident .none nameStr.toSubstring subName [.decl name []])

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
  mkScopedIdent (← getCategoryScopedName cat)

/-- Return identifier for operator with given name to suport category. -/
def getCategoryOpIdent (cat : QualifiedIdent) (name : String) : GenM Ident := do
  mkScopedIdent <| (← getCategoryScopedName cat) |>.str name

partial def ppCat (c : SyntaxCat) : GenM Term := do
  let args ← c.args.mapM ppCat
  match c.head, args with
  | q`Init.CommaSepBy, #[c] => ``(Array $c)
  | q`Init.Option, #[c] => ``(Option $c)
  | q`Init.Seq, #[c] => ``(Array $c)
  | cat, #[] => getCategoryIdent cat
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

def genBinder (name : String) (typeStx : Term) : CommandElabM BracketedBinder := do
  let nameStx := mkLocalIdent name
  `(bracketedBinderF| ($nameStx : $typeStx))

def genCtor (op : DefaultCtor) : GenM (TSyntax ``ctor) := do
  let ctorId : Ident := mkLocalIdent op.leanName
  let binders ← op.argDecls.mapM fun (name, tp) => do
        genBinder name (← ppCat tp)
  `(ctor| | $ctorId:ident $binders:bracketedBinder* )

def mkInductive (cat : QualifiedIdent) (ctors : Array DefaultCtor) : GenM Command := do
  let ident ←  getCategoryIdent cat
  trace[Strata.generator] "Generating {ident}"
  `(inductive $ident : Type where
    $(← ctors.mapM genCtor):ctor*
    deriving Repr)

def categoryToAstTypeIdent (cat : QualifiedIdent) : Ident :=
  mkRootIdent <|
    match cat with
    | q`Init.Expr => ``Strata.Expr
    | q`Init.Type => ``Strata.TypeExpr
    | q`Init.TypeP => ``Strata.Arg
    | _ => ``Strata.Operation

structure ToOp where
  name : String
  argDecls : Array (String × SyntaxCat)

def toAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  mkScopedIdent <| (← getCategoryScopedName cat) ++ `toAst

def ofAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  mkScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst

def argCtor (v : Ident) (i : SyntaxCat) : GenM Term :=
  match i with
  | .atom qid@q`Init.Expr => do
    let toAst ← toAstIdentM qid
    ``(Arg.expr ($toAst $v))
  | .atom q`Init.Ident => ``(Arg.ident $v)
  | .atom q`Init.Num => ``(Arg.num $v)
  | .atom q`Init.Decimal => ``(Arg.decimal $v)
  | .atom q`Init.Str => ``(Arg.strlit $v)
  | .atom qid@q`Init.Type => do
    let toAst ← toAstIdentM qid
    ``(Arg.type ($toAst $v))
  | .atom qid@q`Init.TypeP => do
    let toAst ← toAstIdentM qid
    ``($toAst $v)
  | .atom qid => do
    let toAst ← toAstIdentM qid
    ``(Arg.op ($toAst $v))
  | .app (.atom q`Init.CommaSepBy) c => do
    let e ← mkFreshIdent (mkLocalIdent "e")
    let t ← argCtor e c
    ``(Arg.commaSepList (Array.map (fun ⟨$e, _⟩ => $t) (Array.attach $v)))
  | .app (.atom q`Init.Option) c => do
    let e ← mkFreshIdent (mkLocalIdent "e")
    let t ← argCtor e c
    ``(Arg.option (Option.map (fun ⟨$e, _⟩ => $t) (Option.attach $v)))
  | .app (.atom q`Init.Seq) c => do
    let e ← mkFreshIdent (mkLocalIdent "e")
    let t ← argCtor e c
    ``(Arg.seq (Array.map (fun ⟨$e, _⟩ => $t) (Array.attach $v)))
  | _ =>
    throwError s!"Unexpected category {repr i}"

abbrev MatchAlt := TSyntax ``Lean.Parser.Term.matchAlt

def toAstMatch (cat : QualifiedIdent) (op : DefaultCtor) : GenM MatchAlt := do
  let argDecls := op.argDecls
  let ctor : Ident ← getCategoryOpIdent cat op.leanName
  let args : Array (Ident × SyntaxCat) ← argDecls.mapM fun (nm, c) =>
    return (← mkFreshIdent (mkLocalIdent nm), c)
  let pat : Term ← ``($ctor $(args.map (·.fst)):term*)
  let rhs : Term ←
        match cat with
        | q`Init.Expr =>
          match op.leanName with
          | "fvar" =>
            assert! args.size = 1
            ``(Expr.fvar $(args[0]!.fst))
          | lname =>
            let some nm := op.strataName
              | return panic! s!"Unexpected builtin expression {lname}"
            let init ← ``(Expr.fn $(quote nm))
            args.foldlM (init := init) fun a (nm, tp) => do
              let e ← argCtor nm tp
              ``(Expr.app $a $e)
        | q`Init.Type => do
          let some nm := op.strataName
            | return panic! "Expected type name"
          let toAst ← toAstIdentM cat
          let argTerms : Array Term ← args.mapM fun (v, _) => ``($toAst $v)
          ``(TypeExpr.ident $(quote nm) $(← arrayLit argTerms))
        | q`Init.TypeP => do
          match op.leanName with
          | "type" => ``(Arg.cat (SyntaxCat.atom $(quote q`Init.Type)))
          | "expr" =>
            assert! args.size = 1
            let (nm, tp) := args[0]!
            argCtor nm tp
          | name =>
            panic! s!"Unexpected operator {name}"
        | _ =>
          let mName ←
            match op.strataName with
            | some n => pure n
            | none => throwError s!"Internal: Operation requires strata name"
          let argTerms : Array Term ← args.mapM fun (nm, tp) => argCtor nm tp
          ``(Operation.mk $(quote mName) $(← arrayLit argTerms))
  `(matchAltExpr| | $pat => $rhs)

def genToAst (cat : QualifiedIdent) (ops : Array DefaultCtor) (isRecursive : Bool) : GenM Command := do
  let catIdent ← getCategoryIdent cat
  let astType := categoryToAstTypeIdent cat
  let cases : Array MatchAlt ← ops.mapM (toAstMatch cat)
  let toAst ← toAstIdentM cat
  trace[Strata.generator] "Generating {toAst}"
  let v ← mkFreshIdent (mkLocalIdent "v")
  let t ←
    if isRecursive then
      `(suffix|termination_by sizeOf $v)
    else
      `(suffix|)
  `(def $toAst ($v : $catIdent) : $astType :=
      match $v:ident with $cases:matchAlt*
      $t:suffix)

def getOfIdentArg (vnm : String) (c : SyntaxCat) : GenM Term :=
  match c with
  | .atom cid@q`Init.Expr => do
    let vi ← mkFreshIdent <| mkLocalIdent <| vnm ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofExpressionM fun ⟨$vi, _⟩ => $ofAst $vi)
  | .atom q`Init.Ident => do
    ``(OfAstM.ofIdentM)
  | .atom q`Init.Num => do
    ``(OfAstM.ofNumM)
  | .atom q`Init.Decimal => do
    ``(OfAstM.ofDecimalM)
  | .atom q`Init.Str => do
    ``(OfAstM.ofStrlitM)
  | .atom cid@q`Init.Type => do
    let vi ← mkFreshIdent <| mkLocalIdent <| vnm ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofTypeM fun ⟨$vi, _⟩ => $ofAst $vi)
  | .atom cid@q`Init.TypeP => do
    let vi ← mkFreshIdent <| mkLocalIdent <| vnm ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(fun ⟨$vi, _⟩ => $ofAst $vi)
  | .atom cid => do
    let vi ← mkFreshIdent <| mkLocalIdent <| vnm ++ "_inner"
    let ofAst ← ofAstIdentM cid
    ``(OfAstM.ofOperationM fun ⟨$vi, _⟩ => $ofAst $vi)
  | .app (.atom q`Init.CommaSepBy) c => do
    let f ← getOfIdentArg (vnm ++ "_e") c
    ``(OfAstM.ofCommaSepByM $f)
  | .app (.atom q`Init.Option) c => do
    let f ← getOfIdentArg (vnm ++ "_e") c
    ``(OfAstM.ofOptionM $f)
  | .app (.atom q`Init.Seq) c => do
    let f ← getOfIdentArg (vnm ++ "_e") c
    ``(OfAstM.ofSeqM $f)
  | _ =>
    return panic! s!"getOfIdentArg {repr c} not supported."

def ofAstArgs (argDecls : Array (String × SyntaxCat)) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let (vnm, c) := argDecls[i]
    let v ← mkFreshIdent <| mkLocalIdent <| vnm ++ "_bind"
    let rhs0 ← getOfIdentArg vnm c
    let rhs ← ``(OfAstM.atArg $argsVar $(quote i) $rhs0)
    let stmt ← `(doSeqItem| let $v ← $rhs:term)
    return (v, stmt)
  return args.unzip

def ofAstMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat) (op : DefaultCtor) (rhs : Term) : GenM MatchAlt := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanName}"
  let some nameIndex := nameIndexMap[name]?
    | return panic! s!"Unbound operator name {name}"
  `(matchAltExpr| | Option.some $(quote nameIndex) => $rhs)

def ofAstExprMatchRhs (cat : QualifiedIdent) (argsVar : Ident) (op : DefaultCtor) : GenM Term:= do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let some nm := op.strataName
    | return panic! s!"Missing name for {op.leanName}"
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  let checkExpr ← ``(OfAstM.checkArgCount $(quote nm) $(quote argCount) (Subtype.val $(argsVar)))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    return $ctorIdent $parsedArgs:term*)


def ofAstExprMatch (nameIndexMap : Std.HashMap QualifiedIdent Nat)
      (cat : QualifiedIdent) (argsVar : Ident) (op : DefaultCtor) : GenM (Option MatchAlt) := do
  match op.leanName with
  | "fvar" =>
    pure none
  | _ => do
    let rhs ← ofAstExprMatchRhs cat argsVar op
    some <$> ofAstMatch nameIndexMap op rhs

def ofAstTypeArgs (argDecls : Array (String × SyntaxCat)) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let ofAst ← ofAstIdentM q`Init.Type
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let (vnm, _) := argDecls[i]
    let v ← mkFreshIdent <| mkLocalIdent vnm
    let rhs ← ``($ofAst $argsVar[$(quote i)])
    let stmt ← `(doSeqItem| let $v ← $rhs:term)
    return (v, stmt)
  return args.unzip

def ofAstTypeMatchRhs (cat : QualifiedIdent) (argsVar : Ident) (op : DefaultCtor) : GenM Term := do
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let (parsedArgs, stmts) ← ofAstTypeArgs argDecls argsVar
  let checkExpr ← ``(OfAstM.checkTypeArgCount $(quote argDecls.size) $(argsVar))
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    pure <| $ctorIdent $parsedArgs:term*)

def ofAstOpMatchRhs (cat : QualifiedIdent) (argsVar : Ident) (op : DefaultCtor) : GenM Term := do
  let some name := op.strataName
    | return panic! s!"Unexpected operator {op.leanName}"
  let ctorIdent ← getCategoryOpIdent cat op.leanName
  let argDecls := op.argDecls
  let argCount := argDecls.size
  let checkExpr ← ``(OfAstM.checkArgCount $(quote name) $(quote argCount) (Subtype.val $(argsVar)))
  let (parsedArgs, stmts) ← ofAstArgs argDecls argsVar
  `(do
    let .up p ← $checkExpr:term
    $stmts:doSeqItem*
    return $ctorIdent $parsedArgs:term*)

/--
Creates a mapping from operation names (QualifiedIdent) to unique natural numbers.
This is used to pattern match in the generated code.
-/
def createNameIndexMap (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM (Std.HashMap QualifiedIdent Nat × Ident × Command) := do
  let nameIndexMap := ops.foldl (init := {}) fun map op =>
    match op.strataName with
    | none => map  -- Skip operators without a name
    | some name => map.insert name map.size  -- Assign the next available index
  let ofAstNameMap ← mkScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst.map
  let cmd ← `(def $ofAstNameMap : Std.HashMap Strata.QualifiedIdent Nat := Std.HashMap.ofList $(quote nameIndexMap.toList))
  pure (nameIndexMap, ofAstNameMap, cmd)

def mkOfAstDef (cat : QualifiedIdent) (ofAst : Ident) (v : Ident) (rhs : Term) (isRecursive : Bool) : GenM Command := do
  let catIdent ← getCategoryIdent cat
  let t ←
    if isRecursive ∧ false then
      `(suffix|termination_by sizeOf $v)
    else
      `(suffix|)
  `(partial def $ofAst ($v : $(categoryToAstTypeIdent cat)) : OfAstM $catIdent := $rhs $t:suffix)

def genOfAst (cat : QualifiedIdent) (ops : Array DefaultCtor) (isRecursive : Bool) : GenM (Array Command × Command) := do
  let ofAst ← ofAstIdentM cat
  trace[Strata.generator] "Generating {ofAst}"
  let v ← mkFreshIdent (mkLocalIdent "v")
  match cat with
  | q`Init.Expr =>
    let argsVar ← mkFreshIdent (mkLocalIdent "args")
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let fvarCtorIdent ← getCategoryOpIdent cat "fvar"
    let cases : Array MatchAlt ← ops.filterMapM (ofAstExprMatch nameIndexMap cat argsVar)
    let rhs ←
      `(let vnf := ($v).hnf
        let $argsVar := vnf.args
        match (vnf.fn) with
        | Strata.Expr.fvar i => pure ($fvarCtorIdent i)
        | Strata.Expr.fn fnId =>
          (match ($ofAstNameMap[fnId]?) with
          $cases:matchAlt*
          | _ => OfAstM.throwUnknownIdentifier $(quote cat) fnId)
        | _ => pure (panic! "Unexpected argument"))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs isRecursive)
  | q`Init.Type =>
    let argsVar ← mkFreshIdent (mkLocalIdent "args")
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let cases : Array MatchAlt ← ops.mapM fun op =>
      ofAstMatch nameIndexMap op =<< ofAstTypeMatchRhs cat argsVar op
    let rhs ← `(match ($v) with
      | Strata.TypeExpr.ident typeIdent $argsVar =>
        (match ($ofAstNameMap[typeIdent]?) with
        $cases:matchAlt*
        | _ => OfAstM.throwUnknownIdentifier $(quote cat) typeIdent)
      | _ => OfAstM.throwExpected "Expected type" (Arg.type $v))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs isRecursive)
  | q`Init.TypeP =>
    let catCtorIdent ← getCategoryOpIdent cat "type"
    let exprCtorIdent ← getCategoryOpIdent cat "expr"
    let typeOfAst ← ofAstIdentM q`Init.Type
    let rhs ← `(match $v:term with
      | Arg.cat (SyntaxCat.atom $(quote q`Init.Type)) =>
        return $catCtorIdent
      | Arg.type strataType => do
        let tp ← $typeOfAst:term strataType
        return $exprCtorIdent tp
      | a =>
        OfAstM.throwExpected "Type parameter or type expression" a)
    pure (#[], ← mkOfAstDef cat ofAst v rhs isRecursive)
  | _ =>
    let argsVar ← mkFreshIdent (mkLocalIdent "args")
    let (nameIndexMap, ofAstNameMap, cmd) ← createNameIndexMap cat ops
    let cases : Array MatchAlt ← ops.mapM fun op =>
      ofAstMatch nameIndexMap op =<< ofAstOpMatchRhs cat argsVar op
    let rhs ← `(
      let $argsVar : Strata.SizeBounded (Array Arg) $v 1 := Subtype.mk (Operation.args $v) (by
            simp only [Strata.Operation.sizeOf_spec $v]
            omega)
      match ($ofAstNameMap[Operation.name $v]?) with
      $cases:matchAlt*
      | _ => OfAstM.throwUnknownIdentifier $(quote cat) (Operation.name $v))
    pure (#[cmd], ← mkOfAstDef cat ofAst v rhs isRecursive)

abbrev InhabitedSet := Std.HashSet QualifiedIdent

def checkInhabited (cat : QualifiedIdent) (ops : Array DefaultCtor) : StateT InhabitedSet GenM Unit := do
  if cat ∈ (←get) then
    return ()
  let catIdent ← getCategoryIdent cat
  for op in ops do
    let inhabited ← get
    let isInhabited := op.argDecls.all fun (_, c) =>
        match c with
        | .atom c => c ∈ inhabited
        | .app (.atom q`Init.Seq) _ => true
        | .app (.atom q`Init.CommaSepBy) _ => true
        | .app (.atom q`Init.Option) _ => true
        | _ => panic! s!"Unknown category {repr c}"
    if !isInhabited then
      continue
    let ctor ← getCategoryOpIdent cat op.leanName
    let d ← `(default)
    let e ← op.argDecls.size.foldM (init := ctor) fun _ _ e => `($e $d)
    StateT.lift <| runCmd <|
      elabCommand =<< `(instance : Inhabited $catIdent where default := $e)
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
    let newCats := Std.HashSet.ofArray <| allCtors.map (·.fst)
    let s ←
      withTraceNode `Strata.generator (fun _ =>
        return m!"Declarations group: {allCtors.map (·.fst)}") do
        -- Check if the toAst/ofAst definitions will be recursive by looking for
        -- categories that are not already in inhabited set.
        let isRecursive := allCtors.any fun (_, ops) =>
              ops.any fun op =>
                op.argDecls.any fun (_, c) =>
                  c.foldOverAtomicCategories (init := false)
                    fun b qid => b || qid ∈ newCats
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
            genToAst cat ctors (isRecursive := isRecursive)
          runCmd <| elabCommands toAstDefs
        profileitM Lean.Exception s!"Generating ofAstDefs {cats}" (← getOptions) do
          let ofAstDefs ← allCtors.mapM fun (cat, ctors) => do
            let (cmds, d) ← genOfAst cat ctors (isRecursive := isRecursive)
            (cmds.forM elabCommand : CommandElabM Unit)
            pure d
          runCmd <| elabCommands ofAstDefs
        pure inhabitedCats
    inhabitedCats := s

def runGenM (pref : String) (catNames : Array QualifiedIdent) (exprHasEta : Bool) (m : GenM α) : CommandElabM α := do
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
    categoryNameMap := categoryNameMap,
    exprHasEta := exprHasEta
  }
  m ctx

/--
`#strata_gen ident` generates an AST for the dialect `ident`.

This includes functions for
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
    runGenM dialectName catNames exprHasEta (gen cats)
  | _ =>
    throwUnsupportedSyntax

end Strata
