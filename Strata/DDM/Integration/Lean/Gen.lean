/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command

public meta import Strata.DDM.AST
public meta import Strata.DDM.BuiltinDialects.Init
public import Strata.DDM.Integration.Lean.BoolConv
public import Strata.DDM.Integration.Lean.GenTrace
public meta import Strata.DDM.Integration.Lean.Env
public meta import Strata.DDM.Util.Graph.Preimage
public meta import Strata.DDM.Util.Graph.Tarjan
public meta import Strata.DDM.Util.OrderedSet

meta import Strata.DDM.BuiltinDialects.StrataDDL
import all Strata.DDM.Util.Array
import all Strata.DDM.Util.Vector

import Std.Data.HashSet.Lemmas

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

open Strata.DDM (OrderedSet)

meta section

namespace Strata.OutGraph

/--
An index map `m` contains a partial mapping information of
nodes from a graph with `n` nodes to a graph `m._size`
nodes.  Nodes in the source graph should either map to a unique
node in the target graph or `0` if they are not included.
-/
structure PartialNodeMapping (n : Nat) where
  /--
  Map from indices in source graph to target graph to either
  `0` if the node is droped or `idx + 1` if the node is in the
  target graph.
  -/
  embed : Vector Nat n
  /--
  Reverse map from target graph to source graph.

  N.B. The number of elements is the size of the target graph.
   -/
  rev : Array Nat
  /--
  Constraint that all reverse node maps are in bound.
  -/
  revBound : ∀(m : Nat), m ∈ rev → m < n
  /--
  Constraint that all
  -/
  embedBound : ∀(m : Nat), m ∈ embed → m ≤ rev.size

namespace PartialNodeMapping

abbrev targetSize {n} (im : PartialNodeMapping n) : Nat := im.rev.size

def empty (source_capacity : Nat) : PartialNodeMapping 0 := {
  embed := Vector.emptyWithCapacity source_capacity
  rev := #[]
  revBound := by grind
  embedBound := fun m mem => by simp [Vector.emptyWithCapacity] at mem;
}

/--
Return index of source node in targt graph.
-/
def sourceNode {n} (m : PartialNodeMapping n) (i : Nat)
      (p : i < m.targetSize := by get_elem_tactic) : Fin n :=
  ⟨m.rev[i], m.revBound _ (by grind)⟩

def cast {m n} (em : PartialNodeMapping m) (eq : m = n) : PartialNodeMapping n :=
  have q : PartialNodeMapping m = PartialNodeMapping n := congrArg PartialNodeMapping eq
  q.mp em

def embedFn {n} (em : PartialNodeMapping n) (i : Fin n) : Fin (em.targetSize + 1) :=
  let e := em.embed[i]
  have mem : e ∈ em.embed := by simp [e]
  have _ : e ≤ em.targetSize := em.embedBound _ mem
  have ep : e < em.targetSize + 1 := by omega
  ⟨e, ep⟩

def extend {n} (em : PartialNodeMapping n) (mem : Bool) : PartialNodeMapping (n+1) :=
  let {rev, embed, revBound, embedBound } := em
  if mem then
    let rev' := rev.push embed.size
    { rev := rev'
      embed := embed.push rev'.size
      revBound := by grind
      embedBound := by grind
    }
  else
    { rev := rev
      embed := embed.push 0
      revBound := fun v mem => by grind
      embedBound := fun m mem => by grind
    }

def fromVector.aux {m n} (usedSet : Vector Bool n) (t : PartialNodeMapping m) (ap : m ≤ n := by omega) : PartialNodeMapping n :=
  if ilt : m < n then
    fromVector.aux usedSet (t.extend usedSet[m])
  else
    t.cast (by omega)
  termination_by n - m

def fromVector {n} (usedSet : Vector Bool n) : PartialNodeMapping n :=
  fromVector.aux usedSet (.empty n) (by grind)

end PartialNodeMapping

/--
`g.projection emb` generates the minimal graph `g'` with `n` vertices which for each edge
each edges `⟨s, t⟩ ∈ g`, `g'` contains the edge `⟨emb s - 1, emb t -1⟩` if `emb s, emb t > 0`.

This is a partial homomophism since nodes can be dropped by mapping then to `n`.
-/
def projection {m n} (g : OutGraph m) (emb : Fin m -> Fin (n+1)) : OutGraph n :=
  let gn : OutGraph n := { edges := .replicate n #[] }
  let addEdge (a : Array (Fin n)) (i : Fin m) :=
        let ⟨j, jlt⟩ := emb i
        if jp : j = 0 then
          a
        else
          a.push ⟨j - 1, by omega⟩
  let appendEdgesToArray (i : Fin m) (a : Array (Fin n)) : Array (Fin n) :=
        g.edges[i].foldl (init := a) addEdge
  let appendEdges (g : OutGraph n) (i : Fin m) : OutGraph n :=
        let ⟨j, jlt⟩ := emb i
        if jp : j = 0 then
          gn
        else
          { edges := gn.edges.modify ⟨j-1, by omega⟩ (appendEdgesToArray i) }
  Fin.foldl m (init := gn) appendEdges



end Strata.OutGraph

namespace Strata.Lean

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
def currScopedIdent {m} [Monad m] [Lean.MonadResolveName m]
      (subName : Lean.Name) : m Ident := do
  (scopedIdent · subName) <$> getCurrNamespace

/- Returns an identifier from a string. -/
def localIdent (name : String) : Ident :=
  let dName := .anonymous |>.str name
  .mk (.ident .none name.toSubstring dName [])

/-- Create a canonical identifier. -/
def mkCanIdent (src : Lean.Syntax) (val : Name) : Ident :=
  mkIdentFrom src val true

/--
Create an identifier to a fully qualified Lean name
-/
def mkRootIdent (name : Name) : Ident :=
  let rootName := `_root_ ++ name
  .mk (.ident .none name.toString.toSubstring rootName [.decl name []])

end Lean

open Lean (currScopedIdent localIdent mkCanIdent mkRootIdent)

def arrayLit {m} [Monad m] [Lean.MonadQuotation m] (as : Array Term) : m Term := do
  ``( (#[ $as:term,* ] : Array _) )

namespace SyntaxCatF

/--
Invoke `f` over all atomic (no argument) category names in `c`.
-/
def foldOverAtomicCategories {α}
      (cat : SyntaxCat) (init : α) (f : α → QualifiedIdent → α) : α :=
  if cat.args.size = 0 then
    f init cat.name
  else
    cat.args.foldl (init := init) fun v a => foldOverAtomicCategories a v f
termination_by cat
decreasing_by
  rw [sizeOf_spec cat]
  decreasing_tactic

/--
If we have a an action that is preserves an invariant on all names, then it
is preserved when folding over the atomic categories.
-/
theorem foldOverAtomicCategories_invariant {α β}
      (measure : α → β)
      {f : α  → QualifiedIdent → α}
      (inv : ∀t name, measure (f t name) = measure t)
      (cat : SyntaxCat) (init : α)  :
    measure (cat.foldOverAtomicCategories init f) = measure init := by

  unfold foldOverAtomicCategories
  if p : cat.args.size = 0 then
    simp [p, inv]
  else
    simp [p]
    apply Array.foldl_induction (motive := fun _ s => measure s = measure init) (h0 := rfl)
    intro i b b_eq
    simp only [foldOverAtomicCategories_invariant measure inv cat.args[i]]
    exact b_eq
termination_by cat
decreasing_by
  rw [sizeOf_spec cat]
  decreasing_tactic

end SyntaxCatF

/--
Given a dialect map and a specific dialect, this computes an array
with the imported dialects.  The entries are ordered so that all a dialects
imports appear before it in the array.
-/
def computeImportedDialects (dialects : DialectMap)
        (name : DialectName) : Array DialectName :=
  let s : OrderedSet DialectName := .empty
  let s := s.insert initDialect.name
  let imports (name : DialectName) : Array DialectName :=
      match dialects[name]? with
      | some d => d.imports
      | none => #[]
  s.addAllPostorder imports name |>.toArray

abbrev CategoryName := QualifiedIdent

/--
Dialect names that are not allowed.
-/
def reservedCatNames : Std.HashSet String := { "Type" }

/--
This returns true if the name is a category in the Init or StrataDDL dialect.
-/
def builtinsWellDefined (category : QualifiedIdent) : Bool :=
  match category.dialect with
  | "Init" =>
    match initDialect.cache[category.name]? with
    | some (.syncat _) => true
    | _ => false
  | "StrataDDL" =>
    match StrataDDL.cache[category.name]? with
    | some (.syncat _) => true
    | _ => false
  | _ => false

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

#guard declaredCategories.all fun nm _ => builtinsWellDefined nm

/--
Maps builtin polymorphic categories to their Lean representation
-/
def polymorphicBuiltinCategories : Std.HashMap QualifiedIdent Name :=
  .ofList [
    (q`Init.CommaSepBy, ``Array),
    (q`Init.Option, ``Option),
    (q`Init.Seq, ``Array),
  ]

def polyCatMap : Std.HashMap QualifiedIdent Lean.Expr := .ofList [
  (q`Init.CommaSepBy, .const ``Array [0]),
  (q`Init.Option, .const ``Option [0]),
  (q`Init.Seq, .const ``Array [0]),
]

/--
Privatte categories are categories that should not be directly
used in user dialects.

Note.  As of 1/6/2026, this is not checked during Dialect parsing;
we should fix this.
-/
def privateCategories : Std.HashSet CategoryName := {
  q`Init.TypeExpr,
  q`Init.BindingType,
  q`StrataDDL.Binding
}
#guard privateCategories.all builtinsWellDefined

def ignoreCategory (cat : CategoryName) : Bool :=
  cat ∈ declaredCategories ∨ cat ∈ privateCategories

/--
Special categories ignore operations introduced in Init, but are populated
with operators via functions/types.

User dialects should not have operators that extend them, but operators
and functions may reference them.
-/
def specialCategories : Std.HashSet CategoryName := {
  q`Init.Expr,
  q`Init.Type,
  q`Init.TypeP
}
#guard specialCategories.all builtinsWellDefined


def annTypeExpr (base ann : Lean.Expr) := mkApp2 (mkConst ``Ann) base ann

/--
Argument declaration for code generation.
-/
structure CatOpArg where
  name : String
  cat : SyntaxCat
  wrap : Bool := true

/--
An operation at the category level.
-/
structure CatOp where
  name : QualifiedIdent
  argDecls : Array CatOpArg


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
  /--
  Flag indicating the generated constructor should add an annotation field as a
  first argument.
  -/
  includeAnn : Bool := true
  /--
  Argument declarations
  -/
  argDecls : Array CatOpArg
  /--
  Either annotations are included or there is a single argument we can get
  the annotation from.
  -/
  includeAnnInvariant :
    includeAnn ∨
      if p : argDecls.size = 1 then
        (argDecls[0]'(p ▸ Nat.zero_lt_one)).wrap = true
      else
        false := by simp

def DefaultCtor.leanName (c : DefaultCtor) : Name := .str .anonymous c.leanNameStr

namespace CatOp

partial def checkCat (op : QualifiedIdent) (c : SyntaxCat) : Except String Unit := do
  c.args.forM (checkCat op)
  let f := c.name
  if f ∈ privateCategories then
    throw s!"{op.fullName} refers to unsupported category {f.fullName}."

def ofArgDecl (op : QualifiedIdent) (d : ArgDecl) : Except String CatOpArg := do
  let cat ←
    match d.kind with
    | .type tp =>
      pure <| .atom tp.ann q`Init.Expr
    | .cat c =>
      checkCat op c
      pure c
  -- Check if unwrap metadata is present
  let unwrap := q`StrataDDL.unwrap ∈ d.metadata
  pure { name := d.ident, cat, wrap := !unwrap }

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

structure ErrorBundle (α : Type) where
  value : α
  errors : Array String := #[]

def ErrorM (α : Type) := StateM (ErrorBundle α)
  deriving Monad

namespace ErrorM

def addError {α} (msg : String) : ErrorM α Unit :=
  (modify fun s => { s with errors := s.errors.push msg } : StateM _ _)

instance {α} : MonadState α (ErrorM α) where
  get := (return (←get).value : StateM _ _)
  set v := (modify (fun s => { value := v, errors := s.errors}) : StateM _ _)
  modifyGet f := modifyGet (m := StateM _) fun ⟨v, errors⟩ =>
    let (a, v) := f v
    (a, ⟨v, errors⟩)

end ErrorM

structure CatIndexMap where
  idents : Array QualifiedIdent
  ops : Vector (Array CatOp) idents.size
  map : Std.HashMap QualifiedIdent Nat
  inv : ∀(name : QualifiedIdent) (p : name ∈ map), map[name] < idents.size

namespace CatIndexMap

protected def empty : CatIndexMap where
  idents := #[]
  ops := #v[]
  map := {}
  inv := fun name mem => by simp at mem

instance : EmptyCollection CatIndexMap where
  emptyCollection := .empty

instance : Inhabited CatIndexMap where
  default := .empty

abbrev size (m : CatIndexMap) := m.idents.size

def indexOf?  (cats : CatIndexMap) (cat : QualifiedIdent)
    : Option (Fin cats.size) :=
  match h : cats.map[cat]? with
  | none => none
  | some idx =>
    have idx_lt : idx < cats.size := by
      have ⟨p, eq⟩ :=  Std.HashMap.getElem?_eq_some_iff.mp h
      simp [← eq]
      exact cats.inv cat _
    some ⟨idx, idx_lt⟩

-- Monad that collects errors from adding declarations.
abbrev CatIndexM := ErrorM CatIndexMap

/--
Add a category to the map.
-/
def addCat (m : CatIndexMap) (cat : CategoryName) (_ : cat ∉ m.map): CatIndexMap :=
  let n := m.idents.size
  { idents := m.idents.push cat
    ops := m.ops.push #[] |>.cast (by simp)
    map := m.map.insert cat n
    inv := fun name namep => by
      simp at namep
      if h : cat = name then
        simp [h]
        omega
      else
        have inv := m.inv name
        grind
  }

def addCatM (cat : CategoryName) : CatIndexM Unit := do
  if ignoreCategory cat then
    pure ()
  else
    let already ← modifyGet fun s =>
          if mem : cat ∈ s.map then
            (true, s)
          else
            (false, s.addCat cat mem)
    if already then
      .addError s!"Duplicate category {cat}"


def addOpM (cat : CategoryName) (op : CatOp) : CatIndexM Unit := do
  match (←get).indexOf? cat with
  | none =>
    .addError s!"Missing operator category {cat}"
  | some idx =>
    modify fun m => { m with ops := Vector.modify! m.ops idx.val (·.push op) }

def addDecl (d : DialectName) (decl : Decl) : CatIndexM Unit :=
  let addCatOp (cat : QualifiedIdent) (act : Except String CatOp) : CatIndexM Unit :=
    match act with
    | .ok op =>
      addOpM cat op
    | .error msg => do
      .addError msg
  match decl with
  | .syncat decl =>
    addCatM ⟨d, decl.name⟩
  | .op decl => do
    let cat := decl.category
    if ignoreCategory cat ∨ cat ∈ specialCategories then
      -- Ignored and special category operators are ignored in `Init`, but
      -- generate errors when operators are in other dialects.
      if d ≠ "Init" then
        .addError s!"Skipping operation {decl.name} in {d}: {cat} cannot be extended."
    else
      addCatOp decl.category (CatOp.ofOpDecl d decl)
  | .type decl =>
    addOpM q`Init.Type (.ofTypeDecl d decl)
  | .function decl =>
    addCatOp q`Init.Expr (CatOp.ofFunctionDecl d decl)
  | .metadata _ =>
    pure ()

def addDialect (d : Dialect) : CatIndexM Unit :=
  d.declarations.forM (addDecl d.name)

/- `CatopMap` with only initial dialect-/
protected def init : CatIndexMap :=
  let ((), s) := addDialect initDialect { value := {}, errors := #[] }
  if s.errors.size > 0 then
    panic! s!"Error in Init dialect {s.errors}"
  else
    s.value

end CatIndexMap

def mkCatIndexMap (a : Array Dialect) : CatIndexMap × Array String :=
  let act :=
        a.forM fun d =>
          if d.name = "Init" then
            pure ()
          else
            CatIndexMap.addDialect d
  let ((), s) := act { value := CatIndexMap.init, errors := #[] }
  (s.value, s.errors)

structure WorkSet (n : Nat) where
  set : Vector Bool n
  pending : Array (Fin n)
  inv : ∀idx, idx ∈ pending → set[idx.val] = true

namespace WorkSet

def remainingCount {n} (s : WorkSet n) : Nat :=
  (s.set.toArray.filter (!·)).size + s.pending.size

def empty {n} : WorkSet n :=
  { set := .replicate _ false
    pending := #[]
    inv := fun idx idxp => by simp only [Array.mem_empty_iff] at idxp
  }

def addIdx {n} (s : WorkSet n) (idx : Fin n) : WorkSet n :=
  if p : s.set[idx] = true then
    s
  else
    let { set, pending, inv } := s
    { set := set.set idx true
      pending := pending.push idx
      inv := by grind
    }

theorem remainingCount_addIdx {n} (s : WorkSet n) (idx : Fin n) :
  (s.addIdx idx).remainingCount = s.remainingCount := by
  simp only [WorkSet.addIdx]
  if h : s.set[idx] = true then
    simp [h]
  else
    have eq_false : s.set[idx.val] = false :=
      iff_of_eq (Bool.not_eq_true (s.set[idx.val])) |>.mp h
    simp [-Vector.size_toArray, -Array.size_set,
          remainingCount, Array.size_filter_set, eq_false]
    have false_in : false ∈ s.set :=  ⟨Array.mem_of_getElem eq_false⟩
    have size_pos : (Array.filter (fun x => !x) s.set.toArray).size > 0 := by
      simp [-Vector.size_toArray, Array.size_filter_pos_iff, false_in]
    omega


@[inline]
def pop {n} (s : WorkSet n) (p : s.pending.size > 0) : WorkSet n :=
  let { set, pending, inv } := s
  { set
    pending := pending.pop
    inv := by
      intro idx mem
      apply inv
      simp [Array.mem_pop_ne p, mem]
   }

theorem remaining_count_pop {m} (s : WorkSet m) (p : s.pending.size > 0) :
  (s.pop p).remainingCount + 1 = s.remainingCount := by
  simp_all [pop, remainingCount]
  grind

end WorkSet

def addIdent (m : CatIndexMap) (errors : Array String)
      (op : QualifiedIdent) (arg : String) (nm : QualifiedIdent) : Array String :=
  if nm ∈ declaredCategories then
    errors
  else if nm ∈ privateCategories then
    errors.push s!"{op} {arg} cannot reference private category {nm}."
  else if nm ∈ m.map then
    errors
  else
    errors.push s!"{op} {arg} references undeclared category {nm}."

def addCatArg (m : CatIndexMap) (errors : Array String) (op : QualifiedIdent) (arg : String)
    (cat : SyntaxCat) : Array String :=
  cat.foldOverAtomicCategories (init := errors) (addIdent m · op arg ·)


/--
Add all atomic categories in bindings to set.
-/
def addArgCategories (m : CatIndexMap) (errors : Array String)
      (op : QualifiedIdent) (args : ArgDecls) : Array String :=
  args.foldl (init := errors) fun errors b => addCatArg m errors op b.ident b.kind.categoryOf

def addNewIdent (m:CatIndexMap) (s : Array String) (dialect : String) (nm : QualifiedIdent) :
    Array String :=
  if nm ∈ declaredCategories then
    s
  else if nm ∈ privateCategories then
    s.push s!"{dialect} cannot reference private category {nm}."
  else if nm ∉ m.map then
    s.push s!"{dialect} references undeclared category {nm}."
  else
    s

def checkDialect (m : CatIndexMap) (d : Dialect) : Array String :=
  let dname := d.name
  d.declarations.foldl (init := #[]) fun s decl =>
    match decl with
    | .syncat decl =>
      addNewIdent m s dname ⟨dname, decl.name⟩
    | .op decl =>
      let opName : QualifiedIdent := ⟨dname, decl.name⟩
      if decl.category ∈ specialCategories then
        s.push s!"{opName} extends special category {decl.category}."
      else
        let s := addNewIdent m s dname decl.category
        let s := addArgCategories m s opName decl.argDecls
        s
    | .type _ =>
      addNewIdent m s dname q`Init.Type
    | .function decl =>
      let s := addNewIdent m s dname q`Init.Expr
      let s := addArgCategories m s ⟨dname, decl.name⟩ decl.argDecls
      s
    | .metadata _ => s

/--
Convert the category index map into a graph.
-/
def indexMapToGraph (cats : CatIndexMap) : OutGraph cats.size :=
  let n := cats.size
  let g : OutGraph n := OutGraph.empty n
  -- Build map from qualified identifier to index in categories.
  let identIndexMap := cats.map

  let addArgIndices (cat : QualifiedIdent)
                    (opName : QualifiedIdent)
                    (c : SyntaxCat)
                    (init : OutGraph n)
                    (resIdx : Fin n) : OutGraph n :=
        c.foldOverAtomicCategories (init := init) fun g q =>
          match cats.indexOf? q with
          | some i => g.addEdge i resIdx
          | none => g
  n.fold (init := g) fun i ip g => Id.run do
    let cat := cats.idents[i]
    let ops := cats.ops[i]
    ops.foldl (init := g) fun g op =>
      op.argDecls.foldl (init := g) fun g arg =>
        addArgIndices cat op.name arg.cat g ⟨i, ip⟩


/--
Return indices of categories that are introduced or extended in this dialect.
-/
def newCategories (m : CatIndexMap) (d : Dialect) : Std.HashSet (Fin m.size) :=
  -- Generate set of all categories that appear in this file
  let addIdent (s : Std.HashSet (Fin m.size)) (nm : QualifiedIdent) :=
        match m.indexOf? nm with
        | some idx => s.insert idx
        | none => s

  let rec addCat (s : Std.HashSet (Fin m.size)) (cat : SyntaxCat) :=
        if cat.args.size = 0 then
          match m.indexOf? cat.name with
          | some idx => s.insert idx
          | none => s
        else
          cat.args.foldl (init := s) fun s i => addCat s i

  d.declarations.foldl (init := {}) fun s decl =>
    match decl with
    | .syncat decl => addIdent s ⟨d.name, decl.name⟩
    | .op decl => addIdent s decl.category
    | .type _ => addIdent s q`Init.Type
    | .function _ => addIdent s q`Init.Expr
    | .metadata _ => s

def mkUsedCategories (m : CatIndexMap) (d : Dialect) : Vector Bool m.size :=
  -- Generate set of all categories that appear in this file
  OutGraph.preimage_closure (indexMapToGraph m) (newCategories m d)

def mkStandardCtors (exprHasEta : Bool) (cat : QualifiedIdent) : Array DefaultCtor :=
  match cat with
  | q`Init.Expr =>
    let fvar := {
      leanNameStr := "fvar"
      argDecls := #[{ name := "idx", cat := .atom .none q`Init.Num, wrap := false }]
    }
    if exprHasEta then
      #[fvar,
        { leanNameStr := "bvar"
          argDecls := #[{ name := "idx", cat := .atom .none q`Init.Num, wrap := false }]
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

/-- Array with undeclared categories and their constructors. -/
abbrev CatOpArray := Array (QualifiedIdent × Array DefaultCtor)

@[inline]
def ctors (exprHasEta : Bool) (m : CatIndexMap) (i : Fin m.size) : QualifiedIdent × Array DefaultCtor :=
  let cat := m.idents[i]
  let standardCtors := mkStandardCtors exprHasEta cat
  let usedNames : Std.HashSet String := {}
  let ops := m.ops[i]
  let (allCtors, _) :=
        ops.foldl (init := (standardCtors, usedNames)) fun (a, s) op =>
          let dOp := toDefaultOp s op
          (a.push dOp, s.insert dOp.leanNameStr)
  (cat, allCtors)

def catOpToGraph (categories : CatOpArray) : OutGraph categories.size :=
  let n := categories.size
  let g : OutGraph n := OutGraph.empty n
  -- Build map from qualified identifier to index in categories.
  let identIndexMap : Std.HashMap QualifiedIdent (Fin n) :=
        n.fold (init := {}) fun i p m =>
          m.insert categories[i].fst ⟨i, p⟩

  let addArgIndices (cat : QualifiedIdent)
                    (opName : String)
                    (c : SyntaxCat)
                    (init : OutGraph n)
                    (resIdx : Fin n) : OutGraph n :=
        c.foldOverAtomicCategories (init := init) fun g q =>
          if q ∈ declaredCategories then
            g
          else
            match identIndexMap[q]? with
            | some i => g.addEdge i resIdx
            | none => panic! s!"{opName} in {cat} has unknown category {q.fullName}"
  n.fold (init := g) fun i ip g => Id.run do
    let (cat, ops) := categories[i]
    ops.foldl (init := g) fun g op =>
      op.argDecls.foldl (init := g) fun g arg =>
        addArgIndices cat op.leanNameStr arg.cat g ⟨i, ip⟩

structure GenContext where
  -- Syntax for #strata_gen for source location purposes.
  src : Lean.Syntax
  /--
  Maps category identifiers to their relative Lean name.
  -/
  categoryNameMap : Std.HashMap QualifiedIdent Name

abbrev GenM := ReaderT GenContext CommandElabM

def runCmd {α} (act : CommandElabM α) : GenM α := fun _ => act

/-- Create a fresh name. -/
def genFreshLeanName (s : String) : GenM Name := do
  let fresh ← modifyGet fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  let n : Name := .anonymous |>.str s
  return Lean.addMacroScope (← getEnv).mainModule n fresh

/-- Create a fresh name. -/
def genFreshIdentPair (s : String) : GenM (Ident × Ident) := do
  let name ← genFreshLeanName s
  let src := (←read).src
  return (mkIdentFrom (canonical := true) src name, mkIdentFrom src name)

/-- Create a identifier from a name. -/
def genIdentFrom (name : Name) (canonical : Bool := false) : GenM Ident := do
  return mkIdentFrom (←read).src name canonical

/-- Return identifier for operator with given
 name to Lean name. -/
def getCategoryScopedName (cat : QualifiedIdent) : GenM Name := do
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return catName
  | none =>
    return panic! s!"getCategoryScopedName given {cat}"

/--
`gmkCatExpr annType c unwrap` returns the Lean type of the `c` with the given
`unwrap` flag and annotation type `annType`.

This expression must have type `Type`.
-/
def leanCatTypeExpr (annType : Lean.Expr) (c : SyntaxCat) (wrap : Bool := true) :
      GenM Lean.Expr := do
  let args ← c.args.attach.mapM (fun ⟨sc, _⟩ => leanCatTypeExpr annType sc)

  -- Handle polymorphic categories.
  if let some nm := polymorphicBuiltinCategories[c.name]? then
    assert! args.size == 1
    return annTypeExpr (mkAppN (.const nm [0]) args) annType
  assert! args.size == 0

  -- Handle declared categories
  if let some nm := declaredCategories[c.name]? then
    -- Check if unwrap is specified
    if wrap then
      return annTypeExpr (mkConst nm) annType
    else
      return mkConst nm  -- Return unwrapped type
  -- Handle base case
  let relName ← getCategoryScopedName c.name
  let catName := (← getCurrNamespace) ++ relName
  let catType : Lean.Expr := mkConst catName
  return .app catType annType
termination_by c
decreasing_by
  cases c
  decreasing_tactic

/--
`getCategoryTerm cat annType` returns the Lean term for a non-declared category.
-/
def getCategoryTerm (cat : QualifiedIdent) (annType : Term) : GenM Term := do
  let catIdent ← currScopedIdent (← getCategoryScopedName cat)
  return mkApp catIdent #[annType]

/-- Return identifier for operator with given name to suport category. -/
def getCategoryOpIdent (cat : QualifiedIdent) (name : Name) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ name

/--
`ppCat annType c unwrap` returns the Lean type of the `c` with the given
`unwrap` flag and annotation type `annType`.
-/
partial def mkCatTerm (annType : Term) (c : SyntaxCat) (wrap : Bool := true) : GenM Term := do
  let args ← c.args.mapM (mkCatTerm annType)
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
    let msg := m!"Command elaboration reported messages:\nCommands:\n"
    let msg := commands.foldl (init := msg) fun msg cmd => m!"{msg}  {cmd}\n"
    let msg := m!"{msg}Kind: {m.kind}\n"
    let msg := m!"{msg}Message: {←m.data.format}"
    logError msg

abbrev BracketedBinder := TSyntax ``Lean.Parser.Term.bracketedBinder

def explicitBinder (name : String) (typeStx : Term)
    : CommandElabM BracketedBinder := do
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
        explicitBinder arg.name (← mkCatTerm annType arg.cat (wrap := arg.wrap))
  `(ctor| | $ctorId:ident $ann:bracketedBinder* $binders:bracketedBinder*)

def mkInductive (cat : QualifiedIdent) (ctors : Array DefaultCtor) : GenM Command := do
  assert! cat ∉ declaredCategories
  let ident ← currScopedIdent (← getCategoryScopedName cat)
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

def toAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `toAst

def ofAstIdentM (cat : QualifiedIdent) : GenM Ident := do
  currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst

def mkAnnWithTerm (argCtor : Name) (annTerm v : Term) : Term :=
  mkApp (mkCIdent argCtor) #[mkCApp ``Ann.ann #[annTerm], v]

def annToAst' (argCtor : Name) (term : Term) (wrap : Bool) : Term :=
  if wrap then
    mkAnnWithTerm argCtor term (mkCApp ``Ann.val #[term])
  else
    mkApp (mkCIdent argCtor) #[mkCApp ``default #[], term]

partial def annArg (c : SyntaxCat) (wrap : Bool) : GenM Ident := do
  let cat := c.name
  if cat ∈ polymorphicBuiltinCategories then
    assert! c.args.size == 1
    return mkIdentFrom (←read).src ``Ann.ann
  assert! c.args.size == 0
  if cat ∈ declaredCategories then
    assert! wrap
    return mkIdentFrom (←read).src ``Ann.ann
  getCategoryOpIdent cat `ann

partial def toAstApplyArg (vn : Name) (cat : SyntaxCat) (wrap : Bool := true) :
      GenM Term := do
  let v := mkIdentFrom (←read).src vn
  match cat.name with
  | q`Init.Num =>
    return annToAst' ``ArgF.num v (wrap := wrap)
  | q`Init.Bool => do
    return mkCApp ``ArgF.op #[annToAst' ``OperationF.ofBool v (wrap := wrap)]
  | q`Init.Ident =>
    return annToAst' ``ArgF.ident v (wrap := wrap)
  | q`Init.Str =>
    return annToAst' ``ArgF.strlit v (wrap := wrap)
  | q`Init.Decimal =>
    return annToAst' ``ArgF.decimal v (wrap := wrap)
  | q`Init.ByteArray =>
    return annToAst' ``ArgF.bytes v (wrap := wrap)
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

abbrev MatchAlt := TSyntax ``Lean.Parser.Term.matchAlt

def toAstExprMatch (op : DefaultCtor) (annT : Term) (args : Array CatOpArg) (names : Vector Name args.size) : GenM Term := do
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
    let e ← toAstApplyArg nm d.cat (wrap := d.wrap)
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
      let d : CatOpArg := op.argDecls[0]
      let annF : Ident ← annArg d.cat (wrap := d.wrap)
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
            toAstApplyArg nm d.cat (wrap := d.wrap)
          pure <| mkCApp ``OperationF.mk #[annT, quote mName, ← arrayLit argTerms]
  `(matchAltExpr| | $pat => $rhs)

def genToAst (cat : QualifiedIdent) (ops : Array DefaultCtor) : GenM Command := do
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  let astType : Term := categoryToAstTypeIdent cat annType
  let cases : Array MatchAlt ← ops.mapM (toAstMatch cat)
  let toAst ← toAstIdentM cat
  trace[Strata.generator] "Generating {toAst}"
  let src := (←read).src
  let v ← genFreshLeanName "v"
  `(partial def $toAst {$annType : Type} [Inhabited $annType] ($(mkCanIdent src v) : $catTerm) : $astType :=
      match $(mkIdentFrom src v):ident with $cases:matchAlt*)

def addAnn (act : Name) (e : Term) (wrap : Bool) : Term :=
    let t := mkApp (mkCIdent act) #[e]
    if wrap then
      mkCApp ``Functor.map #[mkCApp ``Ann.mk #[mkCApp ``ArgF.ann #[e]], t]
    else
      t

partial def getOfIdentArg (varName : String) (cat : SyntaxCat) (e : Term) (wrap : Bool := true) : GenM Term := do
  match cat.name with
  | q`Init.Num =>
    return addAnn ``OfAstM.ofNumM e (wrap := wrap)
  | q`Init.Ident =>
    return addAnn ``OfAstM.ofIdentM e (wrap := wrap)
  | q`Init.Str =>
    return addAnn ``OfAstM.ofStrlitM e (wrap := wrap)
  | q`Init.Decimal =>
    return addAnn ``OfAstM.ofDecimalM e (wrap := wrap)
  | q`Init.ByteArray =>
    return addAnn ``OfAstM.ofBytesM e (wrap := wrap)
  | q`Init.Bool => do
    return addAnn ``Strata.Bool.ofAst e (wrap := wrap)
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

def ofAstArgs (argDecls : Array CatOpArg) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
  let argCount := argDecls.size
  let args ← Array.ofFnM (n := argCount) fun ⟨i, _isLt⟩  => do
    let arg := argDecls[i]
    let (vc, vi) ← genFreshIdentPair <| arg.name ++ "_bind"
    let av ← ``($argsVar[$(quote i)])
    let rhs ← getOfIdentArg arg.name arg.cat av (wrap := arg.wrap)
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

def ofAstTypeArgs (argDecls : Array CatOpArg) (argsVar : Ident) : GenM (Array Ident × Array (TSyntax ``doSeqItem)) := do
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
  `(do let .up p ← $checkExpr:term
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
def createNameIndexMap (cat : QualifiedIdent) (ops : Array DefaultCtor) :
      GenM (Std.HashMap QualifiedIdent Nat × Ident × Command) := do
  let nameIndexMap := ops.foldl (init := {}) fun map op =>
    match op.strataName with
    | none => map  -- Skip operators without a name
    | some name => map.insert name map.size  -- Assign the next available index
  let ofAstNameMap ←
        currScopedIdent <| (← getCategoryScopedName cat) ++ `ofAst.nameIndexMap
  let cmd ← `(def $ofAstNameMap : Std.HashMap Strata.QualifiedIdent Nat := Std.HashMap.ofList $(quote nameIndexMap.toList))
  pure (nameIndexMap, ofAstNameMap, cmd)

def mkOfAstDef (cat : QualifiedIdent) (ofAst : Ident) (v : Name) (rhs : Term) :
      GenM Command := do
  let src := (←read).src
  let annType := localIdent "α"
  let catTerm ← getCategoryTerm cat annType
  `(partial def $ofAst {$annType : Type} [Inhabited $annType] [Repr $annType] ($(mkCanIdent src v) : $(categoryToAstTypeIdent cat annType)) : OfAstM $catTerm := $rhs)

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
      Strata.OfAstM.matchTypeParamOrType $(mkIdentFrom src v) $catCtorIdent (fun tp => $exprCtorIdent <$> $typeOfAst tp)
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

def checkInhabited (cat : QualifiedIdent) (ops : Array DefaultCtor) :
      StateT InhabitedSet GenM Unit := do
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

/--
Given a category and an unwrap tag, this returns a Lean expression
which given a value in the category with the wrap parameter, returns
the annotation value.
-/
partial def annExpr (c : SyntaxCat) (wrap : Bool) (annType : Lean.Expr) : GenM Lean.Expr := do
  let cat := c.name
  if let some name := polymorphicBuiltinCategories[cat]? then
    assert! c.args.size == 1
    let baseType ← leanCatTypeExpr annType c.args[0]!
    let baseType := Lean.mkApp (.const name [0]) baseType
    return mkApp2 (.const ``Ann.ann []) baseType annType
  if let some name := declaredCategories[cat]? then
    assert! c.args.size == 0
    assert! wrap
    return mkApp2 (.const ``Ann.ann []) (.const name []) annType

  assert! c.args.size == 0
  match (←read).categoryNameMap[cat]? with
  | some catName =>
    return Lean.mkApp (.const ((← getCurrNamespace) ++ catName ++ `ann) []) annType
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
      let annFn ← annExpr d.cat (wrap := d.wrap) (.bvar (argc+1))
      pure (1, Lean.mkApp annFn (.bvar (argc - 1)))
  let inner : Lean.Expr ← Fin.foldrM argc (init := ann) fun i e => do
    let a := c.argDecls[i]
    let argType ← leanCatTypeExpr (.bvar (inner_off + i)) a.cat (wrap := a.wrap)
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

def gen (categories : Array (Array (QualifiedIdent × Array DefaultCtor))) : GenM Unit := do
  let mut inhabitedCats : InhabitedSet :=
    Std.HashSet.ofArray
      declaredCategories.keysArray
  for allCtors in categories do
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

def runGenM {α} (src : Lean.Syntax)
        (categoryNameMap : Std.HashMap QualifiedIdent Lean.Name)
        (m : GenM α)
        : CommandElabM α := do
  let ctx : GenContext := {
    src := src
    categoryNameMap
  }
  m ctx

/--
`#strata_gen ident` generates an AST for the dialect `ident`.

This includes functions for converting from the standard AST to the generated AST
and back.
-/
syntax (name := strataGenCmd) "#strata_gen" ident : command -- declare the syntax

/--
Create a map from names of categories to their Lean name.
-/
def mkCatNameMap (pref : String) (cm : CatIndexMap) (em : PartialNodeMapping cm.size)
  : Std.HashMap QualifiedIdent Name :=
  -- Get number
  let catNameCounts : Std.HashMap String Nat :=
    em.targetSize.fold (init := {}) fun tgtNode tgtlt m  =>
      let i := cm.idents[em.sourceNode tgtNode]
      m.alter i.name (fun v => some (v.getD 0 + 1))
  let init := .emptyWithCapacity em.targetSize
  em.targetSize.fold (init := init) fun tgtNode tgtlt m =>
    let i := cm.idents[em.sourceNode tgtNode]
    let name :=
          if catNameCounts.getD i.name 0 > 1 then
            .mkSimple s!"{i.dialect}_{i.name}"
          else if i.name ∈ reservedCatNames then
            .mkSimple s!"{pref}{i.name}"
          else
            .mkSimple i.name
    m.insert i name

@[command_elab strataGenCmd]
public def genAstImpl : CommandElab := fun stx =>
  match stx with
  | `(#strata_gen $dialectStx) => do
    let .str .anonymous dialectName := dialectStx.getId
      | throwErrorAt dialectStx s!"Expected dialect name"
    let loader := dialectExt.getState (← getEnv) |>.loaded
    let depDialectNames := computeImportedDialects loader.dialects dialectName
    let usedDialects ← depDialectNames.mapM fun nm =>
          match loader.dialects[nm]? with
          | some d => pure d
          | none => panic! s!"Missing dialect {nm}"
    let some d := loader.dialects[dialectName]?
      | throwErrorAt dialectStx "Missing dialect"
    let (cm, errs) := mkCatIndexMap usedDialects
    if errs.size > 0 then
      for e in errs do
        logError e
      return
    let errors := checkDialect cm d
    if errors.size > 0 then
      for e in errs do
        logError e
      return

    let g := indexMapToGraph cm
    -- Get all categories that are introduced or modified by d
    let relevantCategories := newCategories cm d
    -- Compute the closure of all categories needed for relevant categories.
    let usedSet := OutGraph.preimage_closure g relevantCategories
    let exprHasEta := false -- FIXME

--    let count : Nat := usedSet.foldl (b := 0) fun c e => if e then c + 1 else c


    let em : Graph.PartialNodeMapping cm.size := .fromVector usedSet
    let g := g.projection em.embedFn

    let mutual_indices : Array (Array (OutGraph.Node em.targetSize)) := OutGraph.tarjan g
    let mutual_groups := mutual_indices.map fun a => a.map fun j =>
          ctors exprHasEta cm (em.sourceNode j.val)

    let categoryNameMap := mkCatNameMap dialectName cm em
    runGenM stx categoryNameMap (gen mutual_groups)
  | _ =>
    throwUnsupportedSyntax

end Strata

end
