/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.HasVars
public import Strata.DL.Imperative.CFGDominators
public import Std.Data.TreeMap

/-! # Passification and WP/SP verification-condition generation for acyclic CFGs

Passification, as in Barnett & Leino, "Weakest-Precondition of Unstructured
Programs" (PASTE 2005), and the weakest-precondition (WP) and
strongest-postcondition (SP) verification conditions of Grigore, Charles,
Fairmichael & Kiniry, "Strongest Postcondition of Unstructured Programs" (FTfJP
2009), over the Imperative dialect's commands `Cmd P` and nondeterministic CFGs.
Expressions are built through the `PureExpr` typeclasses (`HasBoolOps`,
`HasIntOps`, `HasFvar`, `HasSubstFvar`, …), so this applies to any expression
language that instantiates them.

The input is an acyclic CFG (loops are cut beforehand) of nondeterministic
blocks: `goto ls` chooses among the successors `ls`, and `goto []` returns.

1. *Passification* (`passify`): critical edges are split, then every write gets
   a fresh incarnation `x@n` (`x := e` becomes `assume x@n == e`, a havoc
   becomes an unconstrained incarnation), reads refer to the current
   incarnations, and at a join each predecessor is extended with equalities that
   bring its incarnations up to the join's.
2. *Verification conditions* (`defObligations`): one obligation per assertion
   and per cover, in definitional form (every block predicate is a named
   definition), so the result is linear in the CFG under SP.

The whole-program VCs of the paper (`vc`, with `vcWp` and `vcSp`) are kept as
the reference formulation that tests compare against. -/

namespace Imperative
namespace PassiveVCGen

public section

open Std (ToFormat Format format)

variable {P : PureExpr}

/-! ## Program shape -/

/-- A passification block: a nondeterministic basic block over `Cmd P`. -/
abbrev PBlock (P : PureExpr) := NondetBlock String (Cmd P) P

/-- A passification CFG: `String`-labelled nondeterministic basic blocks, with
    unique labels (`defObligations` rejects a repeated one). -/
abbrev PCFG (P : PureExpr) := CFG String (PBlock P)

/-- Successor labels of a block (`[]` denotes return). -/
def PBlock.succs (b : PBlock P) : List String :=
  b.transfer.targets

/-- Build a block from body commands and an explicit successor list. -/
def mkBlock (cmds : List (Cmd P)) (succs : List String)
    (md : MetaData P := .empty) : PBlock P :=
  { cmds := cmds, transfer := .goto succs md }

/-! ## Graph structure -/

/-- Each label ↦ its block. -/
def PCFG.blockMap (p : PCFG P) : Std.HashMap String (PBlock P) :=
  p.blocks.foldl (fun m (l, b) => m.insert l b) {}

/-- Each label ↦ its successors (`CFG.succMapWith`). -/
def PCFG.succMap (p : PCFG P) : Std.HashMap String (List String) :=
  CFG.succMapWith PBlock.succs p.blocks

/-- Each label ↦ its predecessors, once per edge; every label is a key
    (`CFG.predMapWith`). -/
def PCFG.predMap (p : PCFG P) : Std.HashMap String (List String) :=
  CFG.predMapWith PBlock.succs p.blocks

/-- A label that two blocks share, if any. -/
def PCFG.repeatedLabel? (p : PCFG P) : Option String := Id.run do
  let mut seen : Std.HashSet String := {}
  for (l, _) in p.blocks do
    if seen.contains l then return some l
    seen := seen.insert l
  return none

/-- `ls` without repeats, keeping first occurrences, in linear time (`eraseDups`
    is quadratic, which a join with many predecessors would feel). -/
def dedupLabels (ls : List String) : List String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for l in ls do
    if !seen.contains l then
      seen := seen.insert l
      out := out.push l
  return out.toList

/-- The blocks reachable from the entry, in topological order (entry first) when
    the CFG is acyclic: a reverse postorder (`CFG.reversePostorderFrom`). -/
def topoOrder (p : PCFG P) : List String :=
  CFG.reversePostorderFrom p.succMap [p.entry]

/-- The labels of the blocks on a cycle reachable from the entry. -/
def reachableCycleLabels (p : PCFG P) : List String :=
  let cyclic := CFG.cycleLabelsWith p.succMap [p.entry]
  (p.blocks.map (·.1)).filter cyclic.contains

/-- Split every critical edge: an edge from a block with several successors to a
    block with several predecessors gets an empty block of its own. Afterwards a
    join's predecessors each have a single successor, which passification
    relies on when it appends the join's equalities to them. -/
def splitCriticalEdges (p : PCFG P) : PCFG P := Id.run do
  let preds := p.predMap
  let mut taken : Std.HashSet String := Std.HashSet.ofList (p.blocks.map (·.1))
  let mut blocks : Array (String × PBlock P) := #[]
  for (l, b) in p.blocks do
    let succs := b.succs
    if succs.length ≤ 1 then
      blocks := blocks.push (l, b)
    else
      let mut newSuccs : Array String := #[]
      let mut extra : Array (String × PBlock P) := #[]
      for s in succs do
        if (preds.getD s []).length > 1 then
          let e := Strata.Name.freshName taken s!"$edge${l}${s}"
          taken := taken.insert e
          extra := extra.push (e, mkBlock [] [s])
          newSuccs := newSuccs.push e
        else
          newSuccs := newSuccs.push s
      let md := match b.transfer with | .goto _ md => md
      blocks := (blocks.push (l, { b with transfer := .goto newSuccs.toList md })) ++ extra
  return { p with blocks := blocks.toList }

/-! ## Incarnations

An incarnation map records the current incarnation of each variable written so
far; an unwritten variable is at incarnation 0 (a variable the body never
writes; one that is declared, such as a parameter under `bracketCfgSpec`, is written
by its declaration, so its value on entry is incarnation 1 or later). Maps are
keyed by the rendered identifier (`toString`), as incarnation names are
(`incarnate`), so identifiers that render alike are the same variable here.

The maps are persistent trees, so a block's map shares structure with its
predecessor's. Each also indexes its variables by incarnation (`byInc`), which
finds the variables written since a given point (`keysFrom`): incarnation
numbers only grow. -/

structure IncMap (P : PureExpr) where
  byVar : Std.TreeMap String (P.Ident × Nat) := ∅
  byInc : Std.TreeMap Nat String := ∅
  /-- The incarnation the `init` of each declared variable gave it, on this path. After a
      join, the smallest among the predecessors. -/
  declAt : Std.TreeMap String Nat := ∅

def incGetKey (m : IncMap P) (k : String) : Nat :=
  ((m.byVar.get? k).map (·.2)).getD 0

def incGet [ToString P.Ident] (m : IncMap P) (x : P.Ident) : Nat :=
  incGetKey m (toString x)

def incSet [ToString P.Ident] (m : IncMap P) (x : P.Ident) (n : Nat) : IncMap P :=
  let k := toString x
  let byInc := match m.byVar.get? k with
    | some (_, old) => m.byInc.erase old
    | none => m.byInc
  { m with byVar := m.byVar.insert k (x, n), byInc := byInc.insert n k }

/-- The keys of the variables at incarnation `c` or later, in increasing
    incarnation. -/
def keysFrom (m : IncMap P) (c : Nat) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := m.byInc.getEntryGE? c
  for _ in [0:m.byInc.size] do
    match cur with
    | none => break
    | some (n, k) =>
      out := out.push k
      cur := m.byInc.getEntryGT? n
  return out.toList

/-- How the generator names what it introduces: the incarnation `x{sep}n` of a variable
    `x` (`incarnate`), and the definitions `{defPrefix}{tag}_{k}` (`vcDefName`). The
    caller chooses them so that no name of its program, and no variable of the CFG,
    contains `sep` or `defPrefix` (`Naming.avoiding`). Then no introduced name is a name of
    the program; two incarnations are distinct (`n` is the digits after the last `sep`,
    `sep` being all `@`); and no incarnation is a definition (an occurrence of
    `defPrefix`, which has no `@` and no digit, would lie within `x`). -/
structure Naming where
  sep : String := "@"
  defPrefix : String := "$__vc"
  deriving Inhabited, Repr

/-- The defaults `@` and `$__vc`, each lengthened (`@@`, …; `$$__vc`, …) until none of
    `names` contains it. -/
def Naming.avoiding (names : List String) : Naming :=
  let occursIn := fun (pat s : String) => (s.splitOn pat).length > 1
  -- Longer than every name, a candidate occurs in none.
  let bound := names.foldl (fun n s => max n s.length) 0 + 1
  let pick := fun (base grow : String) => Id.run do
    let mut c := base
    for _ in [0:bound] do
      if names.any (occursIn c) then c := grow ++ c else break
    return c
  { sep := pick "@" "@", defPrefix := pick "$__vc" "$" }

/-- The passive variable name for the `n`-th incarnation of `x`, e.g. `x@3`. -/
def incarnate [ToString P.Ident] [HasIdent P] (nm : Naming) (x : P.Ident) (n : Nat) :
    P.Ident :=
  HasIdent.ident (P := P) (toString x ++ nm.sep ++ toString n)

/-! ## Variable types

Incarnations are fresh free variables, which a pass running after type checking
must annotate itself (`HasFvar.mkTypedFvar`). Each variable's type is the type of
its `init`; every incarnation of a variable gets that type. This needs one type
per variable name: the caller ensures that (Core lowers structured bodies with
unique declaration names, and its CFG type checker requires the declarations of
a local to agree). A variable with no `init` gets unannotated incarnations. -/

abbrev TyMap (P : PureExpr) := Std.HashMap String P.Ty

/-- The type of each variable, from the first `init` of it. -/
def collectTypes [ToString P.Ident] (p : PCFG P) : TyMap P :=
  p.blocks.foldl
    (fun acc (_, b) =>
      b.cmds.foldl
        (fun acc c =>
          match c with
          | .init x ty _ _ => acc.insertIfNew (toString x) ty
          | _              => acc)
        acc)
    {}

/-- The free variable for the `n`-th incarnation of `x`, annotated with `x`'s
    type when known. -/
def incFvar [ToString P.Ident] [HasIdent P] [HasFvar P]
    (nm : Naming) (tys : TyMap P) (x : P.Ident) (n : Nat) : P.Expr :=
  let xn := incarnate nm x n
  match tys.get? (toString x) with
  | some ty => HasFvar.mkTypedFvar (P := P) xn ty
  | none    => HasFvar.mkFvar (P := P) xn

/-- Rename every variable an expression reads to its current incarnation. -/
def renameExpr [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    (nm : Naming) (tys : TyMap P) (m : IncMap P) (e : P.Expr) : P.Expr :=
  let sm := (HasFvars.getFvars e).map (fun x => (x, incFvar nm tys x (incGet m x)))
  HasSubstFvar.substFvars e sm

/-! ## Passifying commands

A write `x := e` (`set` or `init` with a deterministic right-hand side) reads
`e` at the current incarnations, allocates a fresh incarnation `x@n` and becomes
`assume x@n == e`; a havoc (a nondeterministic right-hand side) allocates a fresh
incarnation and emits nothing. `assert`, `assume` and `cover` are renamed. The
incarnation counter is shared by all variables and starts at 1, so incarnation 0
is never allocated.

A write to a variable whose type satisfies the caller's `inline` test (Core
inlines function types, whose values an SMT solver cannot compare: a local
function, a copy of one, a conditional of two) emits nothing either: its
incarnation is *defined* as the right-hand side, and `passify` substitutes the
definition into every use. The right-hand side was renamed where the write
happens, so the definition captures the values the write sees. At a join, such a
variable is kept or reset (see below). -/

/-- What passifying commands produces besides the passive commands: the
    definitions of the incarnations that are inlined, in order. -/
abbrev Inlined (P : PureExpr) := Array (P.Ident × P.Expr)

def processWrite [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (nm : Naming) (tys : TyMap P) (inline : P.Ty → Bool) (counter : Nat) (m : IncMap P)
    (x : P.Ident)
    (rhs : ExprOrNondet P) (md : MetaData P) : (Nat × IncMap P × List (Cmd P) × Inlined P) :=
  match rhs with
  | .det e =>
      let e' := renameExpr nm tys m e
      if ((tys.get? (toString x)).map inline).getD false then
        (counter + 1, incSet m x counter, [], #[(incarnate nm x counter, e')])
      else
        (counter + 1, incSet m x counter,
          [ Cmd.assume "" (HasIntOps.eq (incFvar nm tys x counter) e') md ], #[])
  | .nondet => (counter + 1, incSet m x counter, [], #[])

/-- The label prefix of the metadata entries that name, at a check, the incarnation each
    variable is at: an entry `varAtPrefix ++ x` with value `.msg` the incarnation's
    name, so that a counterexample can be read in the program's variables. -/
def varAtPrefix : String := "passiveVarAt:"

/-- `md` with an entry per variable written so far (`m`), naming its current incarnation
    (`varAtPrefix`). -/
def withVarsAt [ToString P.Ident] [HasIdent P] (nm : Naming) (m : IncMap P)
    (md : MetaData P) : MetaData P :=
  m.byVar.foldl (init := md) fun md k (x, n) =>
    md.pushElem (.label s!"{varAtPrefix}{k}") (.msg (toString (incarnate (P := P) nm x n)))

def processCmd [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (nm : Naming) (tys : TyMap P) (inline : P.Ty → Bool) (counter : Nat) (m : IncMap P) :
    Cmd P → (Nat × IncMap P × List (Cmd P) × Inlined P)
  | .assert l e md =>
    (counter, m, [ Cmd.assert l (renameExpr nm tys m e) (withVarsAt nm m md) ], #[])
  | .assume l e md => (counter, m, [ Cmd.assume l (renameExpr nm tys m e) md ], #[])
  | .cover  l e md =>
    (counter, m, [ Cmd.cover  l (renameExpr nm tys m e) (withVarsAt nm m md) ], #[])
  | .init x _ty rhs md =>
    let (counter', m', cs, ds) := processWrite nm tys inline counter m x rhs md
    (counter', { m' with declAt := m'.declAt.insert (toString x) (incGet m' x) }, cs, ds)
  | .set  x rhs md     => processWrite nm tys inline counter m x rhs md

def processCmds [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (nm : Naming) (tys : TyMap P) (inline : P.Ty → Bool) (counter : Nat) (m : IncMap P)
    (cs : List (Cmd P)) : (Nat × IncMap P × List (Cmd P) × Inlined P) :=
  let (counter, m, out, defs) := cs.foldl (init := (counter, m, (#[] : Array (Cmd P)), #[]))
    fun (counter, m, out, defs) c =>
      let (counter, m, cs', ds) := processCmd nm tys inline counter m c
      (counter, m, out ++ cs'.toArray, defs ++ ds)
  (counter, m, out.toList, defs)

/-- Substitute the inlined definitions `sm` (by the `toString` of the incarnation)
    into `e`, for the variables `e` has among them only. -/
def substInlined [ToString P.Ident] [HasFvars P] [HasSubstFvar P]
    (sm : Std.HashMap String P.Expr) (e : P.Expr) : P.Expr :=
  let pairs := (HasFvars.getFvars e).filterMap fun x => (sm.get? (toString x)).map (x, ·)
  if pairs.isEmpty then e else HasSubstFvar.substFvars e pairs

/-- Substitute the inlined definitions into the expression of a passive command. -/
def Cmd.substInlined [ToString P.Ident] [HasFvars P] [HasSubstFvar P]
    (sm : Std.HashMap String P.Expr) : Cmd P → Cmd P
  | .assert l e md => .assert l (PassiveVCGen.substInlined sm e) md
  | .assume l e md => .assume l (PassiveVCGen.substInlined sm e) md
  | .cover  l e md => .cover  l (PassiveVCGen.substInlined sm e) md
  | c => c

/-! ## Passifying a CFG

Blocks are processed in topological order. A block with one predecessor starts
from that predecessor's exit map. At a join, a variable whose incarnation differs
between the predecessors takes the largest of them, and each predecessor at a
different incarnation gets `assume x@join == x@pred` appended. Once critical
edges are split, a join's predecessors have no other successor, so the
equalities constrain only the paths into the join.

A variable whose incarnation in some predecessor is inlined (its value is a
lambda: a local function, or any function-typed variable written a lambda) cannot
be reconciled by an equality: the incarnation is its definition, substituted into
its uses, not a variable to equate. (A function-typed variable with no inlined
incarnation on any predecessor, such as one havocked on every path, is a
variable on each, and is reconciled by equalities like any other.)
- If every predecessor inlines it and the definitions agree (`sameDef`), it keeps
  the largest incarnation, with no equalities.
- With `declaredBeforeUse`, if some predecessor does not have it at all, or every
  predecessor that has it declared it after the join's immediate dominator, no
  declaration of it dominates the join, nothing after the join reads it, and it
  keeps the largest incarnation. The flag asserts two things of the input: every
  read of a variable is dominated by an `init` of it, and no path runs two `init`s
  of one variable (`declAt` keeps the latest, so a variable declared before the
  dominator and again after it would otherwise look declared after it only). Core's
  CFG type checker establishes both (`checkDomScoped`; `checkInitsIncomparable`
  and `checkInitsNotReachable`), and a structured body has both by construction
  once sibling declarations are renamed apart (`uniquifyInits`).
- Otherwise it is at a fresh incarnation after the join, unconstrained, and the
  join block starts with `assume [joinResetLabel] true`. That is an
  over-approximation: a fact about the variable after the join says less than on
  each path, so an assertion may fail spuriously and a cover may be met
  spuriously. The mark lets a phase validate such a result (the pass reports it
  `unknown`). A fresh incarnation, rather than incarnation 0, keeps the variable
  apart from its value on entry and from the reset of every other join, and puts
  it above the bound below.

Only variables written since the join's immediate dominator can differ: every
path to a predecessor passes through it, and a write after it gets an
incarnation at least the counter's value when the dominator was done. So a join
looks only at its predecessors' variables from that incarnation on. The work, and
the equalities passification adds, are the sum over joins of the predecessors
times the variables written since the dominator: a write is looked at by every
join that encloses it, so the cost grows with branch nesting depth. -/

/-- The label of the assumption that starts a block where a variable is reset
    (see `passifyLabel`), so that a phase can validate results resting on it. -/
def joinResetLabel : String := "passiveVCJoinReset_"

/-- The state threaded through the blocks: the incarnation counter, each
    processed block's exit map, the counter after it, and its passive body, and
    the inlined definitions. -/
structure PState (P : PureExpr) where
  /-- The next incarnation to allocate. -/
  counter  : Nat
  /-- Each processed block's incarnation map at its end. -/
  exits    : Std.HashMap String (IncMap P)
  /-- The counter after each processed block (a join's `since` bound). -/
  counters : Std.HashMap String Nat
  /-- Each processed block's passive body, with the equalities appended to it. -/
  bodies   : Std.HashMap String (Array (Cmd P))
  /-- The inlined definitions, in order, and by the name of their incarnation. -/
  inlined  : Inlined P := #[]
  inlinedDefs : Std.HashMap String P.Expr := {}

/-- Passify one block (`label`), given the state of the blocks before it: take its
    entry map from its predecessors (joining several as described above, and
    appending the equalities to them), then rename its commands. `idom` is the
    immediate-dominator map, which bounds the variables a join looks at. -/
def passifyLabel [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (nm : Naming) (tys : TyMap P) (inline : P.Ty → Bool) (sameDef : P.Expr → P.Expr → Bool)
    (declaredBeforeUse : Bool)
    (blocks : Std.HashMap String (PBlock P))
    (preds : Std.HashMap String (List String)) (idom : Std.HashMap String String)
    (st : PState P) (label : String) : PState P :=
  let ps := (dedupLabels (preds.getD label [])).filter st.exits.contains
  let (entryMap, bodies, counter, marks) :
      IncMap P × Std.HashMap String (Array (Cmd P)) × Nat × Array (Cmd P) :=
    match ps with
    | [] => ({}, st.bodies, st.counter, #[])
    | [pl] => ((st.exits.get? pl).getD {}, st.bodies, st.counter, #[])
    | p0 :: _ =>
      let since := ((idom.get? label).bind st.counters.get?).getD 0
      let pexits := ps.map fun pl => (pl, (st.exits.get? pl).getD {})
      let keys := (Std.HashSet.ofList (pexits.flatMap fun (_, m) => keysFrom m since)).toArray
        |>.qsort (· < ·)
      -- The inlined definition of a variable's incarnation in a predecessor.
      let defOf := fun (m : IncMap P) (k : String) => match m.byVar.get? k with
        | some (x, n) => st.inlinedDefs.get? (toString (incarnate (P := P) nm x n))
        | none => none
      -- A variable inlined in some predecessor either agrees on all of them, or is reset.
      -- With `declaredBeforeUse`, a variable some predecessor does not have was
      -- declared on the other paths only: its declaration does not dominate the
      -- join, so nothing after the join reads it, and it needs no reset. Without
      -- it, such a variable may be one never written on that path, whose value
      -- there is its value on entry, so it is reset like any other.
      -- Likewise one declared after the immediate dominator on every path that has
      -- it: no declaration of it dominates the join (a block that does dominates the
      -- dominator or is it, and was done before `since`).
      let declaredBelow := fun (k : String) =>
        pexits.all fun (_, m) => !m.byVar.contains k || (m.declAt.get? k).any (· ≥ since)
      let isAgreed := fun (k : String) =>
        (declaredBeforeUse &&
          (!pexits.all (fun (_, m) => m.byVar.contains k) || declaredBelow k)) ||
        match (pexits.map fun (_, m) => defOf m k) with
        | some d :: rest => rest.all fun o => match o with | some d' => sameDef d d' | none => false
        | _ => false
      let isInl := fun (k : String) => pexits.any fun (_, m) => (defOf m k).isSome
      let (inl, plain) := keys.toList.partition isInl
      let (agreed, reset) := inl.partition isAgreed
      -- Each variable at its largest incarnation among the predecessors.
      let maxOf := fun (k : String) =>
        pexits.foldl (fun best (_, m) => match m.byVar.get? k, best with
          | some (x, n), some (_, _, n') => if n > n' then some (k, x, n) else best
          | some (x, n), none => some (k, x, n)
          | none, _ => best) none
      let joined : List (String × P.Ident × Nat) := plain.filterMap maxOf
      let kept : List (String × P.Ident × Nat) := agreed.filterMap maxOf
      let base := ((st.exits.get? p0).getD {})
      let base := (joined ++ kept).foldl (fun m (_, x, n) => incSet m x n) base
      -- Each variable written since the dominator keeps its earliest declaration.
      let base := keys.foldl (fun m k =>
        match pexits.filterMap (fun (_, pm) => pm.declAt.get? k) with
        | [] => m
        | d :: ds => { m with declAt := m.declAt.insert k (ds.foldl min d) }) base
      -- The identifier comes from any predecessor that has the variable.
      let (base, counter) := reset.foldl (fun (m, c) k =>
        match pexits.findSome? fun (_, pm) => (pm.byVar.get? k).map (·.1) with
        | some x => (incSet m x c, c + 1)
        | none => (m, c)) (base, st.counter)
      let bodies := pexits.foldl (fun bodies (pl, pexit) =>
          let syncs := joined.filterMap fun (k, x, n) =>
            let pe := incGetKey pexit k
            if n != pe then
              some (Cmd.assume "" (HasIntOps.eq (incFvar nm tys x n) (incFvar nm tys x pe)) .empty)
            else none
          bodies.insert pl ((bodies.getD pl #[]) ++ syncs.toArray))
        st.bodies
      let marks : Array (Cmd P) :=
        if reset.isEmpty then #[] else #[Cmd.assume joinResetLabel HasBool.tt .empty]
      (base, bodies, counter, marks)
  match blocks.get? label with
  | none   => { st with bodies := bodies, counter := counter }
  | some b =>
    let (counter', exitMap, body, defs) := processCmds nm tys inline counter entryMap b.cmds
    { counter  := counter'
      exits    := st.exits.insert label exitMap
      counters := st.counters.insert label counter'
      bodies   := bodies.insert label ((bodies.getD label #[]) ++ marks ++ body.toArray)
      inlined  := st.inlined ++ defs
      inlinedDefs := defs.foldl (fun m (v, e) => m.insert (toString v) e) st.inlinedDefs }

/-- What `passifyWith` returns: the passive CFG and the graph structure computed on the
    way, which `defObligations` reads again. -/
structure Passified (P : PureExpr) where
  /-- The passive CFG. -/
  cfg : PCFG P
  /-- Its blocks' labels, in topological order (the order of `cfg.blocks`). -/
  order : List String
  /-- The predecessors of each block, after edge splitting. Unreachable blocks may
      appear among them; they are in neither `order` nor `idom`. -/
  preds : Std.HashMap String (List String)
  /-- The immediate dominator of each block of `cfg`. -/
  idom : Std.HashMap String String

/-- `passifyWith` without its checks: on a CFG with a cycle or a repeated label
    the order is not topological and the result is wrong, so only `passifyWith`
    calls it. -/
private def passifyUnchecked [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P]
    [HasSubstFvar P] [HasBool P] [HasInt P] [HasIntOps P]
    (p : PCFG P) (inline : P.Ty → Bool) (sameDef : P.Expr → P.Expr → Bool)
    (declaredBeforeUse : Bool) (nm : Naming) : Passified P :=
  let p := splitCriticalEdges p
  let order := topoOrder p
  let tys := collectTypes p
  let blocks := p.blockMap
  let preds := p.predMap
  let idom := CFG.computeIdomsDag order preds p.entry
  let st := order.foldl (passifyLabel nm tys inline sameDef declaredBeforeUse blocks preds idom)
    { counter := 1, exits := {}, counters := {}, bodies := {} }
  -- Each definition refers only to earlier ones, so substituting them in order
  -- gives closed definitions.
  let sm : Std.HashMap String P.Expr :=
    st.inlined.foldl (fun sm (v, e) => sm.insert (toString v) (substInlined sm e)) {}
  let body := fun (l : String) =>
    let cs := (st.bodies.getD l #[]).toList
    if sm.isEmpty then cs else cs.map (Cmd.substInlined sm)
  { cfg := { entry := p.entry,
             blocks := order.filterMap fun l => (blocks.get? l).map fun b =>
               (l, { b with cmds := body l }) },
    order, preds, idom }

/-- `passify`, also returning the graph structure it computed, for a caller that
    needs it again (`defObligations`). Fails if two blocks share a label, or if a
    cycle is reachable from the entry: passification needs a topological order. -/
def passifyWith [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (p : PCFG P) (inline : P.Ty → Bool := fun _ => false)
    (sameDef : P.Expr → P.Expr → Bool := fun _ _ => false)
    (declaredBeforeUse : Bool := false) (naming : Naming := {}) :
    Except String (Passified P) := do
  if let some l := p.repeatedLabel? then
    throw s!"the control-flow graph has two blocks labelled '{l}'"
  let cyc := reachableCycleLabels p
  if !cyc.isEmpty then
    throw s!"the control-flow graph has a cycle reachable from the entry, through {cyc}; \
             cut its loops first (CFG loop elimination)"
  pure (passifyUnchecked p inline sameDef declaredBeforeUse naming)

/-- Passify an acyclic CFG with unique labels: split its critical edges, then
    passify its reachable blocks in topological order, inlining the writes whose
    variable's type satisfies `inline` (`sameDef` says two inlined definitions
    agree). The result has the reachable blocks only, in that order, each with its
    passive body and its transfer after edge splitting. `declaredBeforeUse` says that
    the language declares every variable before it is read, so that one missing from
    some path into a join was declared on the other paths only (see `passifyLabel`). -/
def passify [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasInt P] [HasIntOps P]
    (p : PCFG P) (inline : P.Ty → Bool := fun _ => false)
    (sameDef : P.Expr → P.Expr → Bool := fun _ _ => false)
    (declaredBeforeUse : Bool := false) (naming : Naming := {}) : Except String (PCFG P) :=
  (·.cfg) <$> passifyWith p inline sameDef declaredBeforeUse naming

/-! ## Predicate transformers on passive commands

After passification a body has only `assert`, `assume` and `cover` (writes have
become `assume`s or vanished). The transformers of the paper (its equations
4–6):

    wp (assume ψ) β = ψ ⇒ β        sp (assume ψ) α = α ∧ ψ
    wp (assert ψ) β = ψ ∧ β        sp (assert ψ) α = α ∧ ψ

A `cover` constrains neither. -/

def wpCmd [HasBoolOps P] : Cmd P → P.Expr → P.Expr
  | .assert _ e _, β => HasBoolOps.and e β
  | .assume _ e _, β => HasBoolOps.imp e β
  | _,             β => β

/-- Weakest precondition of a command list for postcondition `β`. -/
def wp [HasBoolOps P] : List (Cmd P) → P.Expr → P.Expr
  | [],      β => β
  | c :: cs, β => wpCmd c (wp cs β)

def spCmd [HasBoolOps P] (α : P.Expr) : Cmd P → P.Expr
  | .assert _ e _ => HasBoolOps.and α e
  | .assume _ e _ => HasBoolOps.and α e
  | _             => α

/-- Strongest postcondition of a command list for precondition `α`. -/
def sp [HasBoolOps P] (α : P.Expr) : List (Cmd P) → P.Expr
  | []      => α
  | c :: cs => sp (spCmd α c) cs

def conjoin [HasBool P] [HasBoolOps P] : List P.Expr → P.Expr
  | []      => HasBool.tt
  | [e]     => e
  | e :: es => HasBoolOps.and e (conjoin es)

def disjoin [HasBool P] [HasBoolOps P] : List P.Expr → P.Expr
  | []      => HasBool.ff
  | [e]     => e
  | e :: es => HasBoolOps.or e (disjoin es)

/-! ## Whole-program verification conditions

The VCs of the paper's §4, for a passive acyclic CFG, one formula per program:

* WP (eqns 7–8): in reverse topological order, `βₘ = ⋀_{m→n} αₙ` and
  `αₘ = wp (cmds m) βₘ`; the VC is the entry's `α`.
* SP (eqns 9–11): in topological order, `αₙ = ⊤` at the entry and `⋁_{m→n} βₘ`
  elsewhere, `βₙ = sp αₙ (cmds n)`; the VC is `⋀ (α' ⇒ ψ)` over the assertions,
  with `α'` the SP of the commands before `assert ψ` in its block.

Each block predicate is computed once, but the result is a single expression
with no names: a consumer that walks it as a tree sees each predecessor's
predicate once per successor. Verification uses `defObligations` instead. -/

/-- Which calculus to use. -/
inductive VcMethod where
  /-- Weakest precondition. -/
  | wp
  /-- Strongest postcondition. -/
  | sp
  deriving Repr, DecidableEq, Inhabited

/-- `wp`: the entry's weakest precondition. -/
def vcWp [HasBool P] [HasBoolOps P] (p : PCFG P) : P.Expr := Id.run do
  let blocks := p.blockMap
  let mut pre : Std.HashMap String P.Expr := {}
  for label in (topoOrder p).reverse do
    let b := blocks.get? label
    let β := conjoin (((b.map (·.succs)).getD []).filterMap pre.get?)
    pre := pre.insert label (wp ((b.map (·.cmds)).getD []) β)
  return (pre.get? p.entry).getD HasBool.tt

/-- The obligations `α' ⇒ ψ` of a block's assertions, `α'` threaded from `α`. -/
def assertObligations [HasBoolOps P] (α : P.Expr) : List (Cmd P) → List P.Expr
  | []      => []
  | c :: cs =>
    let rest := assertObligations (spCmd α c) cs
    match c with
    | .assert _ ψ _ => HasBoolOps.imp α ψ :: rest
    | _             => rest

/-- `sp`: the conjunction of the assertions' obligations. -/
def vcSp [HasBool P] [HasBoolOps P] (p : PCFG P) : P.Expr := Id.run do
  let blocks := p.blockMap
  let preds := p.predMap
  let mut post : Std.HashMap String P.Expr := {}
  let mut obligations : Array P.Expr := #[]
  for label in topoOrder p do
    let cmds := ((blocks.get? label).map (·.cmds)).getD []
    let α := if label == p.entry then HasBool.tt
      else disjoin ((dedupLabels (preds.getD label [])).filterMap post.get?)
    post := post.insert label (sp α cmds)
    obligations := obligations ++ (assertObligations α cmds).toArray
  return conjoin obligations.toList

/-- The VC of a passive CFG in the chosen calculus. -/
def vcOf [HasBool P] [HasBoolOps P] (method : VcMethod) (p : PCFG P) : P.Expr :=
  match method with
  | .wp => vcWp p
  | .sp => vcSp p

/-- Passify an acyclic CFG, then give its VC in the chosen calculus. Fails as
    `passify` does. -/
def vc [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P]
    (method : VcMethod) (p : PCFG P) (naming : Naming := {}) : Except String P.Expr :=
  vcOf method <$> passify p (naming := naming)

/-! ## Per-obligation verification conditions in definitional form

`defObligations` gives one obligation per `assert` and per `cover` of the CFG.
Every assertion is checked on its own: the other assertions are neither assumed
nor checked in its obligation, so a precondition below is exactly the condition
of reaching a command.

Every block predicate is a named Boolean definition (`DefVC.defs`) that refers to
its neighbours' by name, so the size of the result is linear in the passive CFG
under SP (a formula walked as a tree does not grow at joins):

* per reachable block `n`, `A_n := ⋁ R_m` over the predecessors `m`, with `R_m`
  the precondition at the end of `m` (`⊤` at the entry);
* through a block, each `assume e` defines a new precondition `R := R_prev ∧ e`.

An obligation also has *path facts*: the conjunction of the assumptions that hold
on every path to its command (those of the blocks that dominate its block, and
those before it in its block), defined by a chain `F := F_prev ∧ e` that starts at
each block from the facts at the end of its immediate dominator. They follow from
the precondition, so stating them changes no verdict; a consumer states them as
top-level hypotheses, where a solver uses them without first splitting the
precondition's disjunctions.

Under WP an assertion's goal is the weakest precondition of the entry when only
that assertion is checked: per target, a definition `W_n` for each block that
can reach the target's block, `W_n := wp' cmdsₙ (⋀ W_s)` over the successors `s`
that also can, where `wp'` keeps only the assumptions (the other assertions are
skipped); the target's block contributes the WP of the commands before the
target, ending in its condition. That is one definition per (target, ancestor).
A block that cannot reach the target contributes `⊤` and is left out. These
definitions belong to the target's obligation alone (`goalDefs`), so a consumer
can keep each obligation's query free of the other targets' definitions. In passive
form, a state satisfying the precondition but not the goal exists iff one not
satisfying the goal does, so the assertion holds iff `pre ⇒ goal` is valid.

An `assert` or `cover` in a block not reachable from the entry has precondition
`⊥`: the assertion holds and the cover is not met. -/

/-- One obligation: the command's label and metadata, whether it is a cover
    (checked for satisfiability) or an assertion (checked for validity), its path
    facts, precondition and goal (the assertion's or cover's condition, or under
    WP the target's WP formula), the definitions only its goal uses (in
    dependency order, after the shared ones), and the keys (`labelKey`) of the
    labels of the `assume`s on its paths. -/
structure DefObligation (P : PureExpr) where
  label : String
  md : MetaData P
  isCover : Bool
  facts : P.Expr
  pre : P.Expr
  goal : P.Expr
  goalDefs : List (P.Ident × P.Expr) := []
  assumeLabels : List String

/-- The definitions all obligations share, in dependency order (each refers only
    to earlier names), and the obligations in program order: blocks as listed in
    the input CFG, commands in block order. -/
structure DefVC (P : PureExpr) where
  defs : List (P.Ident × P.Expr)
  obligations : List (DefObligation P)

/-- A definition's name, under the prefix of `nm`, so it cannot collide with a name of
    the program or an incarnation (see `Naming`). -/
def vcDefName [HasIdent P] (nm : Naming) (tag : String) (k : Nat) : P.Ident :=
  HasIdent.ident (P := P) s!"{nm.defPrefix}{tag}_{k}"

/-- The weakest precondition of a block for postcondition `β` with every
    assertion skipped. -/
def wpAssumes [HasBoolOps P] : List (Cmd P) → P.Expr → P.Expr
  | [],                    β => β
  | .assume _ e _ :: cs,   β => HasBoolOps.imp e (wpAssumes cs β)
  | _ :: cs,               β => wpAssumes cs β

/-- The weakest precondition of a block when only its `idx`-th assertion is
    checked: its assumptions before that assertion, then its condition. -/
def wpToTarget [HasBool P] [HasBoolOps P] (idx : Nat) : List (Cmd P) → Nat → P.Expr
  | [],                    _   => HasBool.tt
  | .assume _ e _ :: cs,   cur => HasBoolOps.imp e (wpToTarget idx cs cur)
  | .assert _ ψ _ :: cs,   cur => if cur == idx then ψ else wpToTarget idx cs (cur + 1)
  | _ :: cs,               cur => wpToTarget idx cs cur

/-- The blocks that can reach `target` (target included), by a backward search
    over `preds`. -/
def ancestorsOf (preds : Std.HashMap String (List String)) (target : String) :
    Std.HashSet String :=
  CFG.reachableSetFromSuccsWith preds (preds.size + 1) target |>.insert target

/-- The definitional obligations of an acyclic CFG, after passifying it (see the
    section note). Fails if two blocks share a label, or if a cycle is reachable
    from the entry.

    Each obligation records `labelKey l` for each label `l` of an `assume` on its
    paths, each key once, and none for an empty key: a caller that needs only some
    of what a label says (such as its prefix) keeps the sets small by mapping many
    labels to one key, or to none. `inline` says which writes are inlined,
    `sameDef` which two inlined definitions agree, and `declaredBeforeUse` whether the
    language declares a variable before reading it (see `passify`). -/
def defObligations [ToString P.Ident] [HasIdent P] [HasFvar P] [HasFvars P] [HasSubstFvar P]
    [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P]
    (method : VcMethod) (p : PCFG P) (labelKey : String → String := id)
    (inline : P.Ty → Bool := fun _ => false)
    (sameDef : P.Expr → P.Expr → Bool := fun _ _ => false)
    (declaredBeforeUse : Bool := false) (naming : Naming := {}) :
    Except String (DefVC P) := do
  -- The graph structure `passify` computed: `q`'s blocks are the reachable blocks of
  -- the edge-split graph, with its edges.
  let pq ← passifyWith p inline sameDef declaredBeforeUse naming
  let q := pq.cfg
  let qBlocks := q.blockMap
  let qPreds := pq.preds
  let order := pq.order
  let idom := pq.idom
  let boolVar := fun (x : P.Ident) => HasFvar.mkTypedFvar (P := P) x HasBool.boolTy
  let mut defs : Array (P.Ident × P.Expr) := #[]
  let mut k := 0
  -- Per block of `q`: its precondition and facts at the end, and the labels of the
  -- assumes on paths to its end.
  let mut preEnd : Std.HashMap String P.Expr := {}
  let mut factsEnd : Std.HashMap String P.Expr := {}
  let mut labelsEnd : Std.HashMap String (Std.HashSet String) := {}
  -- Per (passive) assert or cover, keyed by block and position among the block's
  -- asserts and covers: its facts, precondition, and assume labels.
  let mut atCmd : Std.HashMap (String × Nat) (P.Expr × P.Expr × List String) := {}
  for label in order do
    let ps := dedupLabels (qPreds.getD label [])
    let a := if label == q.entry then HasBool.tt else disjoin (ps.filterMap preEnd.get?)
    let aName := vcDefName (P := P) naming "A" k
    k := k + 1
    defs := defs.push (aName, a)
    let mut pre := boolVar aName
    let mut facts : P.Expr :=
      if label == q.entry then HasBool.tt
      else (factsEnd.get? (idom.getD label q.entry)).getD HasBool.tt
    let mut labels : Std.HashSet String :=
      ps.foldl (fun acc m => acc.union ((labelsEnd.get? m).getD {})) {}
    let mut i := 0
    for c in ((qBlocks.get? label).map (·.cmds)).getD [] do
      match c with
      | .assume l e _ =>
        let rName := vcDefName (P := P) naming "R" k
        let fName := vcDefName (P := P) naming "F" (k + 1)
        k := k + 2
        defs := defs.push (rName, HasBoolOps.and pre e)
        defs := defs.push (fName, HasBoolOps.and facts e)
        pre := boolVar rName
        facts := boolVar fName
        let key := labelKey l
        if !key.isEmpty then labels := labels.insert key
      | .assert .. | .cover .. =>
        let ls := labels.toList.toArray.qsort (· < ·) |>.toList
        atCmd := atCmd.insert (label, i) (facts, pre, ls)
        i := i + 1
      | _ => pure ()
    preEnd := preEnd.insert label pre
    factsEnd := factsEnd.insert label facts
    labelsEnd := labelsEnd.insert label labels
  -- Under WP, the goal of each assertion and the definitions it uses, keyed like
  -- `atCmd`.
  let mut wpGoal : Std.HashMap (String × Nat) (P.Expr × List (P.Ident × P.Expr)) := {}
  if method == .wp then
    let revOrder := order.reverse
    for tgt in order do
      let tgtCmds := ((qBlocks.get? tgt).map (·.cmds)).getD []
      if !tgtCmds.any (fun c => match c with | .assert .. => true | _ => false) then
        continue
      -- The blocks that can reach `tgt`, in reverse topological order.
      let anc := ancestorsOf qPreds tgt
      let ancOrder := revOrder.filter anc.contains
      let mut i := 0
      let mut assertIdx := 0
      for c in tgtCmds do
        match c with
        | .assert .. =>
          let mut w : Std.HashMap String P.Expr := {}
          let mut wDefs : Array (P.Ident × P.Expr) := #[]
          for l in ancOrder do
            let wl :=
              if l == tgt then wpToTarget assertIdx tgtCmds 0
              else
                let b := qBlocks.get? l
                let succs := (dedupLabels ((b.map (·.succs)).getD [])).filter anc.contains
                wpAssumes ((b.map (·.cmds)).getD []) (conjoin (succs.filterMap w.get?))
            let wName := vcDefName (P := P) naming "W" k
            k := k + 1
            wDefs := wDefs.push (wName, wl)
            w := w.insert l (boolVar wName)
          wpGoal := wpGoal.insert (tgt, i) ((w.get? q.entry).getD HasBool.tt, wDefs.toList)
          i := i + 1
          assertIdx := assertIdx + 1
        | .cover .. => i := i + 1
        | _ => pure ()
  -- The obligations, in the input's block order. A block of `p` that passification
  -- kept is found in `q` under its label (critical-edge splitting only adds blocks).
  let mut obs : Array (DefObligation P) := #[]
  for (label, b) in p.blocks do
    match qBlocks.get? label with
    | some qb =>
      let mut i := 0
      for c in qb.cmds do
        match c with
        | .assert l ψ md | .cover l ψ md =>
          let isCover := match c with | .cover .. => true | _ => false
          -- Every command of a reachable block was recorded above; a miss would give a
          -- cover a precondition of `⊤`, so it is an error rather than a default.
          let some (facts, pre, ls) := atCmd.get? (label, i)
            | throw s!"internal error: no precondition recorded for '{l}' in block '{label}'"
          let (goal, goalDefs) :=
            if isCover then (ψ, []) else (wpGoal.get? (label, i)).getD (ψ, [])
          obs := obs.push { label := l, md, isCover, facts, pre, goal, goalDefs,
                            assumeLabels := ls }
          i := i + 1
        | _ => pure ()
    | none =>
      -- Not reachable from the entry.
      for c in b.cmds do
        match c with
        | .assert l _ md =>
          obs := obs.push { label := l, md, isCover := false, facts := HasBool.tt,
                            pre := HasBool.ff, goal := HasBool.tt, assumeLabels := [] }
        | .cover l _ md =>
          obs := obs.push { label := l, md, isCover := true, facts := HasBool.tt,
                            pre := HasBool.ff, goal := HasBool.tt, assumeLabels := [] }
        | _ => pure ()
  return { defs := defs.toList, obligations := obs.toList }

end -- public section
end PassiveVCGen
end Imperative
