/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.CoreTransform

/-! # Per-goal irrelevant-axiom filtering for Strata Core verification

This module provides a two-step API designed for use inside a verification loop:

1. `Cache.build` precomputes, once per program, the function call graph and the
   function-to-immediate-axioms map, or with `directed` a `DirectedIndex`.
2. `getIrrelevantAxioms` uses that cached data to answer per-goal relevance
   queries efficiently.

This avoids rebuilding the call graph and axiom map on every proof obligation,
which would be expensive for programs with many goals.

`IrrelevantAxiomsMode` (`Options.lean`) is read by the verifier, not by this
pass.
-/

namespace Core

public section

namespace IrrelevantAxioms

/-! ## Goal-directed relevance (`IrrelevantAxiomsMode.Directed`)

Keeps the axioms a goal reaches through constants (functions without
arguments). With the datatype constructors `Box` and `Tag` and

  axiom x == Box(y)
  axiom y == Tag(true)
  axiom z == Box(w)

a goal about `x` keeps the first axiom, which reaches `y` and so keeps the
second, and drops the third. A kept axiom reaches every function it mentions.

An equality is followed from the side it defines, usually the left, so front
ends must write the defined term on the left; nothing checks this.
`n1 == n2 + 1` is kept for a goal about `n1` and dropped for one that reaches
only `n2`. Written as `n2 + 1 == n1`, it is dropped for a goal about `n1`,
which can turn a pass into an unknown but never a failure into a pass.

A fact about an uninterpreted function `f`, such as `f(x, 0) == true` or
`f(x) == c`, is kept when the goal reaches one of its uninterpreted functions
and one of its constants. `c == f(x)` is also a definition of `c`,
and `f(x) == c + 1` is also followed from `c`. An axiom that is a quantifier,
such as `forall k :: f(k) >= c`, is kept once the goal reaches `f`. Axioms
without constants are always kept. -/

/-- `m` with `i` appended to the entry for `k`. -/
private def pushAt (m : Std.HashMap String (Array Nat)) (k : String) (i : Nat) :
    Std.HashMap String (Array Nat) :=
  m.alter k (fun old => some ((old.getD #[]).push i))

/-- The role a user function plays in goal-directed relevance. -/
inductive SymKind where
  | constant       -- No arguments
  | defined        -- Arguments and a body
  | uninterpreted  -- Arguments and no body
  deriving BEq, Inhabited

/-- Per-axiom data for goal-directed relevance. -/
structure DirectedAxiom where
  name : String
  /-- User functions reached when the axiom is kept. -/
  spread : Array String
  /-- For a fact about uninterpreted functions, the ones it mentions. -/
  uninterpreted : Array String
  deriving Inhabited

/-- Precomputed per-program index for goal-directed relevance. -/
structure DirectedIndex where
  kinds : Std.HashMap String SymKind
  axioms : Array DirectedAxiom
  /-- Positions in `axioms` of the axioms that reaching each constant
      keeps. -/
  byConst : Std.HashMap String (Array Nat)
  /-- Positions of the facts about uninterpreted functions that mention each
      constant. -/
  factsByConst : Std.HashMap String (Array Nat)
  /-- Positions of the quantified axioms that reaching each uninterpreted
      function keeps. -/
  byUninterpreted : Std.HashMap String (Array Nat)
  /-- Positions of the axioms that mention no constant. -/
  always : Array Nat
  /-- User functions in the body of each function that has one. -/
  bodySyms : Std.HashMap String (Array String)

/-- Build the goal-directed relevance index of `prog`. -/
def DirectedIndex.build (prog : Program) : DirectedIndex := Id.run do
  let mut kinds : Std.HashMap String SymKind := {}
  let mut bodies : Array (String × Expression.Expr) := #[]
  for decl in prog.decls do
    let fs := match decl with
      | .func f _ => [f]
      | .recFuncBlock fs _ => fs
      | _ => []
    for f in fs do
      if f.isConstr then continue
      let name := CoreIdent.toPretty f.name
      let kind :=
        if f.inputs.isEmpty then SymKind.constant
        else if f.body.isSome then SymKind.defined
        else SymKind.uninterpreted
      kinds := kinds.insert name kind
      if let some body := f.body then
        bodies := bodies.push (name, body)
  let userSyms := fun (e : Expression.Expr) =>
    let ops := (Lambda.LExpr.getOps e).map CoreIdent.toPretty
    (Std.HashSet.ofList ops).toArray.filter kinds.contains
  let hasKind := fun (k : SymKind) (s : String) => kinds[s]? == some k
  let ofKind := fun (k : SymKind) (syms : Array String) =>
    syms.filter (hasKind k)
  let isConst := fun (e : Expression.Expr) => match e with
    | .op _ name _ => hasKind .constant (CoreIdent.toPretty name)
    | _ => false
  let isUninterpretedApp := fun (e : Expression.Expr) =>
    match (Lambda.getLFuncCall e).1 with
    | .op _ name _ => hasKind .uninterpreted (CoreIdent.toPretty name)
    | _ => false
  let mut bodySyms : Std.HashMap String (Array String) := {}
  for (name, body) in bodies do
    bodySyms := bodySyms.insert name (userSyms body)
  let mut axioms : Array DirectedAxiom := #[]
  let mut byConst : Std.HashMap String (Array Nat) := {}
  let mut factsByConst : Std.HashMap String (Array Nat) := {}
  let mut byUninterpreted : Std.HashMap String (Array Nat) := {}
  let mut always : Array Nat := #[]
  for decl in prog.decls do
    let .ax a _ := decl | continue
    let idx := axioms.size
    let syms := userSyms a.e
    let consts := ofKind .constant syms
    -- The constants a definition is followed from, and whether the axiom is
    -- a fact about uninterpreted functions (or not an equality). An equality
    -- with an uninterpreted application as either side is a fact about that
    -- function.
    let (defines, isFact) : Array String × Bool := match a.e with
      | .eq _ lhs rhs =>
        let lhsConsts := ofKind .constant (userSyms lhs)
        let rhsConsts := ofKind .constant (userSyms rhs)
        let (lhsUf, rhsUf) := (isUninterpretedApp lhs, isUninterpretedApp rhs)
        let (lhsBare, rhsBare) := (isConst lhs, isConst rhs)
        let defines :=
          if lhsConsts.isEmpty then (if rhsUf then #[] else rhsConsts)
          else if rhsConsts.isEmpty then (if lhsUf then #[] else lhsConsts)
          -- Both sides have constants.
          -- Each side is one constant: follow both.
          else if lhsBare && rhsBare then consts
          -- `f(x) == c` and `f(x) == g(y)` define nothing.
          else if lhsUf && (rhsUf || rhsBare) then #[]
          -- An uninterpreted function on the left: follow the right.
          else if lhsUf then rhsConsts
          else lhsConsts
        (defines, lhsUf || rhsUf)
      | _ => (#[], true)
    let uninterpreted := if isFact then ofKind .uninterpreted syms else #[]
    let isQuant := match a.e with | .quant .. => true | _ => false
    axioms := axioms.push { name := a.name, spread := syms, uninterpreted }
    if consts.isEmpty then always := always.push idx
    for c in defines do
      byConst := pushAt byConst c idx
    -- A quantified axiom is kept once one of its uninterpreted functions is
    -- reached. Another fact is kept from any of its constants once one of its
    -- uninterpreted functions is reached; a fact without them (a
    -- non-equality) needs only one of its constants.
    if isQuant && !uninterpreted.isEmpty then
      if !consts.isEmpty then
        for u in uninterpreted do
          byUninterpreted := pushAt byUninterpreted u idx
    else if isFact then
      for c in consts do
        if defines.contains c then continue
        if uninterpreted.isEmpty then byConst := pushAt byConst c idx
        else factsByConst := pushAt factsByConst c idx
  return { kinds, axioms, byConst, factsByConst, byUninterpreted, always,
           bodySyms }

/-- Labels of the axioms that goal-directed relevance drops for a goal whose
    functions (and those of its non-axiom assumptions) are `seeds`.

    A search from `seeds`, and from the functions of the axioms that are
    always kept, through function bodies and kept axioms; a fact about an
    uninterpreted function waits until that function is reached. -/
def DirectedIndex.irrelevantAxioms (idx : DirectedIndex)
    (seeds : List String) : Array String := Id.run do
  let mut seen := Std.HashSet.ofArray (seeds.toArray.filter idx.kinds.contains)
  let mut kept : Array Bool := Array.replicate idx.axioms.size false
  for i in idx.always do
    kept := kept.set! i true
    seen := seen.insertMany idx.axioms[i]!.spread
  let mut todo := seen.toArray
  -- Axioms waiting on each uninterpreted function not yet reached.
  let mut waiting : Std.HashMap String (Array Nat) := {}
  -- Each pass handles one new name, and every name reached is a user
  -- function, so `kinds.size` passes suffice.
  for _ in [0:idx.kinds.size] do
    let some s := todo.back? | break
    todo := todo.pop
    let mut keep : Array Nat := #[]
    match idx.kinds[s]? with
    | some .constant =>
      keep := idx.byConst.getD s #[]
      for i in idx.factsByConst.getD s #[] do
        let ufs := idx.axioms[i]!.uninterpreted
        if ufs.any seen.contains then
          keep := keep.push i
        else
          for u in ufs do
            waiting := pushAt waiting u i
    | some .uninterpreted =>
      keep := waiting.getD s #[] ++ idx.byUninterpreted.getD s #[]
    | _ => pure ()
    let mut next := idx.bodySyms.getD s #[]
    for i in keep do
      if !kept.getD i true then
        kept := kept.set! i true
        next := next ++ idx.axioms[i]!.spread
    for t in next do
      if !seen.contains t then
        seen := seen.insert t
        todo := todo.push t
  let mut irrelevant : Array String := #[]
  for i in [0:idx.axioms.size] do
    if !kept.getD i true then
      irrelevant := irrelevant.push idx.axioms[i]!.name
  return irrelevant

/-- Precomputed data for efficient per-goal axiom relevance queries.
  Build once with `Cache.build` before a verification loop and reuse
  across all goals for the same program. -/
inductive Cache where
  /-- Data for call-graph relevance (`Aggressive`, `Precise`). -/
  | callGraph (funcCG : FunctionCG) (axiomMap : FuncAxMap)
  /-- Data for goal-directed relevance (`Directed`). -/
  | directed (idx : DirectedIndex)

/-- Build the cache from `prog`, for goal-directed relevance when `directed`
    is set. -/
def Cache.build (prog : Program) (directed : Bool := false) : Cache :=
  if directed then .directed (DirectedIndex.build prog)
  else .callGraph prog.toFunctionCG prog.functionImmediateAxiomMap

/-- Labels of the axioms of `prog` irrelevant to `functions`, using a `cache`
  built from `prog`. A call-graph cache uses the transitive fixed-point
  algorithm (`computeRelevantAxioms`), and a directed cache uses
  `DirectedIndex.irrelevantAxioms`. -/
def getIrrelevantAxioms (prog : Program) (cache : Cache) (functions : List String)
    : List String :=
  match cache with
  | .directed idx => (idx.irrelevantAxioms functions).toList
  | .callGraph funcCG axiomMap =>
    let allAxiomNames := prog.decls.filterMap (fun decl =>
      match decl with | .ax a _ => some a.name | _ => none)
    let relevantAxioms := functions.flatMap (fun f =>
      let initialFns :=
        (f :: funcCG.getCalleesClosure f ++ funcCG.getCallersClosure f).uniq
      computeRelevantAxioms prog funcCG axiomMap allAxiomNames initialFns [])
      |>.uniq
    allAxiomNames.filter (fun a => a ∉ relevantAxioms)

open Transform in
/-- Remove irrelevant axiom declarations from `prog` given a list of relevant
    function names. Returns the pruned program via `CoreTransformM`. -/
def run (prog : Program) (functions : List String) : CoreTransformM Program := do
  let cache := Cache.build prog
  let irrelevant := getIrrelevantAxioms prog cache functions
  let irrelevantSet := Std.HashSet.ofList irrelevant
  let prunedDecls := prog.decls.filter (fun decl =>
    match decl with
    | .ax a _ => !irrelevantSet.contains a.name
    | _ => true)
  return { prog with decls := prunedDecls }

end IrrelevantAxioms

/-- Pipeline phase that removes axiom declarations irrelevant to the named
    functions. The transform only deletes axioms (no new assumptions are
    introduced), so it is model-preserving.
    If the user of this pass removes further axioms because e.g., it is in the
    'aggressive' mode, it will have to validate the model by itself. -/
def irrelevantAxiomsPipelinePhase (functions : List String) : PipelinePhase :=
  -- No statement is read or written, so every fact survives.
  modelPreservingPipelinePhase "removeIrrelevantAxioms"
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                         .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions])
    fun prog => do
      let pruned ← IrrelevantAxioms.run prog functions
      return (true, pruned)

end -- public section
end Core
