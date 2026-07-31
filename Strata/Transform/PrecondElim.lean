/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import all Strata.DL.Imperative.Stmt
public import Strata.Util.DecideProp
import Strata.DL.Lambda.Preconditions
import Strata.Languages.Core.Factory
import Strata.Transform.TerminationCheck
import Strata.Util.Tactics

/-! # Partial Function Precondition Elimination

This transformation eliminates function preconditions.

In particular, it does the following:
1. For every call to a function with a precondition, it inserts an `assert` at
the call site.
2. For every function and procedure contract, it generates a well-formedness
check asserting that all calls to functions preconditions within the contract
hold, assuming earlier calls succeed.
3. For function declarations, the well-formedness check also asserts the
preconditions of any partial functions called within the body.
4. The returned program consists only of total functions (no preconditions).

See StrataTest/Transform/PrecondElim.lean for examples.

Note that this transformation must be called BEFORE typechecking, since
in the presence of polymorphic preconditions, the resulting assertions
have type variables that must be unified.
-/

public section

namespace Core
namespace PrecondElim

open Lambda
open Strata (DiagnosticModel)
open Core.Transform

/-- Statistics keys tracked by the precondition elimination transformation. -/
inductive Stats where
  | callSiteAssertsEmitted
  | wfProcedureBodyStmtsEmitted
  | wfProceduresGenerated
  | numFuncsRemovedAfterPrecondStripped

#derive_prefixed_toString Stats "PrecondElim"

/-! ## Naming conventions -/

/-- Suffix for generated well-formedness procedures. -/
def wfSuffix : String := "$$wf"

def wfProcName (name : String) : String := s!"{name}{wfSuffix}"

/-! ## Collecting assertions from expressions -/

/-- Classify a function precondition into a property type for SARIF reporting.
    For functions with multiple preconditions (e.g., SafeSDiv has both div-by-zero
    and overflow), the precondition index distinguishes them. -/
private def classifyPrecondition (funcName : String) (precondIdx : Nat := 0) : Option String :=
  match CoreOp.ofString funcName with
  | .numeric ⟨_, .SafeDiv⟩ | .numeric ⟨_, .SafeMod⟩
  | .numeric ⟨_, .SafeDivT⟩ | .numeric ⟨_, .SafeModT⟩ =>
    some Imperative.MetaData.divisionByZero
  | .bv ⟨_, .SafeSDiv⟩ | .bv ⟨_, .SafeSMod⟩ =>
    if precondIdx == 0 then some Imperative.MetaData.divisionByZero
    else some Imperative.MetaData.arithmeticOverflow
  | .bv ⟨_, .SafeAdd⟩ | .bv ⟨_, .SafeSub⟩ | .bv ⟨_, .SafeMul⟩ | .bv ⟨_, .SafeNeg⟩
  | .bv ⟨_, .SafeUAdd⟩ | .bv ⟨_, .SafeUSub⟩ | .bv ⟨_, .SafeUMul⟩ | .bv ⟨_, .SafeUNeg⟩ =>
    some Imperative.MetaData.arithmeticOverflow
  | .seq .Select | .seq .Update | .seq .Take | .seq .Drop =>
    some Imperative.MetaData.outOfBoundsAccess
  | _ => none

/--
Given a Factory and an expression, collect all partial function call
precondition obligations and return them as `assert` statements.

Ideally, each generated assertion would use the call site expression's own
metadata (`ob.callSiteMetadata`), but `CoreExprMetadata` is currently `Unit`,
so expression-level metadata carries no source location. We therefore inherit
the enclosing statement's `md` (with `propertySummary` stripped to prevent
user-facing messages from leaking into generated checks).
-/
def collectPrecondAsserts (F : @Lambda.Factory CoreLParams) (e : Expression.Expr)
(labelPrefix : String) (md : Imperative.MetaData Expression)
: List Statement :=
  let wfObs := Lambda.collectWFObligations F e
  -- Strip propertySummary: the enclosing statement's user-facing message
  -- (e.g., a Python assert message) should not propagate to generated
  -- precondition checks for called functions.
  let md := md.eraseAllElems Imperative.MetaData.propertySummary
  -- Use modulo to cycle the precondition index correctly across call sites.
  -- For nested calls like SafeSDiv(SafeSDiv(x,y),z), obligations arrive as
  -- [inner-0, inner-1, outer-0, outer-1] with the same funcName throughout.
  -- Without modulo, the index would be 0,1,2,3 instead of 0,1,0,1.
  let (_, _, result) := wfObs.foldl (init := ("", 0, ([] : List Statement)))
    fun (prevFunc, prevIdx, acc) ob =>
      let rawIdx := if ob.funcName == prevFunc then prevIdx + 1 else 0
      let precondCount := F[ob.funcName]?.map (·.preconditions.length) |>.getD 1
      let precondIdx := if precondCount > 0 then rawIdx % precondCount else rawIdx
      let globalIdx := acc.length
      let md' := match classifyPrecondition ob.funcName precondIdx with
        | some pt => md.pushElem Imperative.MetaData.propertyType (.msg pt)
        | none => md
      let stmt := Statement.assert
        s!"{labelPrefix}_calls_{ob.funcName}_{globalIdx}" ob.obligation md'
      (ob.funcName, rawIdx, stmt :: acc)
  result.reverse

/--
Collect assertions for all expressions in a command.
-/
def collectCmdPrecondAsserts (F : @Lambda.Factory CoreLParams)
  (cmd : Imperative.Cmd Expression) : List Statement :=
  match cmd with
  | .init _ _ (.det e) md => collectPrecondAsserts F e "init" md
  | .init _ _ .nondet _ => []
  | .set x (.det e) md => collectPrecondAsserts F e s!"set_{x.name}" md
  | .set _ .nondet _ => []
  | .assert l e md => collectPrecondAsserts F e s!"assert_{l}" md
  | .assume l e md => collectPrecondAsserts F e s!"assume_{l}" md
  | .cover l e md => collectPrecondAsserts F e s!"cover_{l}" md

/--
Collect assertions for call arguments.
-/
def collectCallPrecondAsserts (F : @Lambda.Factory CoreLParams) (pname : String)
  (args : List Expression.Expr) (md : Imperative.MetaData Expression)
  : List Statement :=
  args.flatMap fun arg => collectPrecondAsserts F arg s!"call_{pname}_arg" md

/-! ## Processing contract conditions -/

/--
Process a single contract condition: assert WF of partial function calls,
then assume the condition. Returns the generated statements.
-/
def processCondition (F : @Lambda.Factory CoreLParams)
    (expr : Expression.Expr) (assertLabel : String) (assumeLabel : String)
    (md : Imperative.MetaData Expression) : List Statement :=
  let asserts := collectPrecondAsserts F expr assertLabel md
  let assume := Statement.assume assumeLabel expr md
  asserts ++ [assume]

/-- Returns true if any statement in the list is an assert. -/
private def hasAssert (stmts : List Statement) : Bool :=
  stmts.any (fun s => match s with | .assert _ _ _ => true | _ => false)

/-! ## Loop invariant well-formedness

A loop invariant is *assumed* and re-asserted at the arbitrary mid-loop state,
over the havoc'd loop-carried variables. Checking its well-formedness in the
loop's pre-state is therefore checking the wrong state: the pre-state knows
strictly more, so a definedness obligation can be vacuously discharged there
and never checked where the invariant is actually used.

Core has no program point meaning "at the loop head, before the invariant is
assumed", so we synthesize one: a *severed proof block* placed immediately
before the loop.

```
if * {
  havoc(M);            -- M = loop-carried write-set: the loop-head state
  assert WF(I_0);      -- checked at the loop head, not the pre-state
  assume I_0;          -- chained: I_1's WF may rely on I_0
  assert WF(I_1);
  assume I_1;
  ...
  assume false;        -- sever: this path contributes nothing downstream
} else { }
```

The `havoc(M)` reaches the same state the invariant is assumed at, and the
asserts precede every `assume I_k`, so no invariant is assumed before its own
definedness is established. `assume false` severs the branch: the havoc cannot
leak into the pre-state and the block cannot make downstream obligations
vacuous (it is one arm of a nondeterministic `ite`, so the other arm carries
the real path). The chaining mirrors `processCondition`, which already gives
procedure contracts this discipline.

See `docs/CoreLoopInvariantWFBlock.md`. A native loop `proving` block would
avoid the `assume false`; this pass builds the same program point out of the
statement forms Core has today.
-/

/-- Label of the `assume false` that severs the invariant-WF proof block. -/
def loopInvWFSeverLabel : String := "loop_invariant_wf_sever"

/-- Block label prefix for a loop's invariant-WF proof block. -/
def loopInvWFBlockPrefix : String := "loop_invariant_wf"

/--
Build the severed pre-invariant-proof block for a loop's invariants.

`targets` is the loop-carried write-set to havoc (the loop body's modified
variables, minus those declared inside the body, which are block-local and not
part of the loop-head state).

Returns `none` when no invariant yields a well-formedness obligation, so that
loops with total invariants are left untouched. Otherwise returns the block and
the number of WF asserts it contains (for statistics).
-/
def mkLoopInvariantWFBlock (F : @Lambda.Factory CoreLParams)
    (invariants : List (String × Expression.Expr))
    (targets : List Expression.Ident)
    (md : Imperative.MetaData Expression) : Option (Statement × Nat) :=
  -- Per-invariant WF asserts, each followed by an assume of that invariant so a
  -- later invariant's WF may rely on the earlier ones (as contracts do).
  -- The index keeps the assume labels distinct when source labels are absent or
  -- coincide, matching the `invSuffix` convention in the loop VC passes.
  let chained := (invariants.mapIdx fun i (lbl, inv) =>
    let suffix := if lbl.isEmpty then toString i else s!"{i}_{lbl}"
    let prefix' := if lbl.isEmpty then "loop_invariant" else s!"loop_invariant_{lbl}"
    processCondition F inv prefix' s!"assume_wf_loop_invariant_{suffix}" md).flatten
  -- Nothing to check: leave the loop alone rather than emitting a dead block.
  if !hasAssert chained then
    none
  else
    let havocs := targets.map (fun v => Statement.havoc v md)
    let sever := Statement.assume loopInvWFSeverLabel Core.false md
    let body := havocs ++ chained ++ [sever]
    -- A nondeterministic `ite` whose else-branch is empty: the then-branch is
    -- severed by `assume false`, so this adds a proof context without adding a
    -- feasible path.
    let numAsserts := chained.countP (fun s => match s with | .assert _ _ _ => true | _ => false)
    some (.ite .nondet [.block loopInvWFBlockPrefix body md] [] md, numAsserts)

/-! ## Contract well-formedness procedures -/

/--
Generate a well-formedness checking procedure for a procedure's contract.

For each precondition+postcondition (in order):
  - Assert WF of partial function calls in the condition
  - Assume the condition (for use by subsequent clauses)
-/
def mkContractWFProc (F : @Lambda.Factory CoreLParams) (proc : Procedure)
    (md : Imperative.MetaData Expression)
: Option Decl :=
  let name := proc.header.name.name
  let precondStmts := proc.spec.preconditions.flatMap fun (label, check) =>
    processCondition F check.expr s!"{name}_pre_{label}" label check.md
  let postcondStmts := proc.spec.postconditions.flatMap fun (label, check) =>
    processCondition F check.expr s!"{name}_post_{label}" label check.md
  let body := precondStmts ++ postcondStmts
  if hasAssert body then
    some <| .proc {
      header := { proc.header with name := ⟨wfProcName name, ()⟩, noFilter := true }
      spec := { preconditions := [], postconditions := [] }
      body := .structured body
    } md
  else
    none

/-! ## Function well-formedness generation -/

/--
Generate the well-formedness checking statements for a function's preconditions
and body. This is shared between top-level function declarations and inline
function declarations.

For each precondition (in order):
  - Assert WF of partial function calls in the precondition
  - Assume the precondition

For the body (if present):
  - Assert WF of partial function calls in the body

Returns `none` if no assertions are generated, otherwise `some stmts`.
-/
def mkFuncWFStmts (F : @Lambda.Factory CoreLParams) (funcName : String)
    (preconditions : List (Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata))
    (body : Option Expression.Expr)
    (md : Imperative.MetaData Expression) : Option (List Statement) :=
  let (precondStmts, _) := preconditions.foldl (fun (stmts, idx) precond =>
    let stmts' := processCondition F precond.expr
      s!"{funcName}_precond" s!"precond_{funcName}_{idx}" md
    (stmts ++ stmts', idx + 1)) ([], 0)
  let bodyStmts := match body with
    | none => []
    | some b => collectPrecondAsserts F b s!"{funcName}_body" md
  let allStmts := precondStmts ++ bodyStmts
  if hasAssert allStmts then
    some allStmts
  else
    none

/--
Generate a well-formedness checking procedure for a top-level function declaration.
-/
def mkFuncWFProc (F : @Lambda.Factory CoreLParams) (func : Function)
    (md : Imperative.MetaData Expression)
: Option Decl :=
  let funcName := func.name.name
  (mkFuncWFStmts F funcName func.preconditions func.body md).bind
  (fun wfStmts =>
    some <| .proc {
      header := {
        name := ⟨wfProcName funcName, ()⟩
        typeArgs := func.typeArgs
        inputs := func.inputs
        outputs := []
        noFilter := true
      }
      spec := { preconditions := [], postconditions := [] }
      body := .structured wfStmts
    } md)

/-! ## Statement transformation -/

mutual
/-- Eliminate function preconditions from blocks. -/
def transformStmts (ss : List Statement)
    : CoreTransformM (Bool × List Statement) :=
  match ss with
  | [] => return (false, [])
  | s :: rest => do
    let (changed, s') ← transformStmt s
    let (changed', rest') ← transformStmts rest
    return (changed || changed', s' ++ rest')
  termination_by Imperative.Block.sizeOf ss
  decreasing_by all_goals term_by_mem

/-- Eliminate function preconditions from statement, adding assertions
  at call sites (including in existing assertions and loop invariants).
  Function declaration statements produce a well-formedness check block
  mirroring the procedure created for top-level functions. -/
def transformStmt (s : Statement)
    : CoreTransformM (Bool × List Statement) := do
  let F ← getFactory
  match s with
  | .cmd (.cmd c) =>
    let asserts := collectCmdPrecondAsserts F c
    incrementStat s!"{Stats.callSiteAssertsEmitted}" asserts.length
    return (!asserts.isEmpty, asserts ++ [.cmd (.cmd c)])
  | .cmd (.call pname callArgs md) =>
    let asserts := collectCallPrecondAsserts F pname (CallArg.getInputExprs callArgs) md
    incrementStat s!"{Stats.callSiteAssertsEmitted}" asserts.length
    return (!asserts.isEmpty, asserts ++ [.call pname callArgs md])
  | .block lbl b md => do
    let savedF ← getFactory
    let (changed, b') ← transformStmts b
    setFactory savedF
    return (changed, [.block lbl b' md])
  | .ite c thenb elseb md => do
    let condAsserts := match c with
      | .det e => collectPrecondAsserts F e "ite_cond" md
      | .nondet => []
    incrementStat s!"{Stats.callSiteAssertsEmitted}" condAsserts.length

    let savedF ← getFactory
    let (changed, thenb') ← transformStmts thenb
    setFactory savedF
    let (changed', elseb') ← transformStmts elseb
    setFactory savedF
    return (changed || changed' || !condAsserts.isEmpty,
      condAsserts ++ [.ite c thenb' elseb' md])
  | .loop guard measure invariant body md => do
    let measureAsserts := match measure with
      | none => []
      | some m => collectPrecondAsserts F m "loop_measure" md
    let measureAssertsEnd := match measure with
      | none => []
      | some m => collectPrecondAsserts F m "loop_measure_end" md
    -- Invariant well-formedness is checked at the loop head, not in the
    -- pre-state: see `mkLoopInvariantWFBlock`. The loop-carried write-set is
    -- the body's modified variables minus its block-local declarations, matching
    -- what `LoopElim` havocs for the mid-loop state.
    let localDefs := Imperative.Block.definedVars body false
    let loopTargets :=
      (Imperative.Block.modifiedVars body).filter (fun v => v ∉ localDefs)
    -- `invWFStmts` is the proof block (a single statement) when any invariant
    -- has a WF obligation; `invWFAsserts` counts the asserts inside it.
    let (invWFStmts, invWFAsserts) := match mkLoopInvariantWFBlock F invariant loopTargets md with
      | some (blk, n) => ([blk], n)
      | none => ([], 0)
    let guardAsserts := match guard with
      | .det g => collectPrecondAsserts F g "loop_guard" md
      | .nondet => []
    let guardAssertsEnd := match guard with
      | .det g => collectPrecondAsserts F g "loop_guard_end" md
      | .nondet => []

    incrementStat s!"{Stats.callSiteAssertsEmitted}"
      (measureAsserts.length + measureAssertsEnd.length +
       invWFAsserts + guardAsserts.length + guardAssertsEnd.length)

    let savedF ← getFactory
    let (changed, body') ← transformStmts body
    setFactory savedF
    return (changed || !invWFStmts.isEmpty || !guardAsserts.isEmpty || !measureAsserts.isEmpty,
      guardAsserts ++ invWFStmts ++ measureAsserts ++
      [.loop guard measure invariant (body' ++ measureAssertsEnd ++ guardAssertsEnd) md])
  | .exit lbl md =>
    return (false, [.exit lbl md])
  | .funcDecl decl md => do
    let funcName := decl.name.name
    -- Add function to factory before processing its preconditions/body
    let func ← liftDiag ((Function.ofPureFunc decl).mapError DiagnosticModel.fromFormat)

    let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
      | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
    let F' := F.push func.toLFunc notMem
    setFactory F'
    let decl' := { decl with preconditions := [] }
    let hasPreconds := !decl.preconditions.isEmpty
    if hasPreconds then incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}"

    match mkFuncWFStmts F' funcName decl.preconditions decl.body md with
    | none => return (hasPreconds, [.funcDecl decl' md])
    | some wfStmts =>
      incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}" wfStmts.length
      -- Add init statements for function parameters so they're in scope
      let paramInits := decl.inputs.toList.map fun (name, ty) =>
        Statement.init name ty .nondet md
      return (hasPreconds, [.block s!"{funcName}{wfSuffix}" (paramInits ++ wfStmts) md, .funcDecl decl' md])
  | .typeDecl _ _ =>
    return (false, [s])  -- Type declarations pass through unchanged
  termination_by s.sizeOf
  decreasing_by all_goals term_by_mem
end

/-! ## Main transformation -/

/-- Add a precondition-WF procedure as a leaf node in the cached call graph.
These procedures contain only assert/assume statements and make no procedure
calls, so they have no outgoing edges. -/
private def addWFProcToCallGraph (name : String) : CoreTransformM Unit :=
  modify fun σ => match σ.cachedAnalyses.callGraph with
  | .some cg => { σ with cachedAnalyses := { σ.cachedAnalyses with
      callGraph := .some (cg.addLeafNode name) } }
  | .none => σ

/--
Transform an entire program:
1. For each procedure, transform its body and if needed generate a WF procedure
2. For each function, strip preconditions and if needed generate a WF procedure
3. For each function call, assert that the preconditions hold

Returns (changed, transformed program).
-/
def precondElim (p : Program)
    : CoreTransformM (Bool × Program) := do
  -- If Factory is not set, there is no Factory function to process; finish early.
  match (← get).factory with
  | .none =>
    return (false, p)
  | .some _ =>
    let (changed, newDecls) ← transformDecls p.decls
    return (changed, { decls := newDecls })
where
  transformDecls (decls : List Decl)
      : CoreTransformM (Bool × List Decl) := do
    let mut acc : Array Decl := #[]
    let mut changed := false
    let mut remaining := decls
    while h : remaining ≠ [] do
      let d := remaining.head h
      let rest := remaining.tail
      match d with
      | .proc proc md => do
        if TermCheck.isTermProc proc.header.name.name then
          acc := acc.push d
        else
          let F ← getFactory
          let (bodyChanged, proc') ← match proc.body with
            | .structured ss =>
              let (c, body') ← transformStmts ss
              pure (c, { proc with body := .structured body' })
            -- CFG bodies pass through untouched.
            | .cfg _ => pure (false, proc)
          setFactory F
          let procDecl := Decl.proc proc' md
          match mkContractWFProc F proc md with
          | some wfDecl => do
            incrementStat s!"{Stats.wfProceduresGenerated}"
            incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
              (match wfDecl with | .proc p _ => p.body.structuredLength | _ => 0)
            addWFProcToCallGraph (wfProcName (CoreIdent.toPretty proc.header.name))
            changed := true
            acc := acc.push wfDecl
            acc := acc.push procDecl
          | none =>
            changed := changed || bodyChanged
            acc := acc.push procDecl
      | .func func md => do
        let F ← getFactory
        let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
          | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
        let F' := F.push func.toLFunc notMem
        setFactory F'
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        let hasPreconds := !func.preconditions.isEmpty
        if hasPreconds then incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}"
        match mkFuncWFProc F' func md with
        | some wfDecl => do
          incrementStat s!"{Stats.wfProceduresGenerated}"
          incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
            (match wfDecl with | .proc p _ => p.body.structuredLength | _ => 0)
          addWFProcToCallGraph (wfProcName (CoreIdent.toPretty func.name))
          changed := true
          acc := acc.push wfDecl
          acc := acc.push funcDecl
        | none =>
          changed := changed || hasPreconds
          acc := acc.push funcDecl
      | .recFuncBlock funcs md => do
        let F ← getFactory
        let F' ← funcs.foldlM (init := F) fun F func =>  do
          let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
            | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
          pure <| F.push func.toLFunc notMem
        setFactory F'
        let funcs' := funcs.map ({ · with preconditions := [] })
        let funcDecl := Decl.recFuncBlock funcs' md
        let hasPreconds := funcs.any (!·.preconditions.isEmpty)
        let numStripped := funcs.foldl (fun n f =>
          if !f.preconditions.isEmpty then n + 1 else n) 0
        incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}" numStripped
        let wfDecls ← funcs.filterMapM fun func => do
          match mkFuncWFProc F' func md with
          | some wfDecl => do
            incrementStat s!"{Stats.wfProceduresGenerated}"
            incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
              (match wfDecl with | .proc p _ => p.body.structuredLength | _ => 0)
            addWFProcToCallGraph (wfProcName (CoreIdent.toPretty func.name))
            return some wfDecl
          | none => return none
        if !wfDecls.isEmpty then
          changed := true
          acc := acc.push funcDecl
          acc := acc ++ wfDecls.toArray
        else
          changed := changed || hasPreconds
          acc := acc.push funcDecl
      | .type (.data block) _ => do
        let F ← getFactory
        let bf ← liftDiag (Lambda.genBlockFactory (T := CoreLParams) block)
        let F' ← liftDiag (F.addFactory bf)
        setFactory F'
        acc := acc.push d
      | _ => do
        acc := acc.push d
      remaining := rest
    return (changed, acc.toList)

end PrecondElim

/-- PrecondElim pipeline phase: generates well-formedness checks for
    partial-function preconditions. Model-preserving because it only adds
    new assertions and procedures without abstracting existing ones. -/
def precondElimPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "PrecondElim" fun prog => do
    PrecondElim.precondElim prog

end Core

end -- public section
