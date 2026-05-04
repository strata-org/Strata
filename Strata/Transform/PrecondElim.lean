/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.DL.Lambda.Preconditions
public import Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.CoreOp
import all Strata.DL.Imperative.Stmt
import Strata.Util.DecideProp

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
    and overflow), the precondition index distinguishes them.

    Exposed (not `private`) so that tests can verify the classification for each
    partial op without having to inspect metadata on generated asserts. -/
def classifyPrecondition (funcName : String) (precondIdx : Nat := 0) : Option String :=
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
      body := body
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
      body := wfStmts
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
    -- Preserve the per-invariant label in the generated preconditions' prefix.
    -- For unlabeled invariants, fall back to the plain "loop_invariant" prefix.
    let invAsserts := invariant.flatMap (fun (lbl, inv) =>
      let prefix' := if lbl.isEmpty then "loop_invariant" else s!"loop_invariant_{lbl}"
      collectPrecondAsserts F inv prefix' md)
    let guardAsserts := match guard with
      | .det g => collectPrecondAsserts F g "loop_guard" md
      | .nondet => []
    let guardAssertsEnd := match guard with
      | .det g => collectPrecondAsserts F g "loop_guard_end" md
      | .nondet => []

    incrementStat s!"{Stats.callSiteAssertsEmitted}"
      (measureAsserts.length + measureAssertsEnd.length +
       invAsserts.length + guardAsserts.length + guardAssertsEnd.length)

    let savedF ← getFactory
    let (changed, body') ← transformStmts body
    setFactory savedF
    return (changed || !invAsserts.isEmpty || !guardAsserts.isEmpty || !measureAsserts.isEmpty,
      guardAsserts ++ invAsserts ++ measureAsserts ++
      [.loop guard measure invariant (body' ++ measureAssertsEnd ++ guardAssertsEnd) md])
  | .exit lbl md =>
    return (false, [.exit lbl md])
  | .funcDecl decl md => do
    let funcName := decl.name.name
    -- Add function to factory before processing its preconditions/body
    let func ← liftDiag ((Function.ofPureFunc decl).mapError DiagnosticModel.fromFormat)

    let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
      | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
    let F' := F.push func notMem
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
    match decls with
    | [] => return (false, [])
    | d :: rest =>
      match d with
      | .proc proc md => do
        let F ← getFactory
        let (changed, body') ← transformStmts proc.body
        setFactory F
        let proc' := { proc with body := body' }
        let procDecl := Decl.proc proc' md
        let (changed', rest') ← transformDecls rest
        match mkContractWFProc F proc md with
        | some wfDecl => do
          incrementStat s!"{Stats.wfProceduresGenerated}"
          incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
            (match wfDecl with | .proc p _ => p.body.length | _ => 0)

          addWFProcToCallGraph (wfProcName (CoreIdent.toPretty proc.header.name))
          return (true, wfDecl :: procDecl :: rest')
        | none => return (changed || changed', procDecl :: rest')
      | .func func md => do
        let F ← getFactory
        let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
          | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
        let F' := F.push func notMem
        setFactory F'
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        let hasPreconds := !func.preconditions.isEmpty
        if hasPreconds then incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}"
        let (changed, rest') ← transformDecls rest
        match mkFuncWFProc F' func md with
        | some wfDecl => do
          incrementStat s!"{Stats.wfProceduresGenerated}"
          incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
            (match wfDecl with | .proc p _ => p.body.length | _ => 0)

          addWFProcToCallGraph (wfProcName (CoreIdent.toPretty func.name))
          return (true, wfDecl :: funcDecl :: rest')
        | none => return (changed || hasPreconds, funcDecl :: rest')
      | .recFuncBlock funcs md => do
        let F ← getFactory
        let F' ← funcs.foldlM (init := F) fun F func =>  do
          let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
            | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
          pure <| F.push func notMem
        setFactory F'
        let funcs' := funcs.map ({ · with preconditions := [] })
        let funcDecl := Decl.recFuncBlock funcs' md
        let hasPreconds := funcs.any (!·.preconditions.isEmpty)
        let numStripped := funcs.foldl (fun n f =>
          if !f.preconditions.isEmpty then n + 1 else n) 0
        incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}" numStripped

        let (changed, rest') ← transformDecls rest
        let wfDecls ← funcs.filterMapM fun func => do
          match mkFuncWFProc F' func md with
          | some wfDecl => do
            incrementStat s!"{Stats.wfProceduresGenerated}"
            incrementStat s!"{Stats.wfProcedureBodyStmtsEmitted}"
              (match wfDecl with | .proc p _ => p.body.length | _ => 0)

            addWFProcToCallGraph (wfProcName (CoreIdent.toPretty func.name))
            return some wfDecl
          | none => return none
        if !wfDecls.isEmpty then return (true, funcDecl :: wfDecls ++ rest')
        else return (changed || hasPreconds, funcDecl :: rest')
      | .type (.data block) _ => do
        let F ← getFactory
        let bf ← liftDiag (Lambda.genBlockFactory (T := CoreLParams) block)
        let F' ← liftDiag (F.addFactory bf)
        setFactory F'
        let (changed, rest') ← transformDecls rest
        return (changed, d :: rest')
      | _ => do
        let (changed, rest') ← transformDecls rest
        return (changed, d :: rest')

end PrecondElim

/-- PrecondElim pipeline phase: generates well-formedness checks for
    partial-function preconditions. Model-preserving because it only adds
    new assertions and procedures without abstracting existing ones. -/
def precondElimPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "PrecondElim" fun prog => do
    PrecondElim.precondElim prog

end Core

end -- public section
