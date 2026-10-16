/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

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
2. For every function and procedure contract, it generates well-formedness
lemmas, one per call to a function with preconditions within the contract,
stating that the call's preconditions hold under the earlier conditions. The
function or procedure lists these lemmas among its dependencies.
3. For function declarations, well-formedness lemmas also state the
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
open Strata (Message)
open Core.Transform

/-- Statistics keys tracked by the precondition elimination transformation. -/
inductive Stats where
  | callSiteAssertsEmitted
  | wfProcedureBodyStmtsEmitted
  | wfLemmasGenerated
  | numFuncsRemovedAfterPrecondStripped

#derive_prefixed_toString Stats "PrecondElim"

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

/-! ## Well-formedness lemmas -/

/--
The well-formedness lemmas for the checks `stmts`, quantified over `binders` and
generic in `typeArgs`: one lemma per `assert q`, named and annotated like it,
whose formula is `p₁ ==> … ==> pₙ ==> q` for the conditions `pᵢ` assumed before
it. Earlier checks are not hypotheses, since their own lemmas check them.

A name already in `taken`, such as a declaration of the program, or repeated
among the checks, gets a `_k` suffix: checks from different conditions can
share a label, since each condition numbers its checks from 0.

We should emit only one lemma in the future, whose formula keeps the whole tree
of checks, and be able to verify it incrementally while reporting each check.
-/
def mkWFLemmas (taken : List String) (typeArgs : List TyIdentifier)
    (binders : List (Expression.Ident × Lambda.LMonoTy)) (stmts : List Statement) :
    List Decl :=
  let (_, _, lemmas) := stmts.foldl
    (init := (([] : List Expression.Expr), taken, ([] : List Decl)))
    fun (hyps, names, lemmas) s =>
      match s with
      | .assume _ p _ => (p :: hyps, names, lemmas)
      | .assert label q md =>
        let e := hyps.foldl (init := q) fun body p => LExpr.mkApp () boolImpliesOp [p, body]
        let name := Lemma.freshName names label
        (hyps, name :: names, .lemma { name, typeArgs, e := Lemma.forallOver binders e } md :: lemmas)
      | _ => (hyps, names, lemmas)
  lemmas.reverse

/--
Generate the well-formedness lemmas for a procedure's contract.

For each precondition+postcondition (in order):
  - Check the preconditions of partial function calls in the condition
  - Assume the condition (for use by subsequent clauses)

The lemmas quantify over the procedure's parameters and the `old` values of
its in-out parameters. Preconditions describe the entry state, so in them an
in-out parameter stands for its `old` value.
-/
def mkContractWFLemmas (F : @Lambda.Factory CoreLParams) (taken : List String)
    (proc : Procedure) : List Decl :=
  let name := proc.header.name.name
  let inouts := proc.header.getInoutParams.toList
  let atEntry (e : Expression.Expr) : Expression.Expr :=
    inouts.foldl (init := e) fun e (x, _) =>
      LExpr.substFvar e x (.fvar () (CoreIdent.mkOld x.name) none)
  let precondStmts := proc.spec.preconditions.flatMap fun (label, check) =>
    processCondition F (atEntry check.expr) s!"{name}_pre_{label}" label check.md
  let postcondStmts := proc.spec.postconditions.flatMap fun (label, check) =>
    processCondition F check.expr s!"{name}_post_{label}" label check.md
  let binders := proc.header.inputs.toList ++ proc.header.getOutputOnlyParams.toList ++
    inouts.map fun (x, ty) => (CoreIdent.mkOld x.name, ty)
  mkWFLemmas taken proc.header.typeArgs binders (precondStmts ++ postcondStmts)

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
Generate the well-formedness lemmas for a top-level function declaration,
quantified over the function's inputs.
-/
def mkFuncWFLemmas (F : @Lambda.Factory CoreLParams) (taken : List String)
    (func : Function) (md : Imperative.MetaData Expression) : List Decl :=
  match mkFuncWFStmts F func.name.name func.preconditions func.body md with
  | some stmts => mkWFLemmas taken func.typeArgs func.inputs.toList stmts
  | none => []

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
  at call sites (including in existing assertions and loop invariants). -/
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
  | .typeDecl _ _ =>
    return (false, [s])  -- Type declarations pass through unchanged
  termination_by s.sizeOf
  decreasing_by all_goals term_by_mem
end

/-! ## Main transformation -/

/--
Transform an entire program:
1. For each procedure, transform its body and if needed generate a WF lemma
2. For each function, strip preconditions and if needed generate a WF lemma
3. For each function call, assert that the preconditions hold

Returns (changed, transformed program).
-/
def precondElim (p : Program)
    : CoreTransformM (Bool × Program) := do
  -- The factory is accumulated across declarations *within* this pass so that
  -- WF-obligation collection can resolve calls to earlier declarations. This
  -- accumulation is an internal detail of the pass: restore the factory
  -- afterwards so it does not leak into the pipeline's output state (which is
  -- threaded into `buildEnv`, where the program's functions are registered
  -- afresh and duplicates must surface as errors).
  let savedF ← getFactory
  try
    -- Generated lemmas are named away from every declaration of the program.
    let taken := p.decls.flatMap fun d => d.names.map (·.name)
    let listed := p.decls.flatMap fun
      | .proc proc _ => proc.header.lemmas
      | .func f _ => f.lemmas
      | .recFuncBlock fs _ => fs.flatMap (·.lemmas)
      | _ => []
    let (changed, newDecls) ← transformDecls taken listed p.decls
    setFactory savedF
    return (changed, { decls := newDecls })
  catch e =>
    setFactory savedF
    throw e
where
  transformDecls (taken listed : List String) (decls : List Decl)
      : CoreTransformM (Bool × List Decl) := do
    let mut acc : Array Decl := #[]
    let mut changed := false
    let mut remaining := decls
    while h : remaining ≠ [] do
      let d := remaining.head h
      let rest := remaining.tail
      match d with
      | .proc proc md => do
        let F ← getFactory
        let (bodyChanged, proc') ← match proc.body with
          | .structured ss =>
            let (c, body') ← transformStmts ss
            pure (c, { proc with body := .structured body' })
          -- A CFG body cannot be walked here, and passing it through would
          -- lose the well-formedness and precondition asserts it owes: the
          -- obligations would go missing rather than fail. `noCFGBodies` is
          -- declared as a requirement; this is where it is enforced.
          | .cfg _ =>
            throw (Strata.Message.fromFormat
              f!"❌ PrecondElim: procedure {proc.header.name.name} has a CFG body; \
                 preconditions can only be eliminated from structured bodies.")
        setFactory F -- reset factory
        let wfDecls := mkContractWFLemmas F taken proc
        incrementStat s!"{Stats.wfLemmasGenerated}" wfDecls.length
        changed := changed || bodyChanged || !wfDecls.isEmpty
        acc := acc ++ wfDecls.toArray
        let header := { proc'.header with
          lemmas := proc'.header.lemmas ++ wfDecls.map (·.name.name) }
        acc := acc.push (Decl.proc { proc' with header } md)
      | .func func md => do
        let F ← getFactory
        let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
          | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
        let F' := F.push func.toLFunc notMem
        setFactory F'
        let func' := { func with preconditions := [] }
        let hasPreconds := !func.preconditions.isEmpty
        if hasPreconds then incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}"
        let wfDecls := mkFuncWFLemmas F' taken func md
        incrementStat s!"{Stats.wfLemmasGenerated}" wfDecls.length
        changed := changed || hasPreconds || !wfDecls.isEmpty
        -- A non-recursive function cannot mention itself in its preconditions
        -- or body, so its lemmas never mention it and precede it.
        acc := acc ++ wfDecls.toArray
        acc := acc.push (Decl.func { func' with lemmas := func'.lemmas ++ wfDecls.map (·.name.name) } md)
      | .recFuncBlock funcs md => do
        let F ← getFactory
        let F' ← funcs.foldlM (init := F) fun F func =>  do
          let .isFalse notMem := Strata.decideProp (func.name.name ∈ F)
            | throw (md.toDiagnosticF f!"{func.name.name} already in factory.")
          pure <| F.push func.toLFunc notMem
        setFactory F'
        let hasPreconds := funcs.any (!·.preconditions.isEmpty)
        let numStripped := funcs.foldl (fun n f =>
          if !f.preconditions.isEmpty then n + 1 else n) 0
        incrementStat s!"{Stats.numFuncsRemovedAfterPrecondStripped}" numStripped
        let wfDeclss := funcs.map (mkFuncWFLemmas F' taken · md)
        let funcs' := (funcs.zip wfDeclss).map fun (func, wfDecls) =>
          { func with preconditions := [],
                      lemmas := func.lemmas ++ wfDecls.map (·.name.name) }
        let wfDecls := wfDeclss.flatten
        incrementStat s!"{Stats.wfLemmasGenerated}" wfDecls.length
        changed := changed || hasPreconds || !wfDecls.isEmpty
        -- The lemmas follow the block: a body's path conditions may call the
        -- block's functions.
        acc := acc.push (Decl.recFuncBlock funcs' md)
        acc := acc ++ wfDecls.toArray
      | .lemma l md => do
        -- A lemma's partial calls are checked like an assertion's, by
        -- well-formedness lemmas declared before it. A lemma that a
        -- declaration lists was generated, such as a termination check, and
        -- its owner's own well-formedness lemmas already cover its calls.
        let F ← getFactory
        let wfDecls := if listed.contains l.name then [] else
          mkWFLemmas taken l.typeArgs [] (collectPrecondAsserts F l.e l.name md)
        incrementStat s!"{Stats.wfLemmasGenerated}" wfDecls.length
        changed := changed || !wfDecls.isEmpty
        acc := acc ++ wfDecls.toArray
        acc := acc.push d
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
  -- A CFG-bodied procedure is passed through untouched, so its
  -- well-formedness checks would go missing rather than fail; declaring the
  -- requirement turns that into a rejected pipeline.
  -- The pass only inserts assertion commands ahead of existing statements and
  -- never introduces new assignments, so `staticSingleAssignment` survives.
  -- `noBetaRedexes` is not claimed: a
  -- precondition is instantiated by substituting the call's arguments into it,
  -- and a function-typed parameter applied to an abstraction argument would
  -- leave a redex behind.
  modelPreservingPipelinePhase "precondElim"
    (requires := factSet![.noCFGBodies])
    (establishes := factSet![.noPrecondsFromFuncs])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noNondetGuards,
                         .noPolymorphicFunctions, .typeAnnotated])
    fun prog => do
      PrecondElim.precondElim prog

end Core

end -- public section
