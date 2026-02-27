/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.State
import Strata.Languages.Core.CoreSMT.State
import Strata.Languages.Core.CoreSMT.ExprTranslator
import Strata.Languages.Core.CoreSMT.IsCoreSMT
import Strata.Languages.Core.CoreSMT.Diagnosis
import Strata.Languages.Core.Verifier

/-!
# Statement Processor for CoreSMT Verifier

Processes CoreSMT statements by translating them to SMT solver commands.
Each statement type maps to specific SMT-LIB operations:
- assume → assert
- init with expr → define-fun
- init without expr → declare-fun
- assert → check-sat of negation (push/pop)
- cover → check-sat (push/pop)
- block → push/pop
- funcDecl → declare-fun or define-fun
-/

namespace Strata.Core.CoreSMT

open Core
open Strata.SMT
open Lambda
open Imperative

/-- Run a verification check: for assert, negate the expression; for cover, use it directly. -/
private def runCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr) (property : Imperative.PropertyType)
    (smtCtx : Core.SMT.Context) (md : Imperative.MetaData Core.Expression := .empty)
    : IO (Core.VCResult × Core.SMT.Context) := do
  match translateExpr E expr smtCtx with
  | .error msg =>
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property, assumptions := [], obligation := expr, metadata := md
    }
    return ({ obligation, result := .implementationError s!"Translation error: {msg}" }, smtCtx)
  | .ok (term, smtCtx) =>
    let isCover := property == .cover
    let checkTerm := if isCover then term else Factory.not term
    let decision ← state.solver.checkSatAssuming [checkTerm]
    let outcome := match isCover, decision with
      | true,  .sat     => Core.Outcome.pass
      | true,  .unsat   => Core.Outcome.fail
      | true,  .unknown => Core.Outcome.unknown
      | false, .unsat   => Core.Outcome.pass
      | false, .sat     => Core.Outcome.fail
      | false, .unknown => Core.Outcome.unknown
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property, assumptions := [], obligation := expr, metadata := md
    }
    let smtObligationResult := match decision with
      | .unsat   => SMT.Result.unsat
      | .sat     => SMT.Result.unknown
      | .unknown => SMT.Result.unknown
    let diagnosis ← if outcome != .pass then
      let diagResult ← diagnoseFailure state E expr isCover smtCtx
      let statePathCond := state.pathCondition
      let failures := diagResult.diagnosedFailures.map fun f =>
        { f with report := { f.report with context :=
            { pathCondition := f.report.context.pathCondition ++ statePathCond } } }
      pure (some { isRefuted := failures.any (·.isRefuted), diagnosedFailures := failures,
                   statePathCondition := statePathCond })
    else
      pure none
    return ({ obligation, smtObligationResult, result := outcome, diagnosis }, smtCtx)

private def proveCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) (md : Imperative.MetaData Core.Expression := .empty) :=
  runCheck state E label expr .assert smtCtx md

private def coverCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) (md : Imperative.MetaData Core.Expression := .empty) :=
  runCheck state E label expr .cover smtCtx md

private def processFuncDecl (state : CoreSMTState) (E : Core.Env)
    (decl : Imperative.PureFunc Core.Expression) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) := do
  let inputTypesResult ← decl.inputs.foldlM (fun (acc : Except Std.Format (List TermType)) (_, ty) => do
    match acc with
    | .error msg => return .error msg
    | .ok types =>
      match translateType E ty smtCtx with
      | .error msg => return .error msg
      | .ok (smtTy, _) => return .ok (types ++ [smtTy])
  ) (.ok [])
  let mkError (msg : String) : Core.VCResult :=
    let dummyExpr : Core.Expression.Expr := .const Strata.SourceRange.none (.boolConst true)
    { obligation := { label := s!"funcDecl {decl.name.name}", property := .assert,
                      assumptions := [], obligation := dummyExpr, metadata := .empty },
      result := .implementationError msg }
  match inputTypesResult with
  | .error msg => return (state, smtCtx, [mkError s!"Type translation error: {toString msg}"])
  | .ok inputTypes =>
    match translateType E decl.output smtCtx with
    | .error msg => return (state, smtCtx, [mkError s!"Output type translation error: {toString msg}"])
    | .ok (outTy, smtCtx) =>
      let ufArgs := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) => TermVar.mk name.name smtTy
      let uf : UF := { id := decl.name.name, args := ufArgs, out := outTy }
      let smtCtx := smtCtx.addUF uf
      match decl.body with
      | none =>
        state.solver.declareFun decl.name.name inputTypes outTy
        return ({ state with smtState := state.smtState.addItem (.funcDecl decl.name.name inputTypes outTy) }, smtCtx, [])
      | some body =>
        match translateExpr E body smtCtx with
        | .error msg =>
          return (state, smtCtx, [{ obligation := { label := s!"funcDecl {decl.name.name}", property := .assert,
                                                    assumptions := [], obligation := body, metadata := .empty },
                                    result := .implementationError s!"Body translation error: {msg}" }])
        | .ok (bodyTerm, smtCtx) =>
          let args := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) => (name.name, smtTy)
          state.solver.defineFun decl.name.name args outTy bodyTerm
          return ({ state with smtState := state.smtState.addItem (.funcDef decl.name.name args outTy bodyTerm) }, smtCtx, [])

mutual
/-- Process a single CoreSMT statement. Returns updated state, SMT context,
    and an optional check result (for assert/cover). -/
partial def processStatement (state : CoreSMTState) (E : Core.Env)
    (stmt : Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) := do
  if !isCoreSMTStmt stmt then
    let obligation : Imperative.ProofObligation Core.Expression := {
      label := "non-CoreSMT"
      property := .assert
      assumptions := []
      obligation := .fvar Strata.SourceRange.none (Core.CoreIdent.unres "error") none
      metadata := .empty
    }
    let result : Core.VCResult := { obligation, result := .implementationError "Statement not in CoreSMT subset" }
    return (state, smtCtx, [result])
  match stmt with
  | Core.Statement.assume _label expr _ =>
    match translateExpr E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := "assume", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Translation error: {msg}" }])
    | .ok (term, smtCtx) =>
      let solver : SMT.SolverInterface := state.solver
      solver.assert term
      let state := state.addItem (.assumption term)
      let state := state.addAssumption expr
      return (state, smtCtx, [])

  | Core.Statement.init name ty (some expr) _ =>
    match translateExpr E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"init {name.name}", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Translation error: {msg}" }])
    | .ok (term, smtCtx) =>
      match translateType E ty smtCtx with
      | .error msg =>
        let obligation : Imperative.ProofObligation Core.Expression := {
          label := s!"init {name.name}", property := .assert, assumptions := [], obligation := expr, metadata := .empty
        }
        return (state, smtCtx, [{ obligation, result := .implementationError s!"Type translation error: {msg}" }])
      | .ok (smtTy, smtCtx) =>
        let solver : SMT.SolverInterface := state.solver
        solver.defineFun name.name [] smtTy term
        let state := state.addItem (.varDef name.name smtTy term)
        return (state, smtCtx, [])

  | Core.Statement.init name ty none _ =>
    match translateType E ty smtCtx with
    | .error msg =>
      -- Use a dummy expression for error reporting
      let dummyExpr : Core.Expression.Expr := .const Strata.SourceRange.none (.boolConst true)
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"init {name.name}", property := .assert, assumptions := [],
        obligation := dummyExpr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Type translation error: {toString msg}" }])
    | .ok (smtTy, smtCtx) =>
      let solver : SMT.SolverInterface := state.solver
      solver.declareFun name.name [] smtTy
      let state := state.addItem (.varDecl name.name smtTy)
      return (state, smtCtx, [])

  | Core.Statement.assert label expr md =>
    let (result, smtCtx) ← proveCheck state E label expr smtCtx md
    return (state, smtCtx, [result])

  | Core.Statement.cover label expr md =>
    let (result, smtCtx) ← coverCheck state E label expr smtCtx md
    return (state, smtCtx, [result])

  | .block _label stmts _ =>
    let state ← state.push
    let (state, smtCtx, results) ← processStatements state E stmts smtCtx
    let state ← state.pop
    return (state, smtCtx, results)

  | .funcDecl decl _ =>
    processFuncDecl state E decl smtCtx

  | _ =>
    let obligation : Imperative.ProofObligation Core.Expression := {
      label := "unknown"
      property := .assert
      assumptions := []
      obligation := .fvar Strata.SourceRange.none (Core.CoreIdent.unres "error") none
      metadata := .empty
    }
    return (state, smtCtx, [{ obligation, result := .implementationError "Unexpected statement" }])

/-- Process a list of CoreSMT statements sequentially -/
partial def processStatements (initialState : CoreSMTState) (E : Core.Env)
    (stmts : List Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) := do
  let accumulateErrors := initialState.config.accumulateErrors
  let mut state := initialState
  let mut smtCtx := smtCtx
  let mut results : List Core.VCResult := []
  for stmt in stmts do
    let (state', smtCtx', stmtResults) ← processStatement state E stmt smtCtx
    state := state'
    smtCtx := smtCtx'
    results := results ++ stmtResults
    -- If not accumulating errors and we got a failure, stop
    let shouldStop := !accumulateErrors && stmtResults.any (·.result != Core.Outcome.pass)
    if shouldStop then
      return (state, smtCtx, results)
  return (state, smtCtx, results)
end

end Strata.Core.CoreSMT
