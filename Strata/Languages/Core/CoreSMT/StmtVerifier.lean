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

/-- Helper: translate an expression to SMT term, returning error on failure -/
private def translateExprSafe (E : Core.Env) (e : Core.Expression.Expr)
    (ctx : Core.SMT.Context) : Except Std.Format (Term × Core.SMT.Context) :=
  translateExpr E e ctx

/-- Helper: translate a type to SMT TermType, returning error on failure -/
private def translateTypeSafe (E : Core.Env) (ty : Core.Expression.Ty)
    (ctx : Core.SMT.Context) : Except Std.Format (TermType × Core.SMT.Context) :=
  translateType E ty ctx

/-- Proof check: check-sat of negation using check-sat-assuming -/
private def proveCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) : IO (Core.VCResult × Core.SMT.Context) := do
  match translateExprSafe E expr smtCtx with
  | .error msg =>
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .assert, assumptions := [], obligation := expr, metadata := .empty
    }
    return ({ obligation, result := .implementationError s!"Translation error: {msg}" }, smtCtx)
  | .ok (term, smtCtx) =>
    let solver : SMT.SolverInterface := state.solver
    let decision ← solver.checkSatAssuming [Factory.not term]
    let outcome := match decision with
      | SMT.Decision.unsat   => Core.Outcome.pass
      | SMT.Decision.sat     => Core.Outcome.fail
      | SMT.Decision.unknown => Core.Outcome.unknown
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .assert, assumptions := [], obligation := expr, metadata := .empty
    }
    let smtResult := match decision with
      | SMT.Decision.unsat => SMT.Result.unsat
      | SMT.Decision.sat => SMT.Result.unknown
      | SMT.Decision.unknown => SMT.Result.unknown
    
    -- Add diagnosis for failures
    let diagnosis ← if outcome != .pass then
      let diagResult ← diagnoseFailure state E expr false smtCtx
      let failedExprs := diagResult.diagnosedFailures.map (·.expression)
      let isRefuted := diagResult.diagnosedFailures.any (·.isRefuted)
      pure (some { isRefuted, failedSubExpressions := failedExprs, diagnosedFailures := diagResult.diagnosedFailures })
    else
      pure none
    
    return ({ obligation, smtResult, result := outcome, diagnosis }, smtCtx)

/-- Cover check: check-sat of expression using check-sat-assuming -/
private def coverCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) : IO (Core.VCResult × Core.SMT.Context) := do
  match translateExprSafe E expr smtCtx with
  | .error msg =>
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .cover, assumptions := [], obligation := expr, metadata := .empty
    }
    return ({ obligation, result := .implementationError s!"Translation error: {msg}" }, smtCtx)
  | .ok (term, smtCtx) =>
    let solver : SMT.SolverInterface := state.solver
    let decision ← solver.checkSatAssuming [term]
    let outcome := match decision with
      | SMT.Decision.sat     => Core.Outcome.pass      -- Reachable
      | SMT.Decision.unsat   => Core.Outcome.fail      -- Unreachable
      | SMT.Decision.unknown => Core.Outcome.unknown
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .cover, assumptions := [], obligation := expr, metadata := .empty
    }
    let smtResult := match decision with
      | SMT.Decision.sat => SMT.Result.unknown
      | SMT.Decision.unsat => SMT.Result.unsat
      | SMT.Decision.unknown => SMT.Result.unknown
    
    -- Add diagnosis for failures (reach checks)
    let diagnosis ← if outcome != .pass then
      let diagResult ← diagnoseFailure state E expr true smtCtx  -- true for reach check
      let failedExprs := diagResult.diagnosedFailures.map (·.expression)
      let isRefuted := diagResult.diagnosedFailures.any (·.isRefuted)
      pure (some { isRefuted, failedSubExpressions := failedExprs })
    else
      pure none
    
    return ({ obligation, smtResult, result := outcome, diagnosis }, smtCtx)

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
    match translateExprSafe E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := "assume", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Translation error: {msg}" }])
    | .ok (term, smtCtx) =>
      let solver : SMT.SolverInterface := state.solver
      solver.assert term
      let state := state.addItem (.assumption term)
      return (state, smtCtx, [])

  | Core.Statement.init name ty (some expr) _ =>
    match translateExprSafe E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"init {name.name}", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Translation error: {msg}" }])
    | .ok (term, smtCtx) =>
      match translateTypeSafe E ty smtCtx with
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
    match translateTypeSafe E ty smtCtx with
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

  | Core.Statement.assert label expr _ =>
    let (result, smtCtx) ← proveCheck state E label expr smtCtx
    return (state, smtCtx, [result])

  | Core.Statement.cover label expr _ =>
    let (result, smtCtx) ← coverCheck state E label expr smtCtx
    return (state, smtCtx, [result])

  | .block _label stmts _ =>
    let state ← state.push
    let (state, smtCtx, results) ← processStatements state E stmts smtCtx
    let state ← state.pop
    return (state, smtCtx, results)

  | .funcDecl decl _ =>
    -- Collect type translation results using foldlM
    let result ← decl.inputs.foldlM (fun (acc : Except Std.Format (List TermType)) (_, ty) => do
      match acc with
      | .error msg => return .error msg
      | .ok types =>
        match translateTypeSafe E ty smtCtx with
        | .error msg => return .error msg
        | .ok (smtTy, _) => return .ok (types ++ [smtTy])
    ) (.ok [])
    
    match result with
    | .error msg =>
      let dummyExpr : Core.Expression.Expr := .const Strata.SourceRange.none (.boolConst true)
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
        obligation := dummyExpr, metadata := .empty
      }
      return (state, smtCtx, [{ obligation, result := .implementationError s!"Type translation error: {toString msg}" }])
    | .ok inputTypes =>
      match translateTypeSafe E decl.output smtCtx with
      | .error msg =>
        let dummyExpr : Core.Expression.Expr := .const Strata.SourceRange.none (.boolConst true)
        let obligation : Imperative.ProofObligation Core.Expression := {
          label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
          obligation := dummyExpr, metadata := .empty
        }
        return (state, smtCtx, [{ obligation, result := .implementationError s!"Output type translation error: {toString msg}" }])
      | .ok (outTy, smtCtx) =>
      -- Add function to smtCtx so expression translator can find it
      let ufArgs := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) =>
        TermVar.mk name.name smtTy
      let uf : UF := { id := decl.name.name, args := ufArgs, out := outTy }
      let smtCtx := smtCtx.addUF uf
      match decl.body with
      | none =>
        let solver : SMT.SolverInterface := state.solver
        solver.declareFun decl.name.name inputTypes outTy
        let state := state.addItem (.funcDecl decl.name.name inputTypes outTy)
        return (state, smtCtx, [])
      | some body =>
        match translateExprSafe E body smtCtx with
        | .error msg =>
          let obligation : Imperative.ProofObligation Core.Expression := {
            label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
            obligation := body, metadata := .empty
          }
          return (state, smtCtx, [{ obligation, result := .implementationError s!"Body translation error: {msg}" }])
        | .ok (bodyTerm, smtCtx) =>
          let args := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) => (name.name, smtTy)
          let solver : SMT.SolverInterface := state.solver
          solver.defineFun decl.name.name args outTy bodyTerm
          let state := state.addItem (.funcDef decl.name.name args outTy bodyTerm)
          return (state, smtCtx, [])

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
