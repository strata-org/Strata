/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.State
import Strata.Languages.Core.CoreSMT.ExprTranslator
import Strata.Languages.Core.CoreSMT.IsCoreSMT
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

/-- Proof check: check-sat of negation using push/pop
    TODO: Replace push/pop with check-sat-assuming for solver compatibility.
    This would enable solvers that don't support push/pop (e.g., some portfolio solvers).
    Instead of: push; assert (not term); check-sat; pop
    Use: check-sat-assuming ((not term)) -/
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
    state.solver.push
    state.solver.assert (Factory.not term)
    let decision ← state.solver.checkSat
    state.solver.pop
    let outcome := match decision with
      | .unsat   => Core.Outcome.pass
      | .sat     => Core.Outcome.fail
      | .unknown => Core.Outcome.unknown
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .assert, assumptions := [], obligation := expr, metadata := .empty
    }
    let smtResult := match decision with
      | .unsat => SMT.Result.unsat
      | .sat => SMT.Result.unknown
      | .unknown => SMT.Result.unknown
    return ({ obligation, smtResult, result := outcome }, smtCtx)

/-- Cover check: check-sat of expression using push/pop
    TODO: Replace push/pop with check-sat-assuming for solver compatibility. -/
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
    state.solver.push
    state.solver.assert term
    let decision ← state.solver.checkSat
    state.solver.pop
    let outcome := match decision with
      | .sat     => Core.Outcome.pass      -- Reachable
      | .unsat   => Core.Outcome.fail      -- Unreachable
      | .unknown => Core.Outcome.unknown
    let obligation : Imperative.ProofObligation Core.Expression := {
      label, property := .cover, assumptions := [], obligation := expr, metadata := .empty
    }
    let smtResult := match decision with
      | .sat => SMT.Result.unknown
      | .unsat => SMT.Result.unsat
      | .unknown => SMT.Result.unknown
    return ({ obligation, smtResult, result := outcome }, smtCtx)

mutual
/-- Process a single CoreSMT statement. Returns updated state, SMT context,
    and an optional check result (for assert/cover). -/
partial def processStatement (state : CoreSMTState) (E : Core.Env)
    (stmt : Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × Option Core.VCResult) := do
  if !isCoreSMTStmt stmt then
    let obligation : Imperative.ProofObligation Core.Expression := {
      label := "non-CoreSMT"
      property := .assert
      assumptions := []
      obligation := .fvar () (Core.CoreIdent.unres "error") none
      metadata := .empty
    }
    let result : Core.VCResult := { obligation, result := .implementationError "Statement not in CoreSMT subset" }
    return (state, smtCtx, some result)
  match stmt with
  | Core.Statement.assume _label expr _ =>
    match translateExprSafe E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := "assume", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, some { obligation, result := .implementationError s!"Translation error: {msg}" })
    | .ok (term, smtCtx) =>
      state.solver.assert term
      let state := state.addItem (.assumption term)
      return (state, smtCtx, none)

  | Core.Statement.init name ty (some expr) _ =>
    match translateExprSafe E expr smtCtx with
    | .error msg =>
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"init {name.name}", property := .assert, assumptions := [], obligation := expr, metadata := .empty
      }
      return (state, smtCtx, some { obligation, result := .implementationError s!"Translation error: {msg}" })
    | .ok (term, smtCtx) =>
      match translateTypeSafe E ty smtCtx with
      | .error msg =>
        let obligation : Imperative.ProofObligation Core.Expression := {
          label := s!"init {name.name}", property := .assert, assumptions := [], obligation := expr, metadata := .empty
        }
        return (state, smtCtx, some { obligation, result := .implementationError s!"Type translation error: {msg}" })
      | .ok (smtTy, smtCtx) =>
        state.solver.defineFun name.name [] smtTy term
        let state := state.addItem (.varDef name.name smtTy term)
        return (state, smtCtx, none)

  | Core.Statement.init name ty none _ =>
    match translateTypeSafe E ty smtCtx with
    | .error msg =>
      -- Use a dummy expression for error reporting
      let dummyExpr : Core.Expression.Expr := .const () (.boolConst true)
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"init {name.name}", property := .assert, assumptions := [], 
        obligation := dummyExpr, metadata := .empty
      }
      return (state, smtCtx, some { obligation, result := .implementationError s!"Type translation error: {toString msg}" })
    | .ok (smtTy, smtCtx) =>
      state.solver.declareFun name.name [] smtTy
      let state := state.addItem (.varDecl name.name smtTy)
      return (state, smtCtx, none)

  | Core.Statement.assert label expr _ =>
    let (result, smtCtx) ← proveCheck state E label expr smtCtx
    return (state.incResultCount, smtCtx, some result)

  | Core.Statement.cover label expr _ =>
    let (result, smtCtx) ← coverCheck state E label expr smtCtx
    return (state.incResultCount, smtCtx, some result)

  | .block _label stmts _ =>
    let state ← state.push
    let (state, smtCtx, results) ← processStatements state E stmts smtCtx
    let state ← state.pop
    -- Return the last check result if any
    return (state, smtCtx, results.getLast?)

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
      let dummyExpr : Core.Expression.Expr := .const () (.boolConst true)
      let obligation : Imperative.ProofObligation Core.Expression := {
        label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
        obligation := dummyExpr, metadata := .empty
      }
      return (state, smtCtx, some { obligation, result := .implementationError s!"Type translation error: {toString msg}" })
    | .ok inputTypes =>
      match translateTypeSafe E decl.output smtCtx with
      | .error msg =>
        let dummyExpr : Core.Expression.Expr := .const () (.boolConst true)
        let obligation : Imperative.ProofObligation Core.Expression := {
          label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
          obligation := dummyExpr, metadata := .empty
        }
        return (state, smtCtx, some { obligation, result := .implementationError s!"Output type translation error: {toString msg}" })
      | .ok (outTy, smtCtx) =>
      -- Add function to smtCtx so expression translator can find it
      let ufArgs := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) =>
        TermVar.mk name.name smtTy
      let uf : UF := { id := decl.name.name, args := ufArgs, out := outTy }
      let smtCtx := smtCtx.addUF uf
      match decl.body with
      | none =>
        state.solver.declareFun decl.name.name inputTypes outTy
        let state := state.addItem (.funcDecl decl.name.name inputTypes outTy)
        return (state, smtCtx, none)
      | some body =>
        match translateExprSafe E body smtCtx with
        | .error msg =>
          let obligation : Imperative.ProofObligation Core.Expression := {
            label := s!"funcDecl {decl.name.name}", property := .assert, assumptions := [], 
            obligation := body, metadata := .empty
          }
          return (state, smtCtx, some { obligation, result := .implementationError s!"Body translation error: {msg}" })
        | .ok (bodyTerm, smtCtx) =>
          let args := decl.inputs.zip inputTypes |>.map fun ((name, _), smtTy) => (name.name, smtTy)
          state.solver.defineFun decl.name.name args outTy bodyTerm
          let state := state.addItem (.funcDef decl.name.name args outTy bodyTerm)
          return (state, smtCtx, none)

  | _ =>
    let obligation : Imperative.ProofObligation Core.Expression := {
      label := "unknown"
      property := .assert
      assumptions := []
      obligation := .fvar () (Core.CoreIdent.unres "error") none
      metadata := .empty
    }
    return (state, smtCtx, some { obligation, result := .implementationError "Unexpected statement" })

/-- Process a list of CoreSMT statements sequentially -/
partial def processStatements (state : CoreSMTState) (E : Core.Env)
    (stmts : List Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × List Core.VCResult) := do
  let mut state := state
  let mut smtCtx := smtCtx
  let mut results : List Core.VCResult := []
  for stmt in stmts do
    let (state', smtCtx', result) ← processStatement state E stmt smtCtx
    state := state'
    smtCtx := smtCtx'
    match result with
    | some r => results := results ++ [r]
    | none => pure ()
    -- If not accumulating errors and we got a failure, stop
    if !state.config.accumulateErrors then
      match result with
      | some r =>
        if r.result != Core.Outcome.pass then
          return (state, smtCtx, results)
      | none => pure ()
  return (state, smtCtx, results)
end

end Strata.Core.CoreSMT
