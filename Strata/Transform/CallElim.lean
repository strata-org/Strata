/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.Languages.Core.PipelinePhase

/-! # Call Elimination Transformation -/

public section

namespace Core
namespace CallElim

open Core.Transform

/-- Label prefix for call-elimination assert statements. -/
def callElimAssertPrefix : String := "callElimAssert_"

/-- Label prefix for call-elimination assume statements. -/
def callElimAssumePrefix : String := "callElimAssume_"

/--
The main call elimination transformation algorithm on a single command.
The returned result is a sequence of statements
-/
def callElimCmd (cmd: Command)
  : CoreTransformM (Option (List Statement)) := do
    match cmd with
      | .call lhs procName args md =>

        let some p := (← get).currentProgram | throw "program not available"

        let some proc := Program.Procedure.find? p procName | throw s!"Procedure {procName} not found in program"

        -- Identify output parameters that reference globals for "old g" handling.
        -- Since modifies variables are now output parameters, we check which outputs
        -- are global variables referenced via "old g" in postconditions.
        let postExprs := proc.spec.postconditions.values.map Procedure.Check.expr
        let oldVars := lhs.filter fun g =>
          isGlobalVar p g &&
          postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any (fun (id, _) => id == CoreIdent.mkOld g.name))

        let genArgTrips := genArgExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs) args
        let argTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Expr)
            ← genArgTrips

        let genOutTrips := genOutExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs) lhs
        let outTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOutTrips

        -- Generate fresh variables for "old g" (one per modified global in lhs).
        let genOldTrips := genOldExprIdentsTrip p oldVars
        let oldTripsRaw
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOldTrips
        let oldGVars := oldVars.map (fun g => CoreIdent.mkOld g.name)
        let oldTrips := oldTripsRaw.zip oldGVars |>.map fun (((fresh, ty), _orig), oldG) =>
          ((fresh, ty), oldG)

        -- initialize/declare the newly generated variables
        let argInit := createInits argTrips md
        let outInit := createInitVars outTrips md
        let oldInit := createInitVars oldTripsRaw md

        -- Substitute "old g" in postconditions:
        -- For globals NOT in lhs (not being modified): old g == g at the call site.
        let unmodifiedOldSubst : Map Expression.Ident Expression.Expr :=
          p.decls.filterMap fun d => match d with
            | .var name _ _ _ =>
              let oldVar := CoreIdent.mkOld name.name
              if !lhs.contains name &&
                 postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any
                   (fun (id, _) => id == oldVar))
              then some (oldVar, createFvar name)
              else none
            | _ => none
        let oldSubst := createOldVarsSubst oldTrips ++ unmodifiedOldSubst

        let postconditions : List Expression.Expr := proc.spec.postconditions.values.map
          (fun c => Lambda.LExpr.substFvars c.expr oldSubst)

        -- generate havoc for return variables (which now includes modified globals)
        let havocs := createHavocs lhs md

        -- construct substitutions for argument and return
        let arg_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.inputs).zip $ createFvars argTrips.unzip.fst.unzip.fst
        let ret_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.outputs).zip $ createFvars lhs

        -- construct assumes and asserts in place of pre/post conditions
        let asserts ← createAsserts (proc.spec.preconditions.filter (fun (_, check) => check.attr != .Free))
                        (arg_subst ++ ret_subst)
                        md
                        callElimAssertPrefix
        let assumes ← createAssumes
                        (Procedure.Spec.updateCheckExprs postconditions proc.spec.postconditions)
                        (arg_subst ++ ret_subst)
                        md
                        callElimAssumePrefix
        -- Update cached CallGraph
        let σ ← get
        match σ.cachedAnalyses.callGraph, σ.currentProcedureName with
        | .some cg, .some callerName =>
          let cg' ← cg.decrementEdge callerName procName
          set { σ with
              cachedAnalyses := { σ.cachedAnalyses with
                callGraph := .some cg'}}
        | .some _, .none =>
          set { σ with
              cachedAnalyses := { σ.cachedAnalyses with callGraph := .none }}
        | _, _ => set σ

        return argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes
      | _ => return .none

/-- Call Elimination for an entire program by walking through all procedure
bodies -/
def callElim' (p : Program) : CoreTransformM (Bool × Program) :=
  runProgram (targetProcList := .none) callElimCmd p

end CallElim

/-- Call-elimination pipeline phase: the transform replaces procedure calls
    with assert/havoc/assume sequences. If the obligation's path includes
    labels from call elimination, the callee body was replaced by its
    contract, which is an over-approximation. -/
def callElimPipelinePhase : PipelinePhase where
  transform := CallElim.callElim'
  phase.name := "CallElim"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation CallElim.callElimAssumePrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving

end Core

-- NB: workaround for the fact that Core is both a module and a dialect.
def coreCallElimCmd := Core.CallElim.callElimCmd

end -- public section
