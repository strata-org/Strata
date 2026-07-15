/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

/-! # Call Elimination Transformation -/

public section

namespace Core
namespace CallElim

open Core.Transform

/-- Statistics keys tracked by the call elimination transformation. -/
inductive Stats where
  | visitedCalls

#derive_prefixed_toString Stats "CallElim"

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
      | .call procName callArgs md =>
        let lhs := CallArg.getLhs callArgs
        let args := CallArg.getInputExprs callArgs
        incrementStat s!"{Stats.visitedCalls}"

        let some p := (← get).currentProgram | throw (Strata.DiagnosticModel.fromMessage "program not available")

        let some proc := Program.Procedure.find? p procName | throw (Strata.DiagnosticModel.fromFormat f!"Procedure {procName} not found in program")

        -- Per-call-site type-variable freshening for polymorphic procedures.
        -- The inlined contract carries the callee's source type vars (`x : T`). Copied
        -- verbatim, the SAME `T` is shared across call sites, so two calls at different
        -- concrete types (`idp(5)`, `idp(true)`) force `T` to unify with both `int` and
        -- `bool` — a whole-program type-check abort masking unrelated obligations. Rename
        -- the type vars to globally-fresh ones per call site. For a monomorphic callee
        -- (`typeArgs = []`) the substitution is empty and the applications below are no-ops.
        let tySubst ← freshenTypeArgsSubst proc.header.typeArgs
        let freshTy (ty : Lambda.LMonoTy) : Lambda.LMonoTy := Lambda.LMonoTy.subst tySubst ty
        let freshExpr (e : Expression.Expr) : Expression.Expr := Lambda.LExpr.applySubst e tySubst

        -- Identify output parameters that also appear as input parameters
        -- and are referenced via "old" in postconditions.
        let postExprs := proc.spec.postconditions.values.map Procedure.Check.expr
        let inputNames := proc.header.inputs.keys
        let outputNames := proc.header.outputs.keys
        -- Variables needing old handling: input/output params with old refs.
        let oldVars := lhs.filter fun g =>
          (inputNames.contains g && outputNames.contains g) && -- Inout params
          postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any (fun (id, _) => id == CoreIdent.mkOld g.name))

        let freshInputs := proc.header.inputs.map (fun (id, ty) => (id, freshTy ty))
        let freshOutputs := proc.header.outputs.map (fun (id, ty) => (id, freshTy ty))

        let genArgTrips := genArgExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy freshInputs) args
        let argTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Expr)
            ← genArgTrips

        let genOutTrips := genOutExprIdentsTrip (Lambda.LMonoTySignature.toTrivialLTy freshOutputs) lhs
        let outTrips
            : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
            ← genOutTrips

        -- Generate fresh variables for "old g" (one per modified variable in lhs).
        -- For input/output parameters, look up types from the callee's inputs.
        let genOldIdents ← genOldExprIdents oldVars
        let oldTys ← oldVars.mapM fun id => do
          match proc.header.inputs.find? id with
          | some ty => pure (Lambda.LTy.forAll [] (freshTy ty))
          | none => throw (Strata.DiagnosticModel.fromFormat f!"failed to find type for {Std.format id}")
        let oldTripsRaw := (genOldIdents.zip oldTys).zip oldVars
        let oldGVars := oldVars.map (fun g => CoreIdent.mkOld g.name)
        let oldTrips := oldTripsRaw.zip oldGVars |>.map fun (((fresh, ty), _orig), oldG) =>
          ((fresh, ty), oldG)

        -- initialize/declare the newly generated variables
        let argInit := createInits argTrips md
        let outInit := createInitVars outTrips md
        let oldInit := createInitVars oldTripsRaw md

        -- Substitute "old g" in postconditions:
        -- For input-only parameters (not in outputs): old g == the argument value.
        let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
          (proc.header.inputs.keys.zip args).filterMap fun (paramId, argExpr) =>
            let oldVar := CoreIdent.mkOld paramId.name
            if !outputNames.contains paramId &&
               postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any
                 (fun (id, _) => id == oldVar))
            then some (oldVar, argExpr)
            else none
        let oldSubst := createOldVarsSubst oldTrips ++ inputOnlyOldSubst

        -- Freshen type variables in the postcondition expressions (binder/op/fvar
        -- annotations) with the same per-call-site substitution used for the
        -- temp types above, then substitute the "old" actuals. `freshExpr` only
        -- rewrites type annotations; `substFvars` only rewrites fvar leaves — they
        -- touch disjoint slots, so the order is immaterial.
        let postconditions : List Expression.Expr := proc.spec.postconditions.values.map
          (fun c => Lambda.LExpr.substFvars (freshExpr c.expr) oldSubst)

        -- generate havoc for output variables
        let havocs := createHavocs lhs md

        -- construct substitutions for argument and return
        let arg_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.inputs).zip $ createFvars argTrips.unzip.fst.unzip.fst
        let ret_subst : List (Expression.Ident × Expression.Expr)
                      := (ListMap.keys proc.header.outputs).zip $ createFvars lhs

        -- construct assumes and asserts in place of pre/post conditions.
        -- Freshen type variables in the precondition expressions with the same
        -- per-call-site substitution (no-op for monomorphic callees).
        let freshPreconditions := (proc.spec.preconditions.filter (fun (_, check) => check.attr != .Free)).map
          (fun (l, check) => (l, { check with expr := freshExpr check.expr }))
        let asserts ← createAsserts freshPreconditions
                        (arg_subst ++ ret_subst)
                        md
                        callElimAssertPrefix
        -- For postconditions, filter out input substitutions for inout params
        -- (already covered by ret_subst with post-call values).
        let arg_subst_filtered := arg_subst.filter fun (id, _) =>
          !(ListMap.keys proc.header.outputs).contains id
        let assumes ← createAssumes
                        (Procedure.Spec.updateCheckExprs postconditions proc.spec.postconditions)
                        (ret_subst ++ arg_subst_filtered)
                        md
                        callElimAssumePrefix
        -- Update cached CallGraph
        let σ ← get
        match σ.cachedAnalyses.callGraph, σ.currentProcedureName with
        | .some cg, .some callerName =>
          let cg' ← (cg.decrementEdge callerName procName).mapError Strata.DiagnosticModel.fromMessage
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
bodies. -/
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
  phase.getAssertDescription label :=
    if label.startsWith CallElim.callElimAssertPrefix then
      let stripped := label.drop CallElim.callElimAssertPrefix.length |>.toString
      let parts := stripped.splitOn "_"
      let originalLabel := if parts.length > 1 then
        "_".intercalate (parts.dropLast)
      else stripped
      if originalLabel == "requires" || originalLabel.startsWith "requires_" then
        some "precondition"
      else
        some s!"precondition '{originalLabel}'"
    else none

end Core

-- NB: workaround for the fact that Core is both a module and a dialect.
def coreCallElimCmd := Core.CallElim.callElimCmd

end -- public section
