/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.MarkerLabels
import Strata.Languages.Core.NameSets
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.CallWF
import Strata.DL.Lambda.LExprType

/-! # Call Elimination Transformation -/

public section

namespace Core
namespace CallElim

open Core.Transform
open Imperative

/-- Statistics keys tracked by the call elimination transformation. -/
inductive Stats where
  | visitedCalls

#derive_prefixed_toString Stats "CallElim"

/-- Prefix of the type variables call elimination uses to instantiate a callee's contract.
    Kept as a literal copy in `Lambda.reservedNamePrefixes`, so type checking still
    rejects or renames program names that use it. -/
@[expose] def callElimTyPrefix : String := "$__cety"

/-- Label prefix for call-elimination assert statements. -/
def callElimAssertPrefix : String := "callElimAssert_"

/--
The call elimination kernel: replace the call `procName(callArgs)` (with call-site metadata `md`)
by the callee's contract, as a flat sequence of commands: `init`s for the argument, output and
`old` temporaries, `assert`s of the (non-free) preconditions, `havoc`s of the call's outputs, and
`assume`s of the postconditions. It introduces no control flow, so the result can replace the
call in a structured body or in a CFG block alike. `vt` gives the declared types of the
variables in scope at the call, `taken` the type names the callee's opaque types must avoid,
and `takenVars` the names the temporaries avoid: the program's variable names
(`Program.varNames`), since a temporary named like a program variable would overwrite it, and,
as a precaution, its declaration names, since the SMT encoding names a free variable and a
nullary function by their own names.
-/
def callElimCall (taken takenVars : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (procName : String)
    (tyArgs : Option (List Expression.Ty)) (callArgs : List (CallArg Expression))
    (md : Imperative.MetaData Expression) : CoreTransformM (List Command) := do
  let lhs := CallArg.getLhs callArgs
  incrementStat s!"{Stats.visitedCalls}"

  let some p := (← get).currentProgram | throw (md.toDiagnostic "program not available")

  let some proc := Program.Procedure.find? p procName
    | throw (wellFormedCallsBreach "Call elimination" md
        (undeclaredProcedureMessage procName))
  if let some msg := callArgsError? procName proc callArgs then
    throw (wellFormedCallsBreach "Call elimination" md msg)

  -- Instantiates the callee's contract at this call's type instance.
  let tySubst ←
    callTypeSubstOrBreach "Call elimination" md callElimTyPrefix taken vt proc callArgs tyArgs
  let instantiatedTy (ty : Lambda.LMonoTy) : Lambda.LMonoTy := Lambda.LMonoTy.subst tySubst ty
  let instantiatedExpr (e : Expression.Expr) : Expression.Expr :=
    Lambda.LExpr.applyTypeSubst e tySubst

  -- The callee's signature with type variables instantiated. All later
  -- reads go through these (keys are unchanged by instantiation), so
  -- `proc.header.inputs`/`.outputs` appear only here.
  let instantiatedInputs : @Lambda.LMonoTySignature Unit :=
    proc.header.inputs.map (fun (id, ty) => (id, instantiatedTy ty))
  let instantiatedOutputs : @Lambda.LMonoTySignature Unit :=
    proc.header.outputs.map (fun (id, ty) => (id, instantiatedTy ty))
  let args := typedInputExprs instantiatedInputs callArgs

  -- Identify output parameters that also appear as input parameters
  -- and are referenced via "old" in postconditions. (Safe to scan the
  -- uninstantiated exprs: instantiation rewrites only type annotations —
  -- `replaceUserProvidedType` — so free term variables are unchanged.)
  let postExprs := proc.spec.postconditions.values.map Imperative.Check.expr
  let inputNames := instantiatedInputs.keys
  let outputNames := instantiatedOutputs.keys
  -- Inout params referenced via "old" in a postcondition, paired as
  -- (caller argument variable, callee parameter name). The variable is the
  -- `inout` argument at the parameter's input position, whose value on entry
  -- is the parameter's `old` value. The caller variable drives the
  -- snapshot init; the callee parameter drives the type lookup and the
  -- "old" substitution key that appears in the spec.
  let oldPairs := (inputNames.zip (CallArg.inputArgs callArgs)).filterMap
    fun (param, arg) => match arg with
      | .inoutArg v =>
        if outputNames.contains param && -- Inout param (an input that is also an output)
            postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any
              (fun (id, _) => id == CoreIdent.mkOld param.name)) then
          some (v, param)
        else none
      | _ => none
  let oldVars := oldPairs.map (·.1)

  let genArgTrips :=
    genArgExprIdentsTrip takenVars (Lambda.LMonoTySignature.toTrivialLTy instantiatedInputs) args
  let argTrips
      : List ((Expression.Ident × Expression.Ty) × Expression.Expr)
      ← genArgTrips

  let genOutTrips :=
    genOutExprIdentsTrip takenVars (Lambda.LMonoTySignature.toTrivialLTy instantiatedOutputs) lhs
  let outTrips
      : List ((Expression.Ident × Expression.Ty) × Expression.Ident)
      ← genOutTrips

  -- Generate fresh variables for "old g" (one per modified variable in lhs).
  -- For input/output parameters, look up types from the callee's inputs.
  let oldParams := oldPairs.map (·.2)
  let genOldIdents ← genOldExprIdents takenVars oldVars
  let oldTys ← oldParams.mapM fun param => do
    match instantiatedInputs.find? param with
    | some ty => pure (Lambda.LTy.forAll [] ty)
    | none => throw (Strata.Message.fromFormat f!"failed to find type for {Std.format param}")
  let oldTripsRaw := (genOldIdents.zip oldTys).zip oldVars
  let oldGVars := oldParams.map (fun p => CoreIdent.mkOld p.name)
  let oldTrips := (genOldIdents.zip oldTys).zip oldGVars

  -- initialize/declare the newly generated variables
  let argInit := createInitCmds argTrips md
  let outInit := createInitVarCmds outTrips md
  let oldInit := createInitVarCmds oldTripsRaw md

  -- Substitute "old g" in postconditions:
  -- For input-only parameters (not in outputs): old g == the argument value.
  let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
    (instantiatedInputs.keys.zip args).filterMap fun (paramId, argExpr) =>
      let oldVar := CoreIdent.mkOld paramId.name
      if !outputNames.contains paramId &&
         postExprs.any (fun e => Lambda.LExpr.freeVars e |>.any
           (fun (id, _) => id == oldVar))
      then some (oldVar, argExpr)
      else none
  let oldSubst := createOldVarsSubst oldTrips ++ inputOnlyOldSubst

  -- Instantiate type variables in the postcondition expressions (binder/op/
  -- fvar annotations) with the same per-call-site substitution used for the
  -- temp types above, then substitute the "old" actuals. The order matters:
  -- instantiation must happen first, because `substFvars` splices in caller-side
  -- expressions (`inputOnlyOldSubst` maps `old param` to the actual argument)
  -- whose type annotations — e.g. a caller's own type variable that happens
  -- to share the callee's spelling — must not be renamed.
  let postconditions : List Expression.Expr := proc.spec.postconditions.values.map
    (fun c => Lambda.LExpr.substFvars (instantiatedExpr c.expr) oldSubst)

  -- generate havoc for output variables
  let havocs := createHavocCmds lhs md

  -- construct substitutions for argument and return
  let arg_subst : List (Expression.Ident × Expression.Expr)
                := (ListMap.keys instantiatedInputs).zip $ createTypedFvars argTrips.unzip.fst
  let ret_subst : List (Expression.Ident × Expression.Expr)
                := (ListMap.keys instantiatedOutputs).zip $
                    createTypedFvars (outTrips.map fun ((_, ty), x) => (x, ty))

  -- construct assumes and asserts in place of pre/post conditions.
  -- Instantiate type variables in the precondition expressions with the same
  -- per-call-site substitution (no-op for monomorphic callees).
  let instantiatedPreconditions :=
    (proc.spec.preconditions.filter (fun (_, check) => check.attr != .Free)).map
      (fun (l, check) => (l, { check with expr := instantiatedExpr check.expr }))
  let asserts ← createAssertCmds instantiatedPreconditions
                  (arg_subst ++ ret_subst)
                  md
                  callElimAssertPrefix
  -- For postconditions, filter out input substitutions for inout params
  -- (already covered by ret_subst with post-call values).
  let arg_subst_filtered := arg_subst.filter fun (id, _) =>
    !(ListMap.keys instantiatedOutputs).contains id
  let assumes ← createAssumeCmds
                  (Procedure.Spec.updateCheckExprs postconditions proc.spec.postconditions)
                  (ret_subst ++ arg_subst_filtered)
                  md
                  (if proc.body.isOpaque then callElimPostPrefix else callElimAssumePrefix)
  -- Update cached CallGraph
  let σ ← get
  match σ.cachedAnalyses.callGraph, σ.currentProcedureName with
  | .some cg, .some callerName =>
    let cg' ← (cg.decrementEdge callerName procName).mapError Strata.Message.fromString
    set { σ with
        cachedAnalyses := { σ.cachedAnalyses with
          callGraph := .some cg'}}
  | .some _, .none =>
    set { σ with
        cachedAnalyses := { σ.cachedAnalyses with callGraph := .none }}
  | _, _ => set σ

  -- A call that havocs outputs of a callee that is not opaque and has no postconditions gets one
  -- marked assumption `true` after the havocs (`callElimHavocPrefix`), as if the callee had
  -- `ensures true`, so that a path through the havocked outputs carries a call-elimination
  -- marker. A call without outputs havocs
  -- nothing and gets none, and so does a call to an opaque callee: callers know it only through
  -- its contract, which is the call semantics.
  let assumes ← if assumes.isEmpty && !proc.body.isOpaque && !lhs.isEmpty then do
      let havocMark ← genIdent "call" (fun s => s!"{callElimHavocPrefix}{s}")
      pure [.cmd (.assume havocMark.toPretty (Lambda.LExpr.true default) md)]
    else pure assumes
  return argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes

/-- Call elimination on a single command: a `call` is replaced by its callee's contract
    (`callElimCall`); every other command is declined (`.none`). -/
def callElimCommand (taken takenVars : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (c : Command) :
    CoreTransformM (Option (List Command)) :=
  match c with
  | .call procName tyArgs callArgs md =>
    .some <$> callElimCall taken takenVars vt procName tyArgs callArgs md
  | _ => return .none

/--
Call elimination on a single statement, given the declared types `vt` of the variables in scope,
the type names `taken` the opaque types of a call must avoid, and the variable names
`takenVars` its temporaries must avoid: a `call` statement is
rewritten by `callElimCommand`; every other statement returns `.none` so that `runStmtsRecTyped`
traverses into it.
-/
def callElimCmd (taken takenVars : Std.HashSet String) (vt : TypeSpec.TypeScopes) (s : Statement)
  : CoreTransformM (Option (List Statement)) := do
    match s with
      | .cmd c => return (← callElimCommand taken takenVars vt c).map (·.map .cmd)
      | _ => return .none

/-- Call Elimination for an entire program by walking through all procedure
bodies, structured ones and the blocks of CFG ones. -/
def callElim' (p : Program) : CoreTransformM (Bool × Program) :=
  let taken := p.typeNamesWithPrefix callElimTyPrefix
  let takenVars := p.varNames.insertMany (p.declaredNames ++ p.funcNames)
  declareGeneratedTypes callElimTyPrefix taken
    (runProgramTyped (targetProcList := .none) (callElimCmd taken takenVars) p
      (cfgCmd := some (callElimCommand taken takenVars)))

end CallElim

/-- Call-elimination pipeline phase: the transform replaces procedure calls
    with assert/havoc/assume sequences, in structured bodies and in CFG blocks. If the
    obligation's path includes labels from call elimination, the callee body was replaced by
    its contract, which is an over-approximation. A call to an opaque procedure (`Body.isOpaque`)
    is not: its contract is its call semantics, so its postcondition assumptions carry
    `callElimPostPrefix`, which is not a marker. A marker of a havoc (`callElimHavocPrefix`) has
    the condition `true`, so where `--vcgen wp` keeps it under its reach condition
    (`markerGuards`), a counterexample that falsifies that condition does not pass the call; a
    postcondition assumption is a marker on every path that keeps it. The `init`s that replace a call in a CFG block on a
    cycle are rejected by `CFG.typeCheck` (`checkNoLoopInits`) if the body is checked again. -/
def callElimPipelinePhase : PipelinePhase where
  transform p := do
    rejectMarkerLabels "call elimination" CallElim.callElimAssumePrefix p
    rejectMarkerLabels "call elimination" CallElim.callElimHavocPrefix p
    CallElim.callElim' p
  phase.name := "callElim"
  phase.validationPrefixes := [CallElim.callElimAssumePrefix]
  -- A call to a callee without postconditions becomes a bare `havoc` of its outputs.
  phase.leavesUnmarkedAbstractions := true
  phase.getValidation obligation :=
    markerValidation obligation [CallElim.callElimAssumePrefix, CallElim.callElimHavocPrefix]
      (guarded := [CallElim.callElimHavocPrefix])
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
  -- Two facts are unclaimed. `staticSingleAssignment`, because the replacement
  -- havocs the call's outputs. `noBetaRedexes`, because instantiating the
  -- callee's contract can leave an application of an abstraction behind when a
  -- function-typed formal is given one.
  -- `wellFormedCalls`, because the replacement pairs each argument with the
  -- callee's parameter at its position.
  -- `typeAnnotated` is required and preserved: the replacement uses the annotated variables and
  -- argument expressions of the call.
  requires := factSet![.wellFormedCalls, .typeAnnotated]
  establishes := factSet![.noCalls]
  -- `wellFormedCalls` holds of the output, which has no calls.
  preserves := factSet![.wellFormedCalls, .noCFGBodies, .noLoops, .noLoopInvariants,
                      .noLoopMeasures, .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated, .exitsCovered, .noCFGCycles]

end Core

-- NB: workaround for the fact that Core is both a module and a dialect.
def coreCallElimCmd := Core.CallElim.callElimCmd

end -- public section
