/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.GlobalVarAnalysis
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.LiftInstanceProcedures
import Strata.Languages.Laurel.EliminateExceptions
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.HeapParameterizationConstants
-- For the pass-ordering metadata below: this pass must run after the heap trio and
-- before the contract pass.
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.ContractPass

/-!
# Global Parameterization

Lowers `Program.staticFields` to implicit procedure parameters. Readers receive
an input; writers receive an inout parameter so conditional writes preserve the
incoming value. Effects propagate through calls, and globals follow declaration
order in signatures and call sites.

Calls pass globals as leading arguments and receive written globals as leading
assignment targets. The pass clears `staticFields` after a successful rewrite.

-/

public section

namespace Strata.Laurel


private structure GlobalTransformState where
  globalOrder  : List Identifier
  globalType   : Std.HashMap Nat HighTypeMd
  globalInit   : Std.HashMap Nat StmtExprMd := {}
  readers      : Std.HashMap Nat (Std.HashSet Nat)
  writers      : Std.HashMap Nat (Std.HashSet Nat)
  localGlobals : Std.HashMap Nat Identifier := {}
  usedNames    : Std.HashSet String := {}
  freshCounter : Nat := 0
  diagnostics  : List Message := []

private abbrev GlobalTransformM := StateM GlobalTransformState

private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := { val := e, source }
private def mkVarMd (v : Variable) (source : FileRange) : VariableMd := { val := v, source }

private def firstFreshName (mkCandidate : Nat → String) : GlobalTransformM Identifier := do
  let attempts := (← get).usedNames.size + 1
  for _ in [0:attempts] do
    let s ← get
    let candidate := mkCandidate s.freshCounter
    set { s with freshCounter := s.freshCounter + 1 }
    if !s.usedNames.contains candidate then
      modify fun state => { state with usedNames := state.usedNames.insert candidate }
      return candidate
  panic! "firstFreshName: exhausted distinct candidates without finding a fresh name"

private def freshName (base : String) : GlobalTransformM Identifier :=
  firstFreshName fun counter =>
    if counter == 0 then base else s!"{base}_{counter}"

private def freshVarName : GlobalTransformM Identifier :=
  firstFreshName fun counter => s!"$g_tmp{counter}"

private def collectBoundNames (proc : Procedure) : Std.HashSet String :=
  let initial := (proc.inputs ++ proc.outputs).foldl
    (fun names param => names.insert param.name.text) {}
  let collectExpr (expr : StmtExprMd) : StateM (Std.HashSet String) StmtExprMd := do
    foldStmtExprM (fun node => do
      match node.val with
      | .Assign targets _ =>
          for target in targets do
            match target.val with
            | .Declare param => modify (·.insert param.name.text)
            | _ => pure ()
      | .Var (.Declare param) => modify (·.insert param.name.text)
      | .Quantifier _ param _ _ => modify (·.insert param.name.text)
      | _ => pure ()) expr
    return expr
  (mapProcedureM collectExpr proc |>.run initial).2

private def prepareProcedureGlobals (proc : Procedure) (globals : List Identifier)
    : GlobalTransformM Unit := do
  let boundNames := collectBoundNames proc
  let reservedNames := globals.foldl
    (fun names global => names.insert global.text)
    -- `$heap` is not reserved: it is one of `globals`, so reserving it would rename it
    -- to `$global_$heap` and desync it from the literal `$heap` that `ModifiesClauses`
    -- emits in its frames. Shadowing by a user binding is covered by `boundNames`, and
    -- resolution rejects a user parameter named `$heap`.
    boundNames
  modify fun s => { s with localGlobals := {}, usedNames := reservedNames, freshCounter := 0 }
  for global in globals do
    let localName ← if boundNames.contains global.text then do
        let fresh ← freshName s!"$global_{global.text}"
        pure { fresh with source := global.source }
      else
        pure { global with uniqueId := none }
    match global.uniqueId with
    | some id => modify fun s => { s with localGlobals := s.localGlobals.insert id localName }
    | none => panic! s!"global '{global.text}' has no resolved identity"

private def localGlobalName (global : Identifier) : GlobalTransformM Identifier := do
  let aliases := (← get).localGlobals
  match global.uniqueId.bind aliases.get? with
  | some name => return name
  | none => panic! s!"missing local alias for global '{global.text}'"

private def effectsFor (effects : Std.HashMap Nat (Std.HashSet Nat))
    (global : Identifier) : Std.HashSet Nat :=
  match global.uniqueId with
  | some id => effects.getD id {}
  | none => {}

private def writeGlobalsOf (p : Identifier) : GlobalTransformM (List Identifier) := do
  let s ← get
  return s.globalOrder.filter fun g =>
    p.uniqueId.any fun id => (effectsFor s.writers g).contains id

/-- Written globals are also inputs because they are threaded as inout parameters. -/
private def inputGlobalsOf (p : Identifier) : GlobalTransformM (List Identifier) := do
  let s ← get
  return s.globalOrder.filter fun g => p.uniqueId.any fun id =>
    (effectsFor s.readers g).contains id || (effectsFor s.writers g).contains id

private def globalTypeOf (global : Identifier) : GlobalTransformM HighTypeMd := do
  let types := (← get).globalType
  match global.uniqueId.bind types.get? with
  | some type => return type
  | none => panic! s!"missing type for global '{global.text}'"

private def globalParam (procName : Identifier) (global : Identifier)
    : GlobalTransformM Parameter := do
  let name ← localGlobalName global
  return { name := { name with source := procName.source }
           type := ← globalTypeOf global }

private def globalArgs (globals : List Identifier) (callee : Identifier)
    : GlobalTransformM (List StmtExprMd) :=
  globals.mapM fun global =>
    return mkMd (.Var (.Local (← localGlobalName global))) callee.source

private def globalTargets (globals : List Identifier) (callee : Identifier)
    : GlobalTransformM (List VariableMd) :=
  globals.mapM fun global =>
    return mkVarMd (.Local (← localGlobalName global)) callee.source

private def calleeInputs (model : SemanticModel) (callee : Identifier) : List Parameter :=
  match model.get callee with
  | .staticProcedure proc => proc.inputs
  | .instanceProcedure _ proc => proc.inputs
  | _ => panic! s!"global-dependent callee '{callee.text}' is not a procedure"

private def calleeOutputs (model : SemanticModel) (callee : Identifier) : List Parameter :=
  match model.get callee with
  | .staticProcedure proc => proc.outputs
  | .instanceProcedure _ proc => proc.outputs
  | _ => panic! s!"global-writing callee '{callee.text}' is not a procedure"

/-- Evaluate explicit arguments before sampling hidden globals when an argument
    contains an effect. Binding every explicit argument preserves left-to-right
    source evaluation even when a later argument writes a global. -/
private def bindEffectfulArgs (model : SemanticModel) (callee : Identifier)
    (hiddenInputs : List Identifier) (args : List StmtExprMd)
    : GlobalTransformM (List StmtExprMd × List StmtExprMd) := do
  if hiddenInputs.isEmpty || !(args.any (containsAssignmentOrImperativeCall [])) then
    return ([], args)
  let params := calleeInputs model callee
  let outputs := calleeOutputs model callee
  let bound ← args.attach.mapIdxM fun i ⟨arg, _⟩ => do
    match params[i]? with
    | some param =>
      let isInout := param.name.uniqueId.isSome &&
        outputs.any (·.name.uniqueId == param.name.uniqueId)
      if isInout then
        return (none, arg)
      let name ← freshVarName
      let target := mkVarMd (.Declare ⟨name, some param.type⟩) arg.source
      let binding : StmtExprMd := ⟨.Assign [target] arg, arg.source⟩
      return (some binding, mkMd (.Var (.Local name)) arg.source)
    | none =>
      let name ← freshVarName
      let target := mkVarMd (.Declare ⟨name, some (computeExprType model arg)⟩) arg.source
      let binding : StmtExprMd := ⟨.Assign [target] arg, arg.source⟩
      return (some binding, mkMd (.Var (.Local name)) arg.source)
  return (bound.filterMap (·.1), bound.map (·.2))

private def threadedStaticCall (model : SemanticModel) (callee : Identifier)
    (args : List StmtExprMd) (source : FileRange)
    : GlobalTransformM (List StmtExprMd × StmtExprMd × List Identifier) := do
  let inputs ← inputGlobalsOf callee
  let outputs ← writeGlobalsOf callee
  let (bindings, boundArgs) ← bindEffectfulArgs model callee inputs args
  let call := ⟨.StaticCall callee ((← globalArgs inputs callee) ++ boundArgs), source⟩
  return (bindings, call, outputs)

private def emitStaticCall (model : SemanticModel) (original : StmtExprMd)
    (callee : Identifier) (args : List StmtExprMd) (valueUsed : Bool)
    : GlobalTransformM (List StmtExprMd) := do
  let (bindings, call, outputs) ← threadedStaticCall model callee args original.source
  if outputs.isEmpty then
    return bindings ++ [call]
  else
    let targets ← globalTargets outputs callee
    if valueUsed then
      let result ← freshVarName
      let resultTarget :=
        mkVarMd (.Declare ⟨result, some (computeExprType model original)⟩) original.source
      return bindings ++ [⟨.Assign (targets ++ [resultTarget]) call, original.source⟩,
        mkMd (.Var (.Local result)) original.source]
    else
      -- Preserve output arity when the source discards the callee's value.
      let discards ← (calleeOutputs model callee).mapM fun output => do
        return mkVarMd (.Declare ⟨← freshVarName, some output.type⟩) original.source
      return bindings ++ [⟨.Assign (targets ++ discards) call, original.source⟩]

private def globalOfRef (model : SemanticModel) (name : Identifier)
    : GlobalTransformM (Option Identifier) := do
  let globals := (← get).globalOrder
  return match model.get? name with
    | some (.field owner field) =>
        if owner.text == "$static" then
          globals.find? (·.uniqueId == field.name.uniqueId)
        else none
    | _ => none

private def renameGlobalRef (model : SemanticModel) (name : Identifier)
    : GlobalTransformM Identifier := do
  match ← globalOfRef model name with
  | some global => localGlobalName global
  | none => pure name

private def renameTarget (model : SemanticModel) (target : VariableMd)
    : GlobalTransformM VariableMd := do
  match target.val with
  | .Local name => return { target with val := .Local (← renameGlobalRef model name) }
  | .Declare _ | .Field _ _ => return target

private def transformNode (model : SemanticModel) (valueUsed : Bool) (expr : StmtExprMd)
    : GlobalTransformM (List StmtExprMd) := do
  match expr.val with
  | .StaticCall callee args => emitStaticCall model expr callee args valueUsed
  | .Var (.Local name) =>
      return [{ expr with val := .Var (.Local (← renameGlobalRef model name)) }]
  | .Assign targets rhs =>
      return [{ expr with val := .Assign (← targets.mapM (renameTarget model)) rhs }]
  | .IncrDecr mode op target =>
      return [{ expr with val := .IncrDecr mode op (← renameTarget model target) }]
  | _ => return [expr]

/-- Thread hidden globals through a multi-target assigned call (`assign x, r := f(...)`),
    intercepting it before the bottom-up traversal reaches the call.

    The ordinary path visits the call on its own, where `emitStaticCall` wraps it in a
    block yielding a single value. Two or more receivers cannot be fed from one such
    value, so the hidden arguments are threaded and the hidden receivers merged into the
    assignment's existing target list instead.

    Single-target assignments are left to the ordinary path, which correctly handles a
    target that *is* one of the threaded globals (`g := writer()`); merging would list
    `g` twice. -/
private def transformAssignWithCall (model : SemanticModel)
    (transformArg : StmtExprMd → GlobalTransformM StmtExprMd) (expr : StmtExprMd)
    : GlobalTransformM (Option (List StmtExprMd)) := do
  match expr.val with
  | .Assign targets rhs =>
    match rhs.val with
    | .StaticCall callee args =>
      if targets.length <= 1 then return none
      let hiddenOutputs ← writeGlobalsOf callee
      if hiddenOutputs.isEmpty && (← inputGlobalsOf callee).isEmpty then
        return none
      -- Arguments go through the full transform, not a bare rename: an argument may
      -- itself be a call needing its own hidden globals threaded, and returning `some`
      -- below stops the traversal from reaching it. `threadedStaticCall` then binds any
      -- effectful argument to a temporary, preserving left-to-right evaluation.
      let args' ← args.mapM transformArg
      let targets' ← targets.mapM (renameTarget model)
      let (bindings, call, outputs) ← threadedStaticCall model callee args' expr.source
      -- A source target may name a global the callee also writes, which would give that
      -- global's alias both a hidden receiver and a source one. The source assignment
      -- happens after the call, so it wins; the hidden receiver is diverted to a discard
      -- temporary, which keeps one receiver per callee output.
      let sourceNames := targets'.filterMap fun target =>
        match target.val with
        | .Local name => some name.text
        | _ => none
      let hiddenTargets ← outputs.mapM fun global => do
        let alias ← localGlobalName global
        if sourceNames.contains alias.text then
          return mkVarMd (.Declare ⟨← freshVarName, some (← globalTypeOf global)⟩) callee.source
        else
          return mkVarMd (.Local alias) callee.source
      -- Receivers must follow the callee's output order, which
      -- `globalTransformProcedure` assembles as `hidden globals ++ proc.outputs`. Every
      -- hidden receiver therefore precedes every one the source wrote, including an
      -- explicit inout receiver, which keeps its position inside `targets'`.
      -- `emitStaticCall` orders its own receivers the same way.

      let allTargets := hiddenTargets ++ targets'
      return some (bindings ++ [{ expr with val := .Assign allTargets call }])
    | _ => return none
  | _ => return none

/-- Thread globals through calls and rewrite resolved global references. -/
private partial def globalTransformExpr (model : SemanticModel) (expr : StmtExprMd)
    (valueUsed : Bool := true) : GlobalTransformM StmtExprMd :=
  mapStmtExprFlattenM
    (fun _ e => transformAssignWithCall model (globalTransformExpr model · true) e)
    (transformNode model) valueUsed expr

/-- Add hygienic global parameters and rewrite all procedure expressions. -/
private def globalTransformProcedure (model : SemanticModel) (proc : Procedure)
    : GlobalTransformM Procedure := do
  let inGlobals ← inputGlobalsOf proc.name
  let outGlobals ← writeGlobalsOf proc.name
  prepareProcedureGlobals proc inGlobals
  -- The `reads`/`writes` declarations are inputs to this pass, folded into the effect
  -- maps consulted above. Clear them: `staticFields` is emptied once every global is
  -- threaded, so a surviving declaration would name a global that no longer exists.
  let proc := { proc with readsGlobals := [], writesGlobals := [] }
  let transformValue (expr : StmtExprMd) := globalTransformExpr model expr true
  let preconditions ← proc.preconditions.mapM (·.mapM transformValue)
  let decreases ← proc.decreases.mapM transformValue
  let invokeOn ← proc.invokeOn.mapM transformValue
  let axioms ← proc.axioms.mapM transformValue
  -- `relies` / `guarantees` reference globals too, so rename them alongside the
  -- other specification clauses.
  let relies' ← proc.relies.mapM (·.mapM transformValue)
  let guarantees' ← proc.guarantees.mapM (·.mapM transformValue)
  let contracts := proc.contracts.withClauses (relies := relies') (guarantees := guarantees')
  if proc.isInterpretEntry then
    let prologue ← inGlobals.mapM fun global => do
      let aliasName ← localGlobalName global
      let type ← globalTypeOf global
      let s ← get
      match global.uniqueId.bind s.globalInit.get? with
      | some init =>
        pure (some (⟨.Assign [mkVarMd (.Declare ⟨aliasName, some type⟩) global.source] init,
          global.source⟩ : StmtExprMd))
      | none =>
        modify fun s => { s with diagnostics := s.diagnostics ++
          [diagnosticFromSource global.source
            s!"Internal error: entry procedure '{proc.name.text}' uses global '{global.text}', which reached global lowering without an initializer"
            MessageKind.strataBug] }
        pure none
    let prologue := prologue.filterMap id
    let wrap (body : StmtExprMd) : StmtExprMd :=
      if prologue.isEmpty then body
      else ⟨.Block (prologue ++ [body]) none, body.source⟩
    let body ← match proc.body with
      | .Transparent expression =>
          pure (.Transparent (wrap (← globalTransformExpr model expression false)))
      | .Opaque postconditions implementation modifies => do
          let postconditions ← postconditions.mapM (·.mapM transformValue)
          let modifies ← modifies.mapM fun g => do
            pure { g with targets := ← g.targets.mapM transformValue,
                          guard := ← g.guard.mapM transformValue }
          match implementation with
          | some expression =>
            pure (.Opaque postconditions
              (some (wrap (← globalTransformExpr model expression false))) modifies)
          | none =>
            unless inGlobals.isEmpty do
              modify fun s => { s with diagnostics := s.diagnostics ++
                [diagnosticFromSource proc.name.source
                  s!"Internal error: entry procedure '{proc.name.text}' uses file-scope globals but has no body implementation to initialize them in"
                  MessageKind.strataBug] }
            pure (.Opaque postconditions none modifies)
      | .Abstract postconditions => do
          unless inGlobals.isEmpty do
            modify fun s => { s with diagnostics := s.diagnostics ++
              [diagnosticFromSource proc.name.source
                s!"Internal error: entry procedure '{proc.name.text}' uses file-scope globals but has no body implementation to initialize them in"
                MessageKind.strataBug] }
          pure (.Abstract (← postconditions.mapM (·.mapM transformValue)))
      | .External => pure .External
    return { proc with preconditions, contracts, decreases, invokeOn, axioms, body }
  let inputs ← inGlobals.mapM (globalParam proc.name)
  let outputs ← outGlobals.mapM (globalParam proc.name)
  let body ← match proc.body with
    | .Transparent expression =>
        pure (.Transparent (← globalTransformExpr model expression false))
    | .Opaque postconditions implementation modifies =>
        pure (.Opaque
          (← postconditions.mapM (·.mapM transformValue))
          (← implementation.mapM (fun expr => globalTransformExpr model expr false))
          (← modifies.mapM fun g => do
            pure { g with targets := ← g.targets.mapM transformValue,
                          guard := ← g.guard.mapM transformValue }))
    | .Abstract postconditions =>
        pure (.Abstract (← postconditions.mapM (·.mapM transformValue)))
    | .External => pure .External
  return { proc with
    inputs := inputs ++ proc.inputs
    outputs := outputs ++ proc.outputs
    preconditions
    contracts
    decreases
    invokeOn
    axioms
    body }

private def globalParameterization (model : SemanticModel) (program : Program)
    : Program × List Message :=
  if program.staticFields.isEmpty then
    (program, [])
  else
    let globals := program.staticFields
    let globalOrder := globals.map (·.name)
    let globalType : Std.HashMap Nat HighTypeMd :=
      globals.foldl (fun types global =>
        match global.name.uniqueId with
        | some id => types.insert id global.type
        | none => types) {}
    let globalInit : Std.HashMap Nat StmtExprMd :=
      globals.foldl (fun inits global =>
        match global.name.uniqueId, global.initializer with
        | some id, some init => inits.insert id init
        | _, _ => inits) {}
    let effects := computeGlobalEffectsByProcId model program.staticProcedures globals
    let state : GlobalTransformState :=
      { globalOrder, globalType, globalInit,
        readers := effects.readers, writers := effects.writers }
    let (procedures, finalState) := (program.staticProcedures.mapM
      (globalTransformProcedure model)).run state
    ({ program with staticProcedures := procedures, staticFields := [] },
     finalState.diagnostics)

public def globalParameterizationPass : LoweringPass where
  name := "GlobalParameterization"
  documentation := "Threads file-scope globals through procedure inputs and writer outputs (entry procedures instead declare them as body-prologue locals initialized from the declaration initializers), then clears staticFields."
  needsResolves := true
  run := fun _ program model =>
    let (program', diagnostics) := globalParameterization model program
    (program', diagnostics, {})
  comesAfter :=
    [⟨ eliminateExceptionsPass.meta,
       "a throwing procedure is first normalized to its single Result output, and only then receives its hidden global outputs." ⟩,
     ⟨ eliminateValueInReturnsPass.meta,
       "eliminate value in returns must precede any pass that changes the number of output parameters." ⟩,
     ⟨ liftInstanceProceduresPass.meta,
       "operate on the flat staticProcedures list, after instance procedures are lifted into it." ⟩,
     ⟨ heapParameterizationPass.meta,
       "the heap is modeled as one file-scope global: heap parameterization declares `$heap` and rewrites field access against it, and this pass then threads it through signatures and call sites like any other global." ⟩,
     ⟨ modifiesClausesTransformPass.meta,
       "the modifies pass builds heap frames over `$heap` and needs it still in scope as a global; it also ends the heap trio's shared re-resolve, which binds `$heap` references as `$static` fields so this pass can recognize them." ⟩]
  comesBefore :=
    [⟨ liftImperativeExpressionsPass.meta,
       "the global parameterization pass introduces assignments (threading globals) that need to be lifted." ⟩,
     ⟨ contractPass.meta,
       "the contract pass builds its postcondition helpers from the signature, so a global must already be threaded as an ordinary inout by then: its existing `$out`/`old` machinery then handles `$heap` with no knowledge of globals." ⟩]

end Strata.Laurel

end -- public section
