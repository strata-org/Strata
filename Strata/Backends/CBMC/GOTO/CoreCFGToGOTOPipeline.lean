/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.CollectSymbols
public import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Transform.StructuredToUnstructured

/-! ## Core-to-GOTO translation via CFG

Alternative pipeline that translates Core procedures to CProver GOTO by going
through the CFG representation:

- **Structured body** → `stmtsToCFG` → `coreCFGToGotoTransform`
- **CFG body** → `coreCFGToGotoTransform`

This coexists with the direct path in `CoreToGOTOPipeline.lean`.
-/

namespace Strata

public section

/-! ### Rename helpers for Core commands (CmdExt) -/

private def renameCoreCallArg
    (rn : Std.HashMap String String)
    : Core.CallArg Core.Expression → Core.CallArg Core.Expression
  | .inArg e => .inArg (renameExpr rn e)
  | .inoutArg id => .inoutArg (renameIdent rn id)
  | .outArg id => .outArg (renameIdent rn id)

private def renameCoreCommand
    (rn : Std.HashMap String String)
    : Core.Command → Core.Command
  | .cmd c => .cmd (renameCmd rn c)
  | .call procName callArgs md =>
    .call procName (callArgs.map (renameCoreCallArg rn)) md

private partial def renameCoreStmt
    (rn : Std.HashMap String String)
    : Core.Statement → Core.Statement
  | .cmd c => .cmd (renameCoreCommand rn c)
  | .block l stmts md =>
    .block l (stmts.map (renameCoreStmt rn)) md
  | .ite c t e md =>
    .ite (c.map (renameExpr rn)) (t.map (renameCoreStmt rn)) (e.map (renameCoreStmt rn)) md
  | .loop g m i body md =>
    .loop (g.map (renameExpr rn)) (m.map (renameExpr rn))
      (i.map (fun (l, e) => (l, renameExpr rn e)))
      (body.map (renameCoreStmt rn)) md
  | .exit l md => .exit l md
  | .funcDecl d md => .funcDecl d md
  | .typeDecl tc md => .typeDecl tc md

private def renameCoreDetCFG
    (rn : Std.HashMap String String)
    (cfg : Core.DetCFG) : Core.DetCFG :=
  { cfg with blocks := cfg.blocks.map fun (label, block) =>
    (label, { cmds := block.cmds.map (renameCoreCommand rn),
              transfer := match block.transfer with
                | .condGoto cond lt lf md =>
                  .condGoto (renameExpr rn cond) lt lf md
                | .finish md => .finish md }) }

/-! ### Core-specific CFG-to-GOTO translation

The translator is structured as a two-pass refinement of the CFG:

1. **Forward pass** (`coreCFGToGotoForwardPass`) walks `cfg.blocks` in
   order, threading a `CoreCFGTransLoopState` (instructions, pending
   patches, label map, loop contracts).
2. **Patch-resolution pass** (`coreCFGToGotoResolvePatches`) walks the
   pending patches, looking up each label's location and optionally
   annotating loop-contract guards on backward edges.

This decomposition is mathematically equivalent to inline imperative
loops with `mut` state, but exposes named per-block / per-patch step
functions that the well-formedness proof in
`CoreCFGToGotoTransformWF.lean` recurses on directly. -/

/-- The state threaded through `coreCFGToGotoTransform`'s forward pass:
the GOTO transform under construction, the pending-patches buffer, the
label-to-location map, and the loop-contract metadata map. -/
structure CoreCFGTransLoopState where
  trans : Imperative.GotoTransform Core.Expression.TyEnv
  pendingPatches : Array (Nat × String)
  labelMap : Std.HashMap String Nat
  loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression)

/-- Per-command step function: process one `Core.Command` inside a block
body. Mirrors the body of the inner `for cmd in block.cmds do` loop
inside `coreCFGToGotoBlockStep`.

The state threaded is just the `GotoTransform` (only `trans` is mutated
in the inner loop; the outer-state pieces — `pendingPatches`,
`labelMap`, `loopContracts` — are untouched per-cmd). -/
def coreCFGToGotoCmdStep
    (functionName : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (cmd : Core.Command)
    : Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  match cmd with
  | .cmd c =>
    Imperative.Cmd.toGotoInstructions trans.T functionName c trans
  | .call procName callArgs _md =>
    let lhs := Core.CallArg.getLhs callArgs
    let args := Core.CallArg.getInputExprs callArgs
    let argExprs ← args.mapM toExpr
    let lhsExpr := match lhs with
      | id :: _ =>
        let name := Core.CoreIdent.toPretty id
        let ty := match trans.T.context.types.find? id with
          | some lty =>
            match lty.toMonoTypeUnsafe.toGotoType with
            | .ok gty => gty
            | .error _ =>
              dbg_trace s!"warning: type conversion failed for {name}, defaulting to Integer"
              .Integer
          | none =>
            dbg_trace s!"warning: no type found for {name}, defaulting to Integer"
            .Integer
        CProverGOTO.Expr.symbol name ty
      | [] => CProverGOTO.Expr.symbol "" .Empty
    let calleeExpr := CProverGOTO.Expr.symbol procName
      (CProverGOTO.Ty.mkCode (argExprs.map (·.type)) lhsExpr.type)
    let callCode := CProverGOTO.Code.functionCall lhsExpr calleeExpr argExprs
    let inst : CProverGOTO.Instruction :=
      { type := .FUNCTION_CALL, code := callCode, locationNum := trans.nextLoc }
    return { trans with
      instructions := trans.instructions.push inst
      nextLoc := trans.nextLoc + 1 }

/-- Per-block step function: process one `(label, block)` pair, threading
the loop state. Mirrors the body of `coreCFGToGotoTransform`'s outer
`for (label, block) in cfg.blocks do`. -/
def coreCFGToGotoBlockStep
    (functionName : String)
    (st : CoreCFGTransLoopState)
    (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    : Except Std.Format CoreCFGTransLoopState := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  let (label, block) := lblBlk
  let labelMap := st.labelMap.insert label st.trans.nextLoc
  let srcLoc : CProverGOTO.SourceLocation :=
    { CProverGOTO.SourceLocation.nil with function := functionName }
  let trans := Imperative.emitLabel label srcLoc st.trans
  -- Translate each command via the per-cmd step function.
  let trans ← block.cmds.foldlM (coreCFGToGotoCmdStep functionName) trans
  -- Translate the transfer command
  match block.transfer with
  | .condGoto cond lt lf md =>
    let transferSrcLoc := Imperative.metadataToSourceLoc md functionName trans.sourceText
    let cond_expr ← toExpr cond
    let hasLoopContract := md.any fun elem =>
      elem.fld == Imperative.MetaData.specLoopInvariant ||
      elem.fld == Imperative.MetaData.specDecreases
    let loopContracts :=
      if hasLoopContract then
        st.loopContracts.insert label md
      else
        st.loopContracts
    let (trans, falseIdx) :=
      Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr) transferSrcLoc trans
    let pendingPatches := st.pendingPatches.push (falseIdx, lf)
    let (trans, trueIdx) := Imperative.emitUncondGoto transferSrcLoc trans
    let pendingPatches := pendingPatches.push (trueIdx, lt)
    return { trans, pendingPatches, labelMap, loopContracts }
  | .finish md =>
    -- Emit one END_FUNCTION per `.finish` block. Without this, a CFG
    -- with multiple `.finish` blocks would have intermediate finishes
    -- silently fall through into the next block's LOCATION; the wrapper's
    -- single trailing END_FUNCTION only correctly terminates the last
    -- such block. See `docs/CoreToGOTO_CorrectnessAnalysis.md` §6 (Gap E)
    -- and the WellFormedTranslation.layout_finish field.
    let transferSrcLoc := Imperative.metadataToSourceLoc md functionName trans.sourceText
    let endInst : CProverGOTO.Instruction :=
      { type := .END_FUNCTION,
        locationNum := trans.nextLoc,
        sourceLoc := transferSrcLoc }
    let trans := { trans with
      instructions := trans.instructions.push endInst,
      nextLoc := trans.nextLoc + 1 }
    return { trans, pendingPatches := st.pendingPatches, labelMap,
             loopContracts := st.loopContracts }

/-- Per-patch step function: process one `(idx, label)` pending patch,
threading the loop state. Mirrors the body of
`coreCFGToGotoTransform`'s second `for (idx, label) in pendingPatches`
loop, accumulating into a `(resolvedPatches, trans)` pair. -/
def coreCFGToGotoPatchStep
    (labelMap : Std.HashMap String Nat)
    (loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression))
    (acc : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    : Except Std.Format
        (List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv) := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  let (resolvedPatches, trans) := acc
  let (idx, label) := idxLabel
  match labelMap[label]? with
  | some targetLoc =>
    let mut resolvedPatches := (idx, targetLoc) :: resolvedPatches
    let mut trans := trans
    if let some md := loopContracts[label]? then
      let instLoc := trans.instructions[idx]!.locationNum
      if targetLoc ≤ instLoc then
        let mut guard := trans.instructions[idx]!.guard
        for elem in md do
          if elem.fld == Imperative.MetaData.specLoopInvariant then
            if let .expr e := elem.value then
              let gotoExpr ← toExpr e
              guard := guard.setNamedField "#spec_loop_invariant" gotoExpr
          if elem.fld == Imperative.MetaData.specDecreases then
            if let .expr e := elem.value then
              let gotoExpr ← toExpr e
              guard := guard.setNamedField "#spec_decreases" gotoExpr
        trans := { trans with
          instructions := trans.instructions.set! idx
            { trans.instructions[idx]! with guard := guard } }
    return (resolvedPatches, trans)
  | none =>
    throw f!"[coreCFGToGotoTransform] Unresolved label '{label}' referenced \
             by GOTO at instruction index {idx}."

/--
Translate a Core `DetCFG` to CProver GOTO instructions.

Like `detCFGToGotoTransform` but handles `Core.Command` (which includes
`CmdExt.call`). The CFG should already have identifiers renamed via
`renameCoreDetCFG`.

The forward pass and patch-resolution pass are factored as
`foldlM` over the per-block / per-patch step functions
`coreCFGToGotoBlockStep` and `coreCFGToGotoPatchStep`. This makes the
translator amenable to inductive proof in
`CoreCFGToGotoTransformWF.lean`.
-/
def coreCFGToGotoTransform
    (_Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    : Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) := do
  -- Verify entry block is first
  match cfg.blocks with
  | (firstLabel, _) :: _ =>
    if firstLabel != cfg.entry then
      throw f!"[coreCFGToGotoTransform] Entry label '{cfg.entry}' does not match \
               first block label '{firstLabel}'."
  | [] => pure ()
  -- Forward pass: emit instructions for each block
  let initSt : CoreCFGTransLoopState :=
    { trans := trans, pendingPatches := #[], labelMap := {}, loopContracts := {} }
  let st ← cfg.blocks.foldlM (coreCFGToGotoBlockStep functionName) initSt
  -- Second pass: resolve labels and annotate backward-edge GOTOs with loop contracts
  let (resolvedPatches, trans) ← st.pendingPatches.foldlM
    (coreCFGToGotoPatchStep st.labelMap st.loopContracts) ([], st.trans)
  return Imperative.patchGotoTargets trans resolvedPatches

/-! ### Pipeline wrapper -/

/--
Translate a Core procedure to CProver GOTO via the CFG representation.

Mirrors `procedureToGotoCtx` but routes through `stmtsToCFG` +
`coreCFGToGotoTransform` instead of the direct Stmt-to-GOTO path.
-/
def procedureToGotoCtxViaCFG
    (Env : Core.Expression.TyEnv) (p : Core.Procedure)
    (sourceText : Option String := none)
    (axioms : List Core.Axiom := [])
    (distincts :
      List (Core.Expression.Ident × List Core.Expression.Expr) := [])
    : Except Std.Format
        (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  let pname := Core.CoreIdent.toPretty p.header.name
  if !p.header.typeArgs.isEmpty then
    .error f!"[procedureToGotoCtxViaCFG] Polymorphic procedures unsupported."
  let ret_ty := CProverGOTO.Ty.Empty
  let formals := p.header.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol pname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  let outputs := p.header.outputs.keys.map Core.CoreIdent.toPretty
  let new_outputs := outputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals_from_body := match p.body with
    | .structured ss => (Imperative.Block.definedVars ss).map Core.CoreIdent.toPretty
    | .cfg c => c.blocks.flatMap (fun (_, blk) =>
        blk.cmds.flatMap Core.Command.definedVars)
      |>.map Core.CoreIdent.toPretty
  let new_locals := locals_from_body.map (CProverGOTO.mkLocalSymbol pname ·)
  let rn : Std.HashMap String String :=
    (formals.zip new_formals ++ outputs.zip new_outputs ++ locals_from_body.zip new_locals).foldl
      (init := {}) fun m (k, v) => m.insert k v
  -- Seed the type environment with renamed input and output parameter types
  let inputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_formals.zip p.header.inputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let outputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_outputs.zip p.header.outputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let Env' : Core.Expression.TyEnv :=
    Lambda.TEnv.addInNewestContext (T := ⟨Core.ExpressionMetadata, Unit⟩)
      Env (inputEntries ++ outputEntries)
  -- Emit axioms as ASSUME instructions
  let mut axiomInsts : Array CProverGOTO.Instruction := #[]
  let mut axiomLoc : Nat := 0
  for ax in axioms do
    let gotoExpr ← Lambda.LExpr.toGotoExprCtx
      (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] ax.e
    if gotoExpr.hasUnsupportedQuantifierTypes then continue
    axiomInsts := axiomInsts.push
      { type := .ASSUME, locationNum := axiomLoc,
        guard := gotoExpr,
        sourceLoc := { CProverGOTO.SourceLocation.nil with
          function := pname, comment := s!"axiom {ax.name}" } }
    axiomLoc := axiomLoc + 1
  -- Emit distinct declarations as pairwise != ASSUME instructions
  for (dname, exprs) in distincts do
    let gotoExprs ← exprs.mapM
      (Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [])
    for i in List.range gotoExprs.length do
      for j in List.range gotoExprs.length do
        if i < j then
          let ei := gotoExprs[i]!
          let ej := gotoExprs[j]!
          let neqExpr : CProverGOTO.Expr :=
            { id := .binary .NotEqual, type := .Boolean, operands := [ei, ej] }
          let srcLoc : CProverGOTO.SourceLocation :=
            { CProverGOTO.SourceLocation.nil with
                function := pname
                comment := s!"distinct {Core.CoreIdent.toPretty dname}" }
          axiomInsts := axiomInsts.push
            { type := .ASSUME, locationNum := axiomLoc, guard := neqExpr, sourceLoc := srcLoc }
          axiomLoc := axiomLoc + 1
  -- Build the CFG (from structured body or use existing CFG)
  let (cfg, liftedFuncs) ← match p.body with
    | .structured ss => do
      let (liftedFuncs, body) ← collectFuncDecls ss
      let renamedBody := body.map (renameCoreStmt rn)
      let cfg := Imperative.stmtsToCFG renamedBody
      pure (cfg, liftedFuncs)
    | .cfg c => do
      let cfg := renameCoreDetCFG rn c
      pure (cfg, [])
  -- Translate CFG to GOTO. `coreCFGToGotoTransform` now emits one
  -- END_FUNCTION per `.finish` block inline, so the wrapper no longer
  -- needs to append a trailing END_FUNCTION here.
  let ans ← coreCFGToGotoTransform Env' pname cfg
    { instructions := axiomInsts, nextLoc := axiomLoc, T := Env', sourceText := sourceText }
  let pgm := { name := pname,
               parameterIdentifiers := new_formals.toArray,
               instructions := ans.instructions }
  -- Translate procedure contracts
  let mut contracts : List (String × Lean.Json) := []
  let preExprs := p.spec.preconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  let postExprs := p.spec.postconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  let toGotoExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  if !preExprs.isEmpty then
    let preGoto ← preExprs.mapM toGotoExpr
    let preJson ← (preGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_requires",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr preJson.toArray)])]
  if !postExprs.isEmpty then
    let postGoto ← postExprs.mapM toGotoExpr
    let postJson ← (postGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_ensures",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr postJson.toArray)])]
  -- Build localTypes map for output parameters
  let output_tys ← p.header.outputs.values.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    (outputs.zip output_tys).foldl (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := outputs ++ locals_from_body, contracts := contracts,
      localTypes := localTypes }
  return (ctx, liftedFuncs)

end -- public section

end Strata
