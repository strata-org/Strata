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

/-! ### Core-specific CFG-to-GOTO translation -/

/--
Translate a Core `DetCFG` to CProver GOTO instructions.

Like `detCFGToGotoTransform` but handles `Core.Command` (which includes
`CmdExt.call`). The CFG should already have identifiers renamed via
`renameCoreDetCFG`.
-/
def coreCFGToGotoTransform
    (_Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    : Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  -- Verify entry block is first
  match cfg.blocks with
  | (firstLabel, _) :: _ =>
    if firstLabel != cfg.entry then
      throw f!"[coreCFGToGotoTransform] Entry label '{cfg.entry}' does not match \
               first block label '{firstLabel}'."
  | [] => pure ()
  let mut trans := trans
  let mut pendingPatches : Array (Nat × String) := #[]
  let mut labelMap : Std.HashMap String Nat := {}
  let mut loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression) := {}
  for (label, block) in cfg.blocks do
    labelMap := labelMap.insert label trans.nextLoc
    let srcLoc : CProverGOTO.SourceLocation :=
      { CProverGOTO.SourceLocation.nil with function := functionName }
    trans := Imperative.emitLabel label srcLoc trans
    -- Translate each command
    for cmd in block.cmds do
      match cmd with
      | .cmd c =>
        trans ← Imperative.Cmd.toGotoInstructions trans.T functionName c trans
      | .call procName callArgs _md =>
        let lhs := Core.CallArg.getLhs callArgs
        let args := Core.CallArg.getInputExprs callArgs
        -- `getInputExprs` synthesizes a typeless `LExpr.fvar id none` for every
        -- inout argument. Look up the type from the threaded type env so
        -- `toGotoExprCtx` can produce a typed GOTO symbol expression.
        let typedArgs := args.map fun e => match e with
          | .fvar m id none =>
            match trans.T.context.types.find? id with
            | some lty => Lambda.LExpr.fvar m id (some lty.toMonoTypeUnsafe)
            | none => e
          | _ => e
        let argExprs ← typedArgs.mapM toExpr
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
        trans := { trans with
          instructions := trans.instructions.push inst
          nextLoc := trans.nextLoc + 1 }
    -- Translate the transfer command
    match block.transfer with
    | .condGoto cond lt lf md =>
      let transferSrcLoc := Imperative.metadataToSourceLoc md functionName trans.sourceText
      let cond_expr ← toExpr cond
      let hasLoopContract := md.any fun elem =>
        elem.fld == Imperative.MetaData.specLoopInvariant ||
        elem.fld == Imperative.MetaData.specDecreases
      if hasLoopContract then
        loopContracts := loopContracts.insert label md
      let (trans', falseIdx) :=
        Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr) transferSrcLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (falseIdx, lf)
      let (trans', trueIdx) := Imperative.emitUncondGoto transferSrcLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (trueIdx, lt)
    | .finish _md =>
      pure ()
  -- Second pass: resolve labels and annotate backward-edge GOTOs with loop contracts
  let mut resolvedPatches : List (Nat × Nat) := []
  for (idx, label) in pendingPatches do
    match labelMap[label]? with
    | some targetLoc =>
      resolvedPatches := (idx, targetLoc) :: resolvedPatches
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
    | none =>
      throw f!"[coreCFGToGotoTransform] Unresolved label '{label}' referenced \
               by GOTO at instruction index {idx}."
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
  -- Inout params live in BOTH inputs and outputs by Strata Core convention;
  -- their canonical CBMC binding is the formal symbol (`pname::x`), not a
  -- separate local (`pname::1::x`). Filter inouts out of the outputs list.
  let formalsSet : Std.HashSet String := formals.foldl (·.insert ·) ∅
  let pureOutputPairs := (outputs.zip p.header.outputs.values).filter
    fun (n, _) => !formalsSet.contains n
  let pureOutputs := pureOutputPairs.map (·.1)
  let pureOutputTypes := pureOutputPairs.map (·.2)
  let new_outputs := pureOutputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals_from_body := match p.body with
    | .structured ss => (Imperative.Block.definedVars ss).map Core.CoreIdent.toPretty
    | .cfg c => c.blocks.flatMap (fun (_, blk) =>
        blk.cmds.flatMap Core.Command.definedVars)
      |>.map Core.CoreIdent.toPretty
  let new_locals := locals_from_body.map (CProverGOTO.mkLocalSymbol pname ·)
  let rn : Std.HashMap String String :=
    (formals.zip new_formals ++ pureOutputs.zip new_outputs ++ locals_from_body.zip new_locals).foldl
      (init := {}) fun m (k, v) => m.insert k v
  -- Seed the type environment with renamed input and output parameter types
  let inputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_formals.zip p.header.inputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let outputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_outputs.zip pureOutputTypes).map fun (n, ty) =>
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
  -- Translate CFG to GOTO
  let ans ← coreCFGToGotoTransform Env' pname cfg
    { instructions := axiomInsts, nextLoc := axiomLoc, T := Env', sourceText := sourceText }
  let ending_insts : Array CProverGOTO.Instruction :=
    #[{ type := .END_FUNCTION, locationNum := ans.nextLoc + 1 }]
  let pgm := { name := pname,
               parameterIdentifiers := new_formals.toArray,
               instructions := ans.instructions ++ ending_insts }
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
  -- Build localTypes map for pure output parameters.
  -- Inouts are bound by the formal symbol and don't get a separate local entry.
  let pureOutput_tys ← pureOutputTypes.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    (pureOutputs.zip pureOutput_tys).foldl (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := pureOutputs ++ locals_from_body, contracts := contracts,
      localTypes := localTypes }
  return (ctx, liftedFuncs)

end -- public section

end Strata
