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
Reorder a Core `DetCFG`'s blocks into reverse-postorder from `cfg.entry`.

Standard recursive DFS: visit each successor before prepending the current
block to the accumulator. Real CFG cycles (genuine loops) terminate via
the `seen` set; back-edges to already-visited blocks don't recurse, and
the target's RPO position is determined by its first DFS visit.

After reordering, every forward CFG edge `u → v` has `index(u) < index(v)`
in the returned list. Backward edges in the listing correspond exactly to
real CFG back-edges. Used by `coreCFGToGotoTransform` so that the emitted
GOTO `locationNum` ordering aligns with CFG forward flow, eliminating
spurious back-edges that CBMC's loop detector would otherwise treat as
real loops and instrument with unwinding-assertions.

Blocks unreachable from `cfg.entry` are silently dropped (they emit no
runtime-reachable instructions anyway). Edges to non-existent labels are
defensively ignored here; the downstream label-resolution pass throws
"Unresolved label" if any actually surface.

`partial` because the recursion's termination depends on `seen` set
membership rather than a structural decrease, which Lean can't prove
automatically. Same convention as the other `partial def`s in this file.
-/
private partial def cfgReversePostorder
    (cfg : Core.DetCFG)
    : List (String × Imperative.DetBlock String Core.Command Core.Expression) :=
  let blockMap : Std.HashMap String (Imperative.DetBlock String Core.Command Core.Expression) :=
    cfg.blocks.foldl (fun m (l, b) => m.insert l b) {}
  let succs (blk : Imperative.DetBlock String Core.Command Core.Expression) : List String :=
    match blk.transfer with
    | .condGoto _ lt lf _ => [lt, lf]
    | .finish _ => []
  let rec visit (label : String)
      (st : List (String × Imperative.DetBlock String Core.Command Core.Expression)
            × Std.HashSet String)
      : List (String × Imperative.DetBlock String Core.Command Core.Expression)
        × Std.HashSet String :=
    let (acc, seen) := st
    if seen.contains label then (acc, seen)
    else match blockMap[label]? with
      | none => (acc, seen)
      | some blk =>
        let seen := seen.insert label
        let st := (succs blk).foldl (fun s succLabel => visit succLabel s) (acc, seen)
        ((label, blk) :: st.1, st.2)
  let (rpo, _) := visit cfg.entry ([], {})
  rpo

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
  -- Iterate blocks in reverse-postorder so forward CFG edges emit as
  -- forward-only GOTOs. Without the reorder, SMACK-translated programs
  -- with branches emit blocks in an order where forward control flow
  -- looks like back-edges to CBMC's loop detector, triggering
  -- unwinding-assertion timeouts. See `cfgReversePostorder` above.
  for (label, block) in cfgReversePostorder cfg do
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

/-! ### JSON splice helpers -/

/--
Merge a `Json.obj` of symbol-table entries (keyed by symbol name) into
the existing symtab JSON, which has shape `{"symbolTable": {...}}`.
Later entries win on key collision.
-/
private def mergeSymtabEntries (symtab : Lean.Json) (newEntries : Lean.Json)
    : Lean.Json :=
  match symtab with
  | .obj outer =>
    match outer.toList.find? (·.1 == "symbolTable") with
    | some (_, .obj inner) =>
      let merged := match newEntries with
        | .obj add => add.toList.foldl (fun m (k, v) => m.insert k v) inner
        | _ => inner
      .obj (outer.insert "symbolTable" (.obj merged))
    | _ => symtab
  | _ => symtab

/--
Append a single GOTO-function JSON object to the `"functions"` array
inside the existing GOTO JSON, which has shape
`{"functions": [...]}`.
-/
private def appendGotoFunction (goto : Lean.Json) (newFn : Lean.Json)
    : Lean.Json :=
  match goto with
  | .obj outer =>
    match outer.toList.find? (·.1 == "functions") with
    | some (_, .arr fns) =>
      .obj (outer.insert "functions" (.arr (fns.push newFn)))
    | _ => goto
  | _ => goto

/-! ### CBMC entry-point shim -/

/--
Build a synthetic `__cprover_entry()` GOTO program that calls the
Strata-translated `main` with nondet-initialized parameter values.

CBMC accepts only the standard C entry-point signatures (`int main(void)`,
`int main(int, char**)`, etc.). SMACK-translated `main` takes parameters
(memory maps, exception flags, address state, return value), so cbmc
rejects it with "the program has no entry point" / rc=6 even when
`--function main` is passed.

Returns a JSON pair `(symtab_entries, goto_function)`:
- `symtab_entries`: a `Json.obj` mapping each new symbol name to its
  CBMCSymbol entry (the entry function itself plus one local per
  declared shim variable).
- `goto_function`: a single `Json.obj` for the entry program's body,
  suitable for appending to the existing GOTO functions array.
-/
def buildEntryShim
    (entryName : String)
    (mainName : String)
    (mainFormals : Map String CProverGOTO.Ty)
    (mainRetTy : CProverGOTO.Ty)
    : Except String (Lean.Json × Lean.Json) := do
  -- Declare one local per main formal, named `entryName::1::<formal>`,
  -- initialize from nondet, then call main with those locals.
  let mkLocal := CProverGOTO.mkLocalSymbol entryName
  let argLocals : List (String × CProverGOTO.Ty) :=
    mainFormals.map fun (name, ty) => (mkLocal name, ty)
  let mut insts : Array CProverGOTO.Instruction := #[]
  let mut loc : Nat := 0
  -- DECL + ASSIGN nondet for each formal local
  for (lname, lty) in argLocals do
    let sym := CProverGOTO.Expr.symbol lname lty
    insts := insts.push
      { type := .DECL, code := CProverGOTO.Code.decl sym, locationNum := loc }
    loc := loc + 1
    let nondetExpr := CProverGOTO.Expr.nondet lname lty
    insts := insts.push
      { type := .ASSIGN, code := CProverGOTO.Code.assign sym nondetExpr,
        locationNum := loc }
    loc := loc + 1
  -- Possibly DECL a local for main's return value (so the call has somewhere to land)
  let retLocal := mkLocal "_ret"
  let hasReturn := mainRetTy != CProverGOTO.Ty.Empty
  let lhsExpr : CProverGOTO.Expr :=
    if hasReturn then CProverGOTO.Expr.symbol retLocal mainRetTy
    else CProverGOTO.Expr.symbol "" .Empty
  if hasReturn then
    insts := insts.push
      { type := .DECL, code := CProverGOTO.Code.decl lhsExpr, locationNum := loc }
    loc := loc + 1
  -- FUNCTION_CALL main(arg_locals...)
  let argExprs : List CProverGOTO.Expr :=
    argLocals.map fun (lname, lty) => CProverGOTO.Expr.symbol lname lty
  let calleeExpr := CProverGOTO.Expr.symbol mainName
    (CProverGOTO.Ty.mkCode (argExprs.map (·.type)) lhsExpr.type)
  insts := insts.push
    { type := .FUNCTION_CALL,
      code := CProverGOTO.Code.functionCall lhsExpr calleeExpr argExprs,
      locationNum := loc }
  loc := loc + 1
  -- END_FUNCTION
  insts := insts.push
    { type := .END_FUNCTION, locationNum := loc }
  let pgm : CProverGOTO.Program :=
    { name := entryName,
      parameterIdentifiers := #[],
      instructions := insts }
  -- Build symtab entries: one function symbol for entryName (signature: () -> Empty)
  -- plus one local symbol per arg local (and the optional return local).
  let entryFnSymbol : Map String CProverGOTO.CBMCSymbol :=
    [CProverGOTO.createFunctionSymbol entryName ([] : Map String CProverGOTO.Ty)
      CProverGOTO.Ty.Empty []]
  let argSymbols : Map String CProverGOTO.CBMCSymbol :=
    argLocals.map fun (lname, lty) =>
      -- baseName is the original (unprefixed) ident for prettyName; recover
      -- by stripping the entryName::1:: prefix. Since we always prefix via
      -- mkLocalSymbol, mirror that here.
      let base := lname  -- using full local name as baseName too is harmless
      CProverGOTO.createGOTOSymbol entryName base lname
        (isParameter := false) (isStateVar := false) (ty := some lty)
  let retSymList : Map String CProverGOTO.CBMCSymbol :=
    if hasReturn then
      [CProverGOTO.createGOTOSymbol entryName retLocal retLocal
         (isParameter := false) (isStateVar := false) (ty := some mainRetTy)]
    else []
  let allSymbols := entryFnSymbol ++ argSymbols ++ retSymList
  let symtabJson := Lean.Json.mkObj (allSymbols.map fun (k, v) => (k, Lean.toJson v))
  let gotoFn ← CProverGOTO.programToJson entryName pgm
  return (symtabJson, gotoFn)

/-! ### Body-aware dispatch -/

/--
Translate a Core procedure to CProver GOTO, dispatching on the body
representation: structured bodies go through `procedureToGotoCtx`, CFG
bodies go through `procedureToGotoCtxViaCFG`.
-/
def procedureToGotoCtxDispatch
    (Env : Core.Expression.TyEnv) (p : Core.Procedure)
    (sourceText : Option String := none)
    (axioms : List Core.Axiom := [])
    (distincts :
      List (Core.Expression.Ident × List Core.Expression.Expr) := [])
    : Except Std.Format
        (CoreToGOTO.CProverGOTO.Context × List Core.Function) :=
  match p.body with
  | .cfg _ => procedureToGotoCtxViaCFG Env p sourceText axioms distincts
  | _      => procedureToGotoCtx Env p sourceText axioms distincts

/--
Mirrors `coreToGotoFiles` but dispatches on body type so CFG procedures
go through `procedureToGotoCtxViaCFG` instead of erroring with
"expected structured body, got CFG".
-/
public def coreToGotoFilesDispatch (tcPgm : Core.Program)
    (Env : Core.Expression.TyEnv)
    (baseName : String)
    (sourceText : Option String := none)
    (entryPoints : List String := ["main", "__main__"])
    : EIO String Unit := do
  let findProc (name : String) := tcPgm.decls.find? fun d =>
      match d with
      | .proc p _ => Core.CoreIdent.toPretty p.header.name == name
      | _ => false
  let mainDecl ← match entryPoints.findSome? findProc with
    | some d => pure d
    | none => throw s!"No entry-point procedure found (tried {entryPoints})"
  let some p := mainDecl.getProc?
    | throw "entry point is not a procedure"
  let procName := "main"
  let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
  let distincts := tcPgm.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  match procedureToGotoCtxDispatch Env p sourceText
        (axioms := axioms) (distincts := distincts) with
  | .error e => throw s!"{e}"
  | .ok (ctx, liftedFuncs) =>
    let extraSyms ← match collectExtraSymbols tcPgm with
      | .ok s => pure (Lean.toJson s)
      | .error e => throw s!"{e}"
    let (symtab, goto) ←
      match ← emitProcWithLifted Env procName ctx liftedFuncs extraSyms
              (moduleName := baseName) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"
    -- Splice in the synthetic CBMC entry-point shim. CBMC requires a
    -- standard-C entry signature; SMACK's `main` has memory-map + exception
    -- params that don't match. The shim has signature `void(void)` and calls
    -- main with nondet-initialized arguments.
    let entryName := "__cprover_entry"
    let (shimSyms, shimFn) ←
      match buildEntryShim entryName procName ctx.formals ctx.ret with
      | .ok r => pure r
      | .error e => throw s!"buildEntryShim: {e}"
    let symtab := mergeSymtabEntries symtab shimSyms
    let goto := appendGotoFunction goto shimFn
    let symTabFile := s!"{baseName}.symtab.json"
    let gotoFile := s!"{baseName}.goto.json"
    match ← writeJsonFile symTabFile symtab |>.toBaseIO with
    | .ok () => pure ()
    | .error e => throw s!"Error writing {symTabFile}: {e}"
    match ← writeJsonFile gotoFile goto |>.toBaseIO with
    | .ok () => pure ()
    | .error e => throw s!"Error writing {gotoFile}: {e}"
    let _ ← IO.println s!"Written {symTabFile} and {gotoFile}" |>.toBaseIO

end -- public section

end Strata
