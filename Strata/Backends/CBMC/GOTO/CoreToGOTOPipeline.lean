/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import Strata.Backends.CBMC.GOTO.DefaultSymbols

/-! ## Core-to-GOTO translation pipeline

Translates Core procedures and functions into CProver GOTO contexts.

### Known limitations

#### Program-level declarations (`Core.Decl`)
- **`Decl.var`** (global variables): Emitted as GOTO symbol table entries with
  `isStaticLifetime := true`. Optional initializers are translated to the symbol's
  `value` field.
- **`Decl.ax`** (axioms): Emitted as ASSUME instructions at the start of each
  procedure body.
- **`Decl.distinct`**: Emitted as pairwise `!=` ASSUME instructions at the
  start of each procedure body.

#### Procedure contracts (`Core.Procedure.Spec`)
Preconditions, postconditions, and modifies clauses are now emitted as
`#spec_requires`, `#spec_ensures`, and `#spec_assigns` named sub-expressions
on the code type in the symbol table. These are recognized by
`goto-instrument --apply-code-contracts` (DFCC).

The following are not yet handled:
- **`free requires`/`free ensures`**: Silently skipped (not emitted as contract
  annotations). CBMC's DFCC does not have a direct equivalent of Boogie's free specs.

#### Procedure calls
- **`CmdExt.call`**: Handled by `coreStmtsToGoto`, which emits FUNCTION_CALL
  instructions directly. The `unwrapCmdExt` path (used when no calls are present)
  returns an error on calls as a safety check.
-/

namespace Strata

private def renameIdent (rn : Std.HashMap String String) (id : Core.CoreIdent) : Core.CoreIdent :=
  match rn[id.name]? with
  | some new => ⟨new, id.metadata⟩
  | none => id

private partial def renameExpr
    (rn : Std.HashMap String String)
    : Core.Expression.Expr → Core.Expression.Expr
  | .fvar m name ty => .fvar m (renameIdent rn name) ty
  | .app m f e => .app m (renameExpr rn f) (renameExpr rn e)
  | .abs m name ty e => .abs m name ty (renameExpr rn e)
  | .quant m qk name ty tr e => .quant m qk name ty (renameExpr rn tr) (renameExpr rn e)
  | .ite m c t e => .ite m (renameExpr rn c) (renameExpr rn t) (renameExpr rn e)
  | .eq m e1 e2 => .eq m (renameExpr rn e1) (renameExpr rn e2)
  | e => e

private def renameCmd
    (rn : Std.HashMap String String)
    : Imperative.Cmd Core.Expression → Imperative.Cmd Core.Expression
  | .init name ty e md => .init (renameIdent rn name) ty (e.map (renameExpr rn)) md
  | .set name e md => .set (renameIdent rn name) (renameExpr rn e) md
  | .havoc name md => .havoc (renameIdent rn name) md
  | .assert l e md => .assert l (renameExpr rn e) md
  | .assume l e md => .assume l (renameExpr rn e) md
  | .cover l e md => .cover l (renameExpr rn e) md

private partial def unwrapCmdExt
    (rn : Std.HashMap String String)
    : Core.Statement → Except Std.Format
        (Imperative.Stmt Core.Expression (Imperative.Cmd Core.Expression))
  | .cmd (.cmd c) => .ok (.cmd (renameCmd rn c))
  | .cmd (.call ..) => .error f!"[unwrapCmdExt] Unexpected call; use coreStmtsToGoto instead."
  | .block l stmts md => do
    let stmts' ← stmts.mapM (unwrapCmdExt rn)
    .ok (.block l stmts' md)
  | .ite c t e md => do
    let t' ← t.mapM (unwrapCmdExt rn)
    let e' ← e.mapM (unwrapCmdExt rn)
    .ok (.ite (renameExpr rn c) t' e' md)
  | .loop g m i body md => do
    let body' ← body.mapM (unwrapCmdExt rn)
    .ok (.loop (renameExpr rn g) (m.map (renameExpr rn)) (i.map (renameExpr rn)) body' md)
  | .exit l md => .ok (.exit l md)
  | .funcDecl _d _md =>
    .error f!"[unwrapCmdExt] Unexpected funcDecl; should have been lifted by collectFuncDecls."
  | .typeDecl _tc _md => .error f!"[unwrapCmdExt] Unexpected typeDecl."

/--
Check whether a Core statement list contains any call statements.
-/
private def hasCallStmt : List Core.Statement → Bool
  | [] => false
  | .cmd (.call ..) :: _ => true
  | .block _ stmts _ :: rest => hasCallStmt stmts || hasCallStmt rest
  | .ite _ t e _ :: rest => hasCallStmt t || hasCallStmt e || hasCallStmt rest
  | .loop _ _ _ body _ :: rest => hasCallStmt body || hasCallStmt rest
  | _ :: rest => hasCallStmt rest

/--
Collect all funcDecl statements from a procedure body (recursively)
and return them as Core.Functions, stripping them from the body.
-/
private def collectFuncDecls : List Core.Statement →
    Except Std.Format (List Core.Function × List Core.Statement)
  | [] => return ([], [])
  | .funcDecl decl _ :: rest => do
    let f ← Core.Function.ofPureFunc decl
    let (fs, rest') ← collectFuncDecls rest
    return (f :: fs, rest')
  | .block l stmts md :: rest => do
    let (fs1, stmts') ← collectFuncDecls stmts
    let (fs2, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2, .block l stmts' md :: rest')
  | .ite c t e md :: rest => do
    let (fs1, t') ← collectFuncDecls t
    let (fs2, e') ← collectFuncDecls e
    let (fs3, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2 ++ fs3, .ite c t' e' md :: rest')
  | .loop g m i body md :: rest => do
    let (fs1, body') ← collectFuncDecls body
    let (fs2, rest') ← collectFuncDecls rest
    return (fs1 ++ fs2, .loop g m i body' md :: rest')
  | s :: rest => do
    let (fs, rest') ← collectFuncDecls rest
    return (fs, s :: rest')

/--
Translate Core statements to GOTO instructions, handling calls at
any nesting level.
-/
private partial def coreStmtsToGoto
    (Env : Core.Expression.TyEnv) (pname : String)
    (rn : Std.HashMap String String)
    (stmts : List Core.Statement)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    : Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) := do
  let toExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  match stmts with
  | [] => return trans
  | stmt :: rest =>
    let trans ← match stmt with
      | .cmd (.call lhs procName args _md) =>
        let renamedLhs := lhs.map (renameIdent rn)
        let renamedArgs := args.map (renameExpr rn)
        let argExprs ← renamedArgs.mapM toExpr
        let lhsExpr := match renamedLhs with
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
        let calleeExpr := CProverGOTO.Expr.symbol procName .Empty
        let callCode := CProverGOTO.Code.functionCall lhsExpr calleeExpr argExprs
        let inst : CProverGOTO.Instruction :=
          { type := .FUNCTION_CALL, code := callCode, locationNum := trans.nextLoc }
        pure { trans with
          instructions := trans.instructions.push inst
          nextLoc := trans.nextLoc + 1 }
      | .block l body md =>
        if hasCallStmt body then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.sourceText
          let trans := Imperative.emitLabel l srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn body trans
          let end_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"end_block_{l}" srcLoc trans
          let (matching, remaining) := trans.pendingExits.partition fun (_, lab) =>
            lab == some l || lab == none
          let patches := matching.map fun (idx, _) => (idx, end_loc)
          pure (Imperative.patchGotoTargets { trans with pendingExits := remaining } patches)
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | .ite cond thenb elseb md =>
        if hasCallStmt thenb || hasCallStmt elseb then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.sourceText
          let cond_expr ← toExpr (renameExpr rn cond)
          let (trans, goto_else_idx) :=
            Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr) srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn thenb trans
          let (trans, goto_end_idx) := Imperative.emitUncondGoto srcLoc trans
          let else_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"else_{else_loc}" srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn elseb trans
          let end_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"end_if_{else_loc}" srcLoc trans
          pure (Imperative.patchGotoTargets trans
            [(goto_else_idx, else_loc), (goto_end_idx, end_loc)])
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | .loop guard measure invariants body md =>
        if hasCallStmt body then
          let srcLoc := Imperative.metadataToSourceLoc md pname trans.sourceText
          let loop_head := trans.nextLoc
          let trans := Imperative.emitLabel s!"loop_{loop_head}" srcLoc trans
          let guard_expr ← toExpr (renameExpr rn guard)
          let (trans, goto_end_idx) :=
            Imperative.emitCondGoto (CProverGOTO.Expr.not guard_expr) srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn body trans
          let mut backGuard := CProverGOTO.Expr.true
          for inv in invariants do
            let inv_expr ← toExpr (renameExpr rn inv)
            backGuard := backGuard.setNamedField "#spec_loop_invariant" inv_expr
          match measure with
            | some meas =>
              let meas_expr ← toExpr (renameExpr rn meas)
              backGuard := backGuard.setNamedField "#spec_decreases" meas_expr
            | none => pure ()
          let backInst : CProverGOTO.Instruction :=
            { type := .GOTO, guard := backGuard, target := some loop_head,
              locationNum := trans.nextLoc, sourceLoc := srcLoc }
          let trans := { trans with
            instructions := trans.instructions.push backInst
            nextLoc := trans.nextLoc + 1 }
          let end_loc := trans.nextLoc
          let trans := Imperative.emitLabel s!"end_loop_{loop_head}" srcLoc trans
          pure (Imperative.patchGotoTargets trans [(goto_end_idx, end_loc)])
        else
          let impStmt ← unwrapCmdExt rn stmt
          Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
      | other => do
        let impStmt ← unwrapCmdExt rn other
        Imperative.Stmt.toGotoInstructions trans.T pname impStmt trans
    coreStmtsToGoto Env pname rn rest trans

/--
Translate a Core procedure into a CProver GOTO context.
Returns the GOTO context together with any local function declarations
that were lifted out of the procedure body. Axioms and distinct
declarations are emitted as ASSUME instructions at the start of the
body. Procedure contracts (requires/ensures/modifies) are attached
as named sub-expressions on the code type.
-/
def procedureToGotoCtx
    (Env : Core.Expression.TyEnv) (p : Core.Procedure)
    (sourceText : Option String := none)
    (axioms : List Core.Axiom := [])
    (distincts :
      List (Core.Expression.Ident × List Core.Expression.Expr) := [])
    (varTypes :
      Core.Expression.Ident → Option Core.Expression.Ty := fun _ => none)
    (asMain : Bool := false)
    : Except Std.Format
        (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  -- Lift local function declarations out of the body
  let (liftedFuncs, body) ← collectFuncDecls p.body
  let pname := Core.CoreIdent.toPretty p.header.name
  if !p.header.typeArgs.isEmpty then
    .error f!"[procedureToGotoCtx] Polymorphic procedures unsupported."
  let ret_ty := CProverGOTO.Ty.Empty
  -- When asMain is true, convert formals to havoc'd locals so CBMC accepts
  -- the function as a standard C entry point (void main(void)).
  let (formals, formals_tys, mainHavocInsts) ← if asMain && !p.header.inputs.isEmpty then do
    let fnames := p.header.inputs.keys.map Core.CoreIdent.toPretty
    let ftys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
    let renamed := fnames.map (CProverGOTO.mkLocalSymbol pname ·)
    let mut insts : Array CProverGOTO.Instruction := #[]
    let mut loc : Nat := 0
    for (rn_name, ty) in renamed.zip ftys do
      let sym := CProverGOTO.Expr.symbol rn_name ty
      insts := insts.push
        { type := .DECL, locationNum := loc, code := CProverGOTO.Code.decl sym,
          sourceLoc := { CProverGOTO.SourceLocation.nil with function := pname } }
      loc := loc + 1
    pure ([], ([] : Map String CProverGOTO.Ty), insts)
  else do
    let f := p.header.inputs.keys.map Core.CoreIdent.toPretty
    let ft ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
    pure (f, f.zip ft, #[])
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol pname ·)
  let outputs := p.header.outputs.keys.map Core.CoreIdent.toPretty
  let new_outputs := outputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals := (Imperative.Block.definedVars body).map Core.CoreIdent.toPretty
  let new_locals := locals.map (CProverGOTO.mkLocalSymbol pname ·)
  -- When asMain, inputs are renamed as locals, not formals
  let inputNames := p.header.inputs.keys.map Core.CoreIdent.toPretty
  let (new_inputs, extraLocals) := if asMain && !p.header.inputs.isEmpty then
    let asLocals := inputNames.map (CProverGOTO.mkLocalSymbol pname ·)
    (asLocals, inputNames)
  else
    (new_formals, [])
  let rn : Std.HashMap String String :=
    (inputNames.zip new_inputs ++ outputs.zip new_outputs ++ locals.zip new_locals).foldl
      (init := {}) fun m (k, v) => m.insert k v
  -- Seed the type environment with renamed input and output parameter types
  let inputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_inputs.zip p.header.inputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let outputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_outputs.zip p.header.outputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let Env' : Core.Expression.TyEnv :=
    Lambda.TEnv.addInNewestContext (T := ⟨Core.ExpressionMetadata, Unit⟩)
      Env (inputEntries ++ outputEntries)
  -- Emit axioms as ASSUME instructions at the start of the body
  let mut axiomInsts : Array CProverGOTO.Instruction := #[]
  let mut axiomLoc : Nat := mainHavocInsts.size
  for ax in axioms do
    let gotoExpr ← Lambda.LExpr.toGotoExprCtx
      (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] ax.e
    -- Skip axioms with quantifiers over types unsupported by CBMC's SMT2 backend
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
  let ans ← if hasCallStmt body then
    coreStmtsToGoto Env' pname rn body
      { instructions := axiomInsts, nextLoc := axiomLoc, T := Env', sourceText := sourceText }
  else do
    let impBody ← body.mapM (unwrapCmdExt rn)
    Imperative.Stmts.toGotoTransform Env' pname impBody (loc := axiomLoc) (sourceText := sourceText)
      |>.map fun ans => { ans with instructions := axiomInsts ++ ans.instructions }
  let ending_insts : Array CProverGOTO.Instruction :=
    #[{ type := .END_FUNCTION, locationNum := ans.nextLoc + 1 }]
  let pgm := { name := pname,
               parameterIdentifiers := new_formals.toArray,
               instructions := mainHavocInsts ++ ans.instructions ++ ending_insts }
  -- Translate procedure contracts to GOTO JSON annotations
  -- Free specs (CheckAttr.Free) are assumed but not checked, so we skip them.
  let mut contracts : List (String × Lean.Json) := []
  -- Collect contract clauses for the function type and DFCC contract symbol.
  -- Non-free requires/ensures become assertions (via CallElim); all clauses
  -- (including free) are needed for the contract::FUNC symbol used by DFCC.
  let preExprs := p.spec.preconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  let postExprsChecked := p.spec.postconditions.values.filter (fun c => c.attr == .Default)
    |>.map (fun c => renameExpr rn c.expr)
  let postExprsAll := p.spec.postconditions.values
    |>.map (fun c => renameExpr rn c.expr)
  let toGotoExpr := Lambda.LExpr.toGotoExprCtx
    (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []
  if !preExprs.isEmpty then
    let preGoto ← preExprs.mapM toGotoExpr
    let preJson ← (preGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_requires",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr preJson.toArray)])]
  -- Function type gets only checked (non-free) ensures for CallElim assertions.
  -- The contract:: symbol (created in Context.toJson) gets all ensures for DFCC.
  if !postExprsChecked.isEmpty then
    let postGoto ← postExprsChecked.mapM toGotoExpr
    let postJson ← (postGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_ensures",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr postJson.toArray)])]
  -- Also collect all ensures (including free) for the DFCC contract symbol
  if !postExprsAll.isEmpty then
    let allPostGoto ← postExprsAll.mapM toGotoExpr
    let allPostJson ← (allPostGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_ensures_all",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr allPostJson.toArray)])]
  if !p.spec.modifies.isEmpty then
    let mut modGoto : List CProverGOTO.Expr := []
    for ident in p.spec.modifies do
      let ty ← match varTypes ident with
        | some (.forAll [] mono) => Lambda.LMonoTy.toGotoType mono
        | _ => pure .Integer
      modGoto := modGoto ++ [CProverGOTO.Expr.symbol (Core.CoreIdent.toPretty ident) ty]
    let modJson ← (modGoto.mapM CProverGOTO.exprToJson).mapError (fun e => f!"{e}")
    contracts := contracts ++ [("#spec_assigns",
      Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr modJson.toArray)])]
  -- Build localTypes map for output parameters and asMain inputs
  let output_tys ← p.header.outputs.values.mapM Lambda.LMonoTy.toGotoType
  let input_tys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    ((outputs.zip output_tys) ++ (extraLocals.zip input_tys)).foldl
      (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := outputs ++ extraLocals ++ locals, contracts := contracts,
      localTypes := localTypes }
  return (ctx, liftedFuncs)

/--
Translate a Core function into a CProver GOTO context.
The body is emitted as a single SET_RETURN_VALUE instruction.
-/
def functionToGotoCtx
    (_Env : Core.Expression.TyEnv) (f : Core.Function)
    : Except Std.Format CoreToGOTO.CProverGOTO.Context := do
  let fname := Core.CoreIdent.toPretty f.name
  if !f.typeArgs.isEmpty then
    .error f!"[functionToGotoCtx] Polymorphic functions unsupported."
  let some body := f.body
    | .error f!"[functionToGotoCtx] Function {fname} has no body."
  let ret_ty ← Lambda.LMonoTy.toGotoType f.output
  let formals := f.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← f.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol fname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  let rn : Std.HashMap String String :=
    (formals.zip new_formals).foldl (init := {}) fun m (k, v) => m.insert k v
  let bodyExpr := renameExpr rn body
  let gotoBody ← Lambda.LExpr.toGotoExpr bodyExpr
  let retInst : CProverGOTO.Instruction :=
    { type := .SET_RETURN_VALUE, code := .set_return_value gotoBody, locationNum := 0 }
  let endInst : CProverGOTO.Instruction :=
    { type := .END_FUNCTION, locationNum := 1 }
  let pgm := { name := fname,
               parameterIdentifiers := new_formals.toArray,
               instructions := #[retInst, endInst] }
  return { program := pgm, formals := formals_tys, ret := ret_ty, locals := [] }

/-- Info for rewriting GOTO function_application nodes to structural operations. -/
structure GotoDatatypeInfo where
  /-- Constructor name → (tag value, [(fieldName, fieldGotoType)]) -/
  constrInfo : Std.HashMap String (Nat × List (String × CProverGOTO.Ty)) := {}
  /-- Tester name → (tag value, struct type) -/
  testerInfo : Std.HashMap String (Nat × CProverGOTO.Ty) := {}
  /-- Selector name → (field name, field type) -/
  selInfo : Std.HashMap String (String × CProverGOTO.Ty) := {}
  /-- Datatype name → full list of (fieldName, fieldGotoType) for the struct -/
  dtFields : Std.HashMap String (List (String × CProverGOTO.Ty)) := {}

/-- Build GotoDatatypeInfo from a Core program's declarations. -/
def collectGotoDatatypeInfo (pgm : Core.Program) : GotoDatatypeInfo :=
  pgm.decls.foldl (init := {}) fun info decl =>
    match decl with
    | .type (.data dts) _ =>
      let mutualNames := dts.map (·.name)
      dts.foldl (init := info) fun info dt =>
      -- Wrap recursive field types in pointers (matching datatypeToSymbolEntry)
      let wrapTy (fty : Lambda.LMonoTy) (gty : CProverGOTO.Ty) : CProverGOTO.Ty :=
        match fty with
        | .tcons name _ => if mutualNames.contains name then .Pointer gty else gty
        | _ => gty
      -- Collect all fields across all constructors (matching struct layout)
      let allFields : List (String × CProverGOTO.Ty) :=
        dt.constrs.flatMap fun c => c.args.filterMap fun (fid, fty) =>
          match fty.toGotoType with
          | .ok gty => some (fid.name, wrapTy fty gty)
          | .error _ => none
      let dtTy := CProverGOTO.Ty.StructTag dt.name
      dt.constrs.zip (List.range dt.constrs.length) |>.foldl (init := { info with
        dtFields := info.dtFields.insert dt.name allFields
      }) fun info (c, tag) =>
        let cFields := c.args.filterMap fun (fid, fty) =>
          match fty.toGotoType with
          | .ok gty => some (fid.name, wrapTy fty gty)
          | .error _ => none
        if cFields.length != c.args.length then info
        else
          let selEntries := c.args.foldl (init := info.selInfo) fun m (fid, fty) =>
            let selName := s!"{dt.name}..{fid.name}!"
            match fty.toGotoType with
            | .ok gty => m.insert selName (fid.name, wrapTy fty gty)
            | .error _ => m
          { info with
            constrInfo := info.constrInfo.insert c.name.name (tag, cFields)
            testerInfo := info.testerInfo.insert c.testerName (tag, dtTy)
            selInfo := selEntries }
    | _ => info

/-- Rewrite a GOTO Expr, replacing function_application nodes for datatype
    constructors/testers/selectors with structural operations. -/
partial def rewriteDatatypeExpr (gi : GotoDatatypeInfo)
    (e : CProverGOTO.Expr) : CProverGOTO.Expr :=
  let go := rewriteDatatypeExpr gi
  match e.id with
  | .functionApplication name =>
    let ops := e.operands.map go
    -- Constructor: from_int(x) → struct { $tag=2, ..., as_int=x, ... }
    if let some (tag, cFields) := gi.constrInfo.get? name then
      if let some allFields := gi.dtFields.get? (getStructName e.type) then
        let tagExpr : CProverGOTO.Expr :=
          { id := .nullary (.constant (toString tag)), type := .Integer }
        let fieldExprs := allFields.map fun (fname, fty) =>
          match cFields.findIdx? (fun (n, _) => n == fname) with
          | some i =>
            let arg := ops[i]?.getD (defaultForTy fty)
            match fty with
            | .Pointer _ =>
              -- Use NULL for pointer fields; the actual value is lost but
              -- testers (tag comparison) still work structurally.
              -- Selectors for pointer fields remain as function_application.
              defaultForTy fty
            | _ => arg
          | none => defaultForTy fty
        { e with id := .struct, operands := tagExpr :: fieldExprs }
      else { e with operands := ops }
    -- Tester: Any..isfrom_int(v) → member(v, $tag) == tag_value
    else if let some (tag, _) := gi.testerInfo.get? name then
      match ops[0]? with
      | some arg =>
        let tagMember : CProverGOTO.Expr :=
          { id := .member "$tag", type := .Integer, operands := [arg] }
        let tagVal : CProverGOTO.Expr :=
          { id := .nullary (.constant (toString tag)), type := .Integer }
        { id := .binary .Equal, type := .Boolean, operands := [tagMember, tagVal] }
      | none => { e with operands := ops }
    -- Selector: field access for non-pointer fields; keep pointer selectors
    -- as function_application (pointer fields are NULL in struct literals)
    else if let some (fieldName, fieldTy) := gi.selInfo.get? name then
      match fieldTy with
      | .Pointer _ => { e with operands := ops }
      | _ => match ops[0]? with
        | some arg => { id := .member fieldName, type := fieldTy, operands := [arg] }
        | none => { e with operands := ops }
    else { e with operands := ops }
  | _ => { e with operands := e.operands.map go }
where
  getStructName (ty : CProverGOTO.Ty) : String :=
    match ty with | .StructTag n => n | _ => ""
  defaultForTy (ty : CProverGOTO.Ty) : CProverGOTO.Expr :=
    match ty with
    | .Boolean => { id := .nullary (.constant "false"), type := .Boolean }
    | .Integer => { id := .nullary (.constant "0"), type := .Integer }
    | .Real => { id := .nullary (.constant "0"), type := .Real }
    | .String => { id := .nullary (.constant "\"\""), type := .String }
    | .Pointer _ => { id := .nullary (.constant "NULL"), type := ty }
    | .StructTag name =>
      -- Build a default struct with tag=0 and default fields
      match gi.dtFields.get? name with
      | some fields =>
        let tagExpr : CProverGOTO.Expr :=
          { id := .nullary (.constant "0"), type := .Integer }
        let fieldExprs := fields.map fun (_, fty) => defaultForTy fty
        { id := .struct, type := ty, operands := tagExpr :: fieldExprs }
      | none => { id := .nullary (.constant "0"), type := ty }
    | _ => { id := .nullary (.constant "0"), type := ty }

/-- Rewrite all GOTO instructions in a context, replacing datatype
    function_application nodes with structural operations. -/
def rewriteDatatypeExprsInCtx (gi : GotoDatatypeInfo)
    (ctx : CoreToGOTO.CProverGOTO.Context) : CoreToGOTO.CProverGOTO.Context :=
  let rw := rewriteDatatypeExpr gi
  let rwInst (inst : CProverGOTO.Instruction) : CProverGOTO.Instruction :=
    { inst with
      guard := rw inst.guard
      code := { inst.code with operands := inst.code.operands.map rw } }
  { ctx with program := { ctx.program with
      instructions := ctx.program.instructions.map rwInst } }

/-- Lower address_of(rvalue) patterns to DECL+ASSIGN temporaries.
    Walks an expression tree; when it finds address_of(e) where e is not
    a symbol, it emits DECL tmp; ASSIGN tmp := e; and replaces with
    address_of(tmp). Returns the rewritten expression. -/
partial def lowerAddressOf (pname : String) (counter : IO.Ref Nat)
    (extraInsts : IO.Ref (Array CProverGOTO.Instruction))
    (extraLocals : IO.Ref (Array (String × CProverGOTO.Ty)))
    (e : CProverGOTO.Expr) : IO CProverGOTO.Expr := do
  let go := lowerAddressOf pname counter extraInsts extraLocals
  match e.id with
  | .unary .AddressOf =>
    match e.operands[0]? with
    | some inner =>
      let inner' ← go inner
      match inner'.id with
      | .nullary (.symbol _) => return { e with operands := [inner'] }
      | _ =>
        -- Hoist rvalue to a temporary
        let n ← counter.get
        counter.set (n + 1)
        let tmpBase := s!"__dt_tmp_{n}"
        let tmpName := CProverGOTO.mkLocalSymbol pname tmpBase
        let tmpSym := CProverGOTO.Expr.symbol tmpName inner'.type
        let srcLoc : CProverGOTO.SourceLocation :=
          { CProverGOTO.SourceLocation.nil with function := pname }
        extraLocals.modify (·.push (tmpBase, inner'.type))
        extraInsts.modify (·.push
          { type := .DECL, locationNum := 999999,
            code := CProverGOTO.Code.decl tmpSym, sourceLoc := srcLoc })
        extraInsts.modify (·.push
          { type := .ASSIGN, locationNum := 999999,
            code := CProverGOTO.Code.assign tmpSym inner', sourceLoc := srcLoc })
        return { e with operands := [tmpSym] }
    | none => return e
  | _ =>
    let mut newOps : List CProverGOTO.Expr := []
    for op in e.operands.reverse do
      let op' ← go op
      newOps := op' :: newOps
    return { e with operands := newOps }

/-- Lower all address_of(rvalue) patterns in a context to temporaries. -/
def lowerAddressOfInCtx (ctx : CoreToGOTO.CProverGOTO.Context)
    : IO CoreToGOTO.CProverGOTO.Context := do
  let pname := ctx.program.name
  let counter ← IO.mkRef (0 : Nat)
  let extraInsts ← IO.mkRef (#[] : Array CProverGOTO.Instruction)
  let extraLocals ← IO.mkRef (#[] : Array (String × CProverGOTO.Ty))
  let mut newInsts : Array CProverGOTO.Instruction := #[]
  for inst in ctx.program.instructions do
    extraInsts.set #[]
    let guard' ← lowerAddressOf pname counter extraInsts extraLocals inst.guard
    let mut codeOps : List CProverGOTO.Expr := []
    for op in inst.code.operands.reverse do
      let op' ← lowerAddressOf pname counter extraInsts extraLocals op
      codeOps := op' :: codeOps
    let extras ← extraInsts.get
    for extra in extras do
      newInsts := newInsts.push extra
    newInsts := newInsts.push { inst with
      guard := guard'
      code := { inst.code with operands := codeOps } }
  -- Build old→new location number mapping and renumber.
  let mut locMap : Std.HashMap Nat Nat := {}
  let mut finalInsts : Array CProverGOTO.Instruction := #[]
  let mut locNum : Nat := 0
  for inst in newInsts do
    if inst.locationNum != 999999 then
      locMap := locMap.insert inst.locationNum locNum
    finalInsts := finalInsts.push { inst with locationNum := locNum }
    locNum := locNum + 1
  -- Fix up GOTO targets
  finalInsts := finalInsts.map fun inst =>
    match inst.target with
    | some tgt => { inst with target := locMap.get? tgt }
    | none => inst
  let newLocals ← extraLocals.get
  return { ctx with
    program := { ctx.program with instructions := finalInsts }
    locals := ctx.locals ++ (newLocals.toList.map (·.1))
    localTypes := newLocals.foldl (init := ctx.localTypes) fun m (n, ty) => m.insert n ty }

def emitProcWithLifted (Env : Core.Expression.TyEnv) (procName : String)
    (ctx : CoreToGOTO.CProverGOTO.Context) (liftedFuncs : List Core.Function)
    (extraSyms : Lean.Json) (moduleName : String := "")
    (gotoDtInfo : GotoDatatypeInfo := {})
    : IO (Lean.Json × Lean.Json) := do
  let ctx := rewriteDatatypeExprsInCtx gotoDtInfo ctx
  -- address_of lowering disabled: CBMC's pointer analysis generates
  -- byte_extract on structs with non-constant-width members (string),
  -- causing crashes in lower_byte_operators. Use NULL for pointer fields.
  let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
  let mut symtabObj := match json.symtab with | .obj m => m | _ => .empty
  let mut gotoFns := match json.goto with
    | .obj m => match m.toList.find? (·.1 == "functions") with
      | some (_, .arr fns) => fns | _ => #[]
    | _ => #[]
  for f in liftedFuncs do
    let funcName := Core.CoreIdent.toPretty f.name
    match functionToGotoCtx Env f with
    | .error e => throw (.userError s!"{e}")
    | .ok fctx =>
      let fjson ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName fctx)
      match fjson.symtab with
      | .obj m => for (k, v) in m.toList do
          symtabObj := symtabObj.insert k v
      | _ => pure ()
      match fjson.goto with
      | .obj m => match m.toList.find? (·.1 == "functions") with
        | some (_, .arr fns) => gotoFns := gotoFns ++ fns
        | _ => pure ()
      | _ => pure ()
  match extraSyms with
  | .obj m => for (k, v) in m.toList do
      symtabObj := symtabObj.insert k v
  | _ => pure ()
  -- Add CBMC default symbols (architecture constants, builtins)
  for (k, v) in CProverGOTO.defaultSymbols (moduleName := moduleName) do
    symtabObj := symtabObj.insert k (Lean.toJson v)
  let symtab := Lean.Json.mkObj [("symbolTable", Lean.Json.obj symtabObj)]
  return (symtab, Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)])

-- Datatype partial evaluation

/--
Datatype info collected from program declarations, used for partial evaluation
of tester/selector applications on known constructors.
-/
structure DatatypeInfo where
  /-- Constructor name → its tester name -/
  constrToTester : Std.HashMap String String := {}
  /-- Tester name → the constructor it tests for -/
  testerToConstr : Std.HashMap String String := {}
  /-- All tester names for a given datatype (keyed by any constructor name) -/
  constrSiblingTesters : Std.HashMap String (List String) := {}
  /-- Selector name (e.g. "Any..as_int!") → (constructor name, field index) -/
  selectorInfo : Std.HashMap String (String × Nat) := {}
  /-- Set of all constructor names -/
  constrNames : Std.HashSet String := {}

/-- Build DatatypeInfo from a Core program's declarations. -/
def collectDatatypeInfo (pgm : Core.Program) : DatatypeInfo :=
  pgm.decls.foldl (init := {}) fun info decl =>
    match decl with
    | .type (.data dts) _ => dts.foldl (init := info) fun info dt =>
      let allTesters := dt.constrs.map (·.testerName)
      dt.constrs.foldl (init := info) fun info c =>
        let cname := c.name.name
        let selectors := (List.range c.args.length).foldl (init := info.selectorInfo) fun m i =>
          match c.args[i]? with
          | some (fieldId, _) =>
            let selName := s!"{dt.name}..{fieldId.name}!"
            m.insert selName (cname, i)
          | none => m
        { info with
          constrToTester := info.constrToTester.insert cname c.testerName
          testerToConstr := info.testerToConstr.insert c.testerName cname
          constrSiblingTesters := info.constrSiblingTesters.insert cname allTesters
          selectorInfo := selectors
          constrNames := info.constrNames.insert cname }
    | _ => info

/-- Collect arguments from a fully-applied constructor: `C(a₁, ..., aₙ)` → `(C, [a₁,...,aₙ])`.
    Returns `none` if the head is not a known constructor. -/
private def matchConstrApp (dtInfo : DatatypeInfo) (e : Lambda.LExpr Core.CoreLParams.mono)
    : Option (String × List (Lambda.LExpr Core.CoreLParams.mono)) :=
  let rec collect (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collect f; (h, as ++ [a])
    | other => (other, [])
  let (head, args) := collect e
  match head with
  | .op _ o _ =>
    if dtInfo.constrNames.contains o.name then some (o.name, args) else none
  | _ => none

/--
Partially evaluate datatype tester and selector applications on known constructors.
- `tester(C(args))` → `true` if tester matches C, `false` otherwise
- `selector_i(C(args))` → `args[i]` if selector matches C
Recurses into subexpressions.
-/
partial def partialEvalDatatypes (dtInfo : DatatypeInfo)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let m : Core.ExpressionMetadata := default
  let rec go (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    match e with
    -- Unary application: tester(arg) or selector(arg)
    | .app appMd (.op opMd fn opTy) arg =>
      let arg' := go arg
      let fname := fn.name
      -- Check if it's a tester applied to a known constructor
      if let some expectedConstr := dtInfo.testerToConstr.get? fname then
        if let some (actualConstr, _) := matchConstrApp dtInfo arg' then
          if expectedConstr == actualConstr then .const m (.boolConst true)
          else .const m (.boolConst false)
        else .app appMd (.op opMd fn opTy) arg'
      -- Check if it's a selector applied to a known constructor
      else if let some (selConstr, idx) := dtInfo.selectorInfo.get? fname then
        if let some (actualConstr, args) := matchConstrApp dtInfo arg' then
          if selConstr == actualConstr then
            match args[idx]? with
            | some argVal => argVal
            | none => .app appMd (.op opMd fn opTy) arg'
          else .app appMd (.op opMd fn opTy) arg'
        else .app appMd (.op opMd fn opTy) arg'
      else .app appMd (.op opMd fn opTy) arg'
    -- Simplify ite(true, t, e) → t, ite(false, t, e) → e
    | .ite md c t el =>
      let c' := go c
      match c' with
      | .const _ (.boolConst true) => go t
      | .const _ (.boolConst false) => go el
      | _ => .ite md c' (go t) (go el)
    -- Simplify eq on identical constructor applications with same args
    | .eq md l r =>
      let l' := go l
      let r' := go r
      -- eq(C(args), C(args)) where both are identical constructor apps
      if let some (lc, largs) := matchConstrApp dtInfo l' then
        if let some (rc, _) := matchConstrApp dtInfo r' then
          -- Different constructors → false
          if lc != rc then .const m (.boolConst false)
          -- Same nullary constructor → true
          else if largs.isEmpty then .const m (.boolConst true)
          else .eq md l' r'
        else .eq md l' r'
      else .eq md l' r'
    -- General recursive cases
    | .app md f a => .app md (go f) (go a)
    | .abs md n ty b => .abs md n ty (go b)
    | .quant md k n ty tr b => .quant md k n ty (go tr) (go b)
    | .const .. | .op .. | .bvar .. | .fvar .. => e
  go e

/-- Apply datatype partial evaluation to all expressions in a Core program. -/
def partialEvalDatatypesInProgram (pgm : Core.Program) : Core.Program :=
  let dtInfo := collectDatatypeInfo pgm
  if dtInfo.constrNames.isEmpty then pgm
  else
    let pe := partialEvalDatatypes dtInfo
    let mapCmd : Core.Command → Core.Command
      | .cmd (.init n ty (some e) md) => .cmd (.init n ty (some (pe e)) md)
      | .cmd (.set n e md) => .cmd (.set n (pe e) md)
      | .cmd (.assert l e md) => .cmd (.assert l (pe e) md)
      | .cmd (.assume l e md) => .cmd (.assume l (pe e) md)
      | .cmd (.cover l e md) => .cmd (.cover l (pe e) md)
      | .call lhs pn args md => .call lhs pn (args.map pe) md
      | other => other
    let rec mapStmt : Core.Statement → Core.Statement
      | .cmd c => .cmd (mapCmd c)
      | .block l b md => .block l (b.map mapStmt) md
      | .ite c t e md => .ite (pe c) (t.map mapStmt) (e.map mapStmt) md
      | .loop g m invs b md => .loop (pe g) (m.map pe) (invs.map pe) (b.map mapStmt) md
      | .exit l md => .exit l md
      | .funcDecl d md => .funcDecl d md
      | .typeDecl tc md => .typeDecl tc md
    let mapCheck (c : Core.Procedure.Check) : Core.Procedure.Check :=
      { c with expr := pe c.expr }
    let decls' := pgm.decls.map fun d =>
      match d with
      | .ax ax md => .ax { ax with e := pe ax.e } md
      | .proc p md =>
        let spec' := { p.spec with
          preconditions := p.spec.preconditions.map (fun (l, c) => (l, mapCheck c))
          postconditions := p.spec.postconditions.map (fun (l, c) => (l, mapCheck c))
        }
        .proc { p with spec := spec', body := p.body.map mapStmt } md
      | other => other
    { pgm with decls := decls' }

-- Datatype axiom generation

/--
Generate datatype axioms for CBMC: tester and selector axioms for each constructor.
For constructor `C(f₁:T₁,...,fₙ:Tₙ)` of datatype `D`, generates:
  - `∀ x₁:T₁,...,xₙ:Tₙ. D..isC(C(x₁,...,xₙ)) = true`   (tester positive)
  - `∀ x₁:T₁,...,xₙ:Tₙ. D..isC'(C(x₁,...,xₙ)) = false`  (tester negative, for each other C')
  - `∀ x₁:T₁,...,xₙ:Tₙ. D..fᵢ!(C(x₁,...,xₙ)) = xᵢ`     (selector)
Only generates axioms for constructors whose field types are all GOTO-translatable.
-/
def generateDatatypeAxioms (pgm : Core.Program) : List Core.Axiom :=
  let m : Core.ExpressionMetadata := default
  let mkOp (name : String) (ty : Lambda.LMonoTy) : Lambda.LExpr Core.CoreLParams.mono :=
    .op m ⟨name, ()⟩ (some ty)
  pgm.decls.flatMap fun decl =>
    match decl with
    | .type (.data dts) _ => dts.flatMap fun dt => dt.constrs.flatMap fun c =>
      if !c.args.all (fun (_, ty) => ty.toGotoType matches .ok _) then []
      else
        let dtTy : Lambda.LMonoTy := .tcons dt.name []
        let testerTy : Lambda.LMonoTy := .arrow dtTy .bool
        let fieldTys := c.args.map (fun (_, ty) => ty)
        let constrTy := fieldTys.foldr (fun t acc => .arrow t acc) dtTy
        let n := c.args.length
        let bvars := (List.range n).map fun i =>
          Lambda.LExpr.bvar (T := Core.CoreLParams.mono) m (n - 1 - i)
        let constrApp := bvars.foldl (fun acc arg => .app m acc arg) (mkOp c.name.name constrTy)
        let quantify (body : Lambda.LExpr Core.CoreLParams.mono) :=
          let names := c.args.map (fun (id, _) => id.name)
          (names.zip fieldTys).foldr
            (fun (name, ty) acc => Lambda.LExpr.all m name (some ty) acc) body
        let testerPos :=
          let ax := quantify (.eq m (.app m (mkOp c.testerName testerTy) constrApp) (.const m (.boolConst true)))
          { name := s!"dt_{dt.name}_{c.name.name}_tester_pos", e := ax : Core.Axiom }
        let testerNegs := dt.constrs.filterMap fun c' =>
          if c'.name.name == c.name.name then .none
          else
            let ax := quantify (.eq m (.app m (mkOp c'.testerName testerTy) constrApp) (.const m (.boolConst false)))
            some { name := s!"dt_{dt.name}_{c.name.name}_not_{c'.name.name}", e := ax : Core.Axiom }
        let selectors := (List.range n).filterMap fun i =>
          c.args[i]?.map fun (fieldId, fieldTy) =>
          let selName := s!"{dt.name}..{fieldId.name}!"
          let selTy : Lambda.LMonoTy := .arrow dtTy fieldTy
          let ax := quantify (.eq m (.app m (mkOp selName selTy) constrApp) bvars[i]!)
          { name := s!"dt_{dt.name}_{c.name.name}_sel_{fieldId.name}", e := ax : Core.Axiom }
        [testerPos] ++ testerNegs ++ selectors
    | _ => []

-- Recursive function body axioms

/-- Unroll a recursive function body by substituting recursive calls with the
    body, up to a given depth. At depth 0, recursive calls are left as-is. -/
private partial def unrollRecBody (fname : String)
    (formals : List Core.CoreIdent)
    (body : Lambda.LExpr Core.CoreLParams.mono)
    (depth : Nat) (e : Lambda.LExpr Core.CoreLParams.mono)
    : Lambda.LExpr Core.CoreLParams.mono :=
  if depth == 0 then e
  else
    let rec go (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
      -- Check if this is a call to fname
      let (head, args) := collectAppRec e
      match head with
      | .op _ o _ =>
        let args' := args.map go
        if o.name == fname && args'.length == formals.length then
          -- Substitute formals with args in body, then unroll one more level
          let substituted := Lambda.LExpr.substFvars body (formals.zip args')
          unrollRecBody fname formals body (depth - 1) substituted
        else rebuildAppRec head args'
      | _ =>
        match e with
        | .const .. | .op .. | .bvar .. | .fvar .. => e
        | .abs m n ty b => .abs m n ty (go b)
        | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
        | .app m f a => .app m (go f) (go a)
        | .ite m c t el => .ite m (go c) (go t) (go el)
        | .eq m l r => .eq m (go l) (go r)
    go e
where
  collectAppRec (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collectAppRec f; (h, as ++ [a])
    | other => (other, [])
  rebuildAppRec (head : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono :=
    args.foldl (fun acc arg => .app default acc arg) head

/-- Generate axioms for recursive functions: `∀ inputs. f(inputs) = body`.
    Unrolls the recursion to the given depth (each level substitutes recursive
    calls with the body). -/
def generateRecFuncAxioms (pgm : Core.Program) (unrollDepth : Nat := 2)
    : List Core.Axiom :=
  let m : Core.ExpressionMetadata := default
  pgm.decls.flatMap fun d =>
    match d.getFunc? with
    | some f =>
      if !f.isRecursive || f.typeArgs.length > 0 then []
      else match f.body with
      | none => []
      | some body =>
        -- Skip functions with parameters that can't be encoded in GOTO
        if !f.inputs.values.all (fun ty => ty.toGotoType matches .ok _) then []
        else if !(f.output.toGotoType matches .ok _) then []
        else
        let fname := f.name.name
        let formals := f.inputs.keys
        let formalTys := f.inputs.values
        -- Build f(x₁,...,xₙ)
        let fTy := formalTys.foldr (fun t acc => .arrow t acc) f.output
        let fOp := Lambda.LExpr.op (T := Core.CoreLParams.mono) m ⟨fname, ()⟩ (some fTy)
        let fApp := formals.foldl (fun acc x =>
          .app m acc (.fvar m x (some (f.inputs.find? x |>.getD .bool)))) fOp
        -- Generate axioms for each unrolling depth
        (List.range (unrollDepth + 1)).map fun depth =>
          let unrolledBody := unrollRecBody fname formals body depth body
          -- Wrap in ∀ quantifiers
          let axiomBody := Lambda.LExpr.eq m fApp unrolledBody
          let quantified := (formals.zip formalTys).foldr
            (fun (x, ty) acc => Lambda.LExpr.all m x.name (some ty) acc) axiomBody
          { name := s!"rec_{fname}_depth_{depth}", e := quantified : Core.Axiom }
    | none => []

-- Function definition inlining

/--
Inline function bodies in an expression. For each fully-applied call `f(a₁, ..., aₙ)`
where `f` has a known body, replace it with `body[a₁/x₁, ..., aₙ/xₙ]`.
This avoids emitting uninterpreted `mathematical_function` symbols in GOTO.
-/
partial def inlineFuncDefs
    (defs : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  let rec go (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    let (head, args) := collectApp e
    match head with
    | .op _ o _ =>
      let args' := args.map go
      match defs.find? (fun (n, _, _) => n == o.name) with
      | some (_, formals, body) =>
        if args'.length == formals.length then
          go (Lambda.LExpr.substFvars body (formals.zip args'))
        else rebuildApp head args'
      | none => rebuildApp head args'
    | _ =>
      match e with
      | .const .. | .op .. | .bvar .. | .fvar .. => e
      | .abs m n ty b => .abs m n ty (go b)
      | .quant m k n ty tr b => .quant m k n ty (go tr) (go b)
      | .app m f a => .app m (go f) (go a)
      | .ite m c t el => .ite m (go c) (go t) (go el)
      | .eq m l r => .eq m (go l) (go r)
  go e
where
  collectApp (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collectApp f; (h, as ++ [a])
    | other => (other, [])
  rebuildApp (head : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono :=
    args.foldl (fun acc arg => .app default acc arg) head

/-- Build the function definition map from a program's declarations. -/
def collectFuncDefs (pgm : Core.Program)
    : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono) :=
  pgm.decls.filterMap fun d => do
    let f ← d.getFunc?
    let body ← f.body
    guard (!f.isRecursive)
    guard (f.typeArgs.isEmpty)
    some (f.name.name, f.inputs.keys, body)

/-- Collect recursive function definitions with GOTO-translatable types. -/
def collectRecFuncDefs (pgm : Core.Program)
    : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono) :=
  pgm.decls.filterMap fun d => do
    let f ← d.getFunc?
    let body ← f.body
    guard f.isRecursive
    guard (f.typeArgs.isEmpty)
    guard (f.inputs.values.all (fun ty => ty.toGotoType matches .ok _))
    guard (f.output.toGotoType matches .ok _)
    some (f.name.name, f.inputs.keys, body)

/-- Inline recursive function calls with bounded unrolling.
    At depth 0, recursive calls are left as-is (uninterpreted). -/
partial def inlineRecFuncDefs
    (recDefs : List (String × List Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
    (maxDepth : Nat)
    (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
  go maxDepth e
where
  go (depth : Nat) (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono :=
    if depth == 0 then e
    else
      let (head, args) := collectApp e
      match head with
      | .op _ o _ =>
        let args' := args.map (go depth)
        match recDefs.find? (fun (n, _, _) => n == o.name) with
        | some (_, formals, body) =>
          if args'.length == formals.length then
            go (depth - 1) (Lambda.LExpr.substFvars body (formals.zip args'))
          else rebuildApp head args'
        | none => rebuildApp head args'
      | _ =>
        match e with
        | .const .. | .op .. | .bvar .. | .fvar .. => e
        | .abs m n ty b => .abs m n ty (go depth b)
        | .quant m k n ty tr b => .quant m k n ty (go depth tr) (go depth b)
        | .app m f a => .app m (go depth f) (go depth a)
        | .ite m c t el => .ite m (go depth c) (go depth t) (go depth el)
        | .eq m l r => .eq m (go depth l) (go depth r)
  collectApp (e : Lambda.LExpr Core.CoreLParams.mono)
      : Lambda.LExpr Core.CoreLParams.mono × List (Lambda.LExpr Core.CoreLParams.mono) :=
    match e with
    | .app _ f a => let (h, as) := collectApp f; (h, as ++ [a])
    | other => (other, [])
  rebuildApp (head : Lambda.LExpr Core.CoreLParams.mono)
      (args : List (Lambda.LExpr Core.CoreLParams.mono))
      : Lambda.LExpr Core.CoreLParams.mono :=
    args.foldl (fun acc arg => .app default acc arg) head

/-- Inline function definitions in all expressions of a Core program. -/
def inlineFuncDefsInProgram (pgm : Core.Program) : Core.Program :=
  let defs := collectFuncDefs pgm
  if defs.isEmpty then pgm
  else
    let inl := inlineFuncDefs defs
    let mapCmd : Core.Command → Core.Command
      | .cmd (.init n ty (some e) md) => .cmd (.init n ty (some (inl e)) md)
      | .cmd (.set n e md) => .cmd (.set n (inl e) md)
      | .cmd (.assert l e md) => .cmd (.assert l (inl e) md)
      | .cmd (.assume l e md) => .cmd (.assume l (inl e) md)
      | .cmd (.cover l e md) => .cmd (.cover l (inl e) md)
      | .call lhs pn args md => .call lhs pn (args.map inl) md
      | other => other
    let rec mapStmt : Core.Statement → Core.Statement
      | .cmd c => .cmd (mapCmd c)
      | .block l b md => .block l (b.map mapStmt) md
      | .ite c t e md => .ite (inl c) (t.map mapStmt) (e.map mapStmt) md
      | .loop g m invs b md => .loop (inl g) (m.map inl) (invs.map inl) (b.map mapStmt) md
      | .exit l md => .exit l md
      | .funcDecl d md => .funcDecl d md
      | .typeDecl tc md => .typeDecl tc md
    let mapCheck (c : Core.Procedure.Check) : Core.Procedure.Check :=
      { c with expr := inl c.expr }
    let decls' := pgm.decls.map fun d =>
      match d with
      | .ax ax md => .ax { ax with e := inl ax.e } md
      | .proc p md =>
        let spec' := { p.spec with
          preconditions := p.spec.preconditions.map (fun (l, c) => (l, mapCheck c))
          postconditions := p.spec.postconditions.map (fun (l, c) => (l, mapCheck c))
        }
        .proc { p with spec := spec', body := p.body.map mapStmt } md
      | other => other
    { pgm with decls := decls' }

/-- Inline recursive function calls with bounded unrolling (depth 1).
    Only inlines one level — the recursive call in the body is left as-is. -/
def inlineRecFuncDefsInProgram (pgm : Core.Program) : Core.Program :=
  let recDefs := collectRecFuncDefs pgm
  if recDefs.isEmpty then pgm
  else
    -- Depth 1: substitute the body once, leaving recursive calls uninterpreted
    let inl := inlineRecFuncDefs recDefs 1
    let mapCmd : Core.Command → Core.Command
      | .cmd (.init n ty (some e) md) => .cmd (.init n ty (some (inl e)) md)
      | .cmd (.set n e md) => .cmd (.set n (inl e) md)
      | .cmd (.assert l e md) => .cmd (.assert l (inl e) md)
      | .cmd (.assume l e md) => .cmd (.assume l (inl e) md)
      | .cmd (.cover l e md) => .cmd (.cover l (inl e) md)
      | .call lhs pn args md => .call lhs pn (args.map inl) md
      | other => other
    let rec mapStmt : Core.Statement → Core.Statement
      | .cmd c => .cmd (mapCmd c)
      | .block l b md => .block l (b.map mapStmt) md
      | .ite c t e md => .ite (inl c) (t.map mapStmt) (e.map mapStmt) md
      | .loop g m invs b md => .loop (inl g) (m.map inl) (invs.map inl) (b.map mapStmt) md
      | .exit l md => .exit l md
      | .funcDecl d md => .funcDecl d md
      | .typeDecl tc md => .typeDecl tc md
    let decls' := pgm.decls.map fun d =>
      match d with
      | .proc p md =>
        .proc { p with body := p.body.map mapStmt } md
      | other => other
    { pgm with decls := decls' }

end Strata
