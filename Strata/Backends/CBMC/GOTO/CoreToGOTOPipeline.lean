/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.CollectSymbols
public import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import Strata.Transform.ProcedureInlining

/-! ## Core-to-GOTO translation pipeline

Translates Core procedures and functions into CProver GOTO contexts.

### Known limitations

#### Program-level declarations (`Core.Decl`)
- **`Decl.ax`** (axioms): Emitted as ASSUME instructions at the start of each
  procedure body.
- **`Decl.distinct`**: Emitted as pairwise `!=` ASSUME instructions at the
  start of each procedure body.

#### Procedure contracts (`Core.Procedure.Spec`)
Preconditions and postconditions are emitted as `#spec_requires` and
`#spec_ensures` named sub-expressions on the code type in the symbol table.
These are recognized by `goto-instrument --apply-code-contracts` (DFCC).

The following are not yet handled:
- **`free requires`/`free ensures`**: Silently skipped (not emitted as contract
  annotations). CBMC's DFCC does not have a direct equivalent of Boogie's free specs.

#### Procedure calls
- **`CmdExt.call`**: Handled by `coreStmtsToGoto`, which emits FUNCTION_CALL
  instructions directly. The `unwrapCmdExt` path (used when no calls are present)
  returns an error on calls as a safety check.
-/

namespace Strata

public section

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
  | .set name e md => .set (renameIdent rn name) (e.map (renameExpr rn)) md
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
    .ok (.ite (c.map (renameExpr rn)) t' e' md)
  | .loop g m i body md => do
    let body' ← body.mapM (unwrapCmdExt rn)
    .ok (.loop (g.map (renameExpr rn)) (m.map (renameExpr rn))
      (i.map (fun (l, e) => (l, renameExpr rn e))) body' md)
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
      | .cmd (.call procName callArgs _md) =>
        let lhs := Core.CallArg.getLhs callArgs
        let args := Core.CallArg.getInputExprs callArgs
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
        let calleeExpr := CProverGOTO.Expr.symbol procName
          (CProverGOTO.Ty.mkCode (argExprs.map (·.type)) lhsExpr.type)
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
          let cond_expr ← match cond with
            | .det e => toExpr (renameExpr rn e)
            | .nondet => pure { id := .side_effect .Nondet, type := .Boolean, operands := [] : CProverGOTO.Expr }
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
          let guard_expr ← match guard with
            | .det e => toExpr (renameExpr rn e)
            | .nondet => pure { id := .side_effect .Nondet, type := .Boolean, operands := [] : CProverGOTO.Expr }
          let (trans, goto_end_idx) :=
            Imperative.emitCondGoto (CProverGOTO.Expr.not guard_expr) srcLoc trans
          let trans ← coreStmtsToGoto Env pname rn body trans
          let mut backGuard := CProverGOTO.Expr.true
          for (_, inv) in invariants do
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
    : Except Std.Format
        (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  -- Lift local function declarations out of the body
  let (liftedFuncs, body) ← collectFuncDecls p.body
  let pname := Core.CoreIdent.toPretty p.header.name
  if !p.header.typeArgs.isEmpty then
    .error f!"[procedureToGotoCtx] Polymorphic procedures unsupported."
  let ret_ty := CProverGOTO.Ty.Empty
  let formals := p.header.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol pname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  let outputs := p.header.outputs.keys.map Core.CoreIdent.toPretty
  let new_outputs := outputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals := (Imperative.Block.definedVars body).map Core.CoreIdent.toPretty
  let new_locals := locals.map (CProverGOTO.mkLocalSymbol pname ·)
  let rn : Std.HashMap String String :=
    (formals.zip new_formals ++ outputs.zip new_outputs ++ locals.zip new_locals).foldl
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
  -- Emit axioms as ASSUME instructions at the start of the body
  let mut axiomInsts : Array CProverGOTO.Instruction := #[]
  let mut axiomLoc : Nat := 0
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
               instructions := ans.instructions ++ ending_insts }
  -- Translate procedure contracts to GOTO JSON annotations
  -- Free specs (CheckAttr.Free) are assumed but not checked, so we skip them.
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
  -- Build localTypes map for output parameters (so they get proper types in symbol table)
  let output_tys ← p.header.outputs.values.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    (outputs.zip output_tys).foldl (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := outputs ++ locals, contracts := contracts,
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

/--
Emit a procedure context and its lifted functions as combined
symtab/goto JSON.
-/
def emitProcWithLifted (Env : Core.Expression.TyEnv) (procName : String)
    (ctx : CoreToGOTO.CProverGOTO.Context) (liftedFuncs : List Core.Function)
    (extraSyms : Lean.Json) (moduleName : String)
    : IO (Lean.Json × Lean.Json) := do
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
  let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := moduleName)
  return (symtab, Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)])

/-! ## High-level pipeline steps

Composable building blocks for translating Core programs to GOTO.
-/

/-- Type-check a Core program using the standard context and factory.
    Returns the type-checked program and the resulting type environment. -/
public def typeCheckCore (program : Core.Program)
    (factory : @Lambda.Factory Core.CoreLParams := Core.Factory)
    : Except String (Core.Program × Core.Expression.TyEnv) := do
  let Ctx := { Lambda.LContext.default with
    functions := factory, knownTypes := Core.KnownTypes }
  let Env := Lambda.TEnv.default
  match Core.Program.typeCheck Ctx Env program with
  | .ok (tcPgm, Env') => return (tcPgm, Env')
  | .error e => throw s!"{e.format none}"

/-- Translate a type-checked Core program to CProver GOTO JSON files.
    Finds an entry-point procedure from `entryPoints` (defaulting to
    `["main", "__main__"]`), translates it to GOTO, and writes
    `<baseName>.symtab.json` and `<baseName>.goto.json`. -/
public def coreToGotoFiles (tcPgm : Core.Program) (Env : Core.Expression.TyEnv)
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
  -- Always use "main" as the GOTO function name (CBMC expects --function main)
  let procName := "main"
  let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
  let distincts := tcPgm.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  match procedureToGotoCtx Env p sourceText (axioms := axioms) (distincts := distincts)
        with
  | .error e => throw s!"{e}"
  | .ok (ctx, liftedFuncs) =>
    let extraSyms ← match collectExtraSymbols tcPgm with
      | .ok s => pure (Lean.toJson s)
      | .error e => throw s!"{e}"
    let (symtab, goto) ←
      match ← emitProcWithLifted Env procName ctx liftedFuncs extraSyms (moduleName := baseName) |>.toBaseIO with
      | .ok r => pure r
      | .error e => throw s!"{e}"
    let symTabFile := s!"{baseName}.symtab.json"
    let gotoFile := s!"{baseName}.goto.json"
    match ← writeJsonFile symTabFile symtab |>.toBaseIO with
    | .ok () => pure ()
    | .error e => throw s!"Error writing {symTabFile}: {e}"
    match ← writeJsonFile gotoFile goto |>.toBaseIO with
    | .ok () => pure ()
    | .error e => throw s!"Error writing {gotoFile}: {e}"
    let _ ← IO.println s!"Written {symTabFile} and {gotoFile}" |>.toBaseIO

/--
Inline procedures, type-check, and emit CProver GOTO JSON files.
-/
public def inlineCoreToGotoFiles (program : Core.Program)
    (baseName : String)
    (sourceText : Option String := none)
    (entryPoints : List String := ["main", "__main__"])
    (factory : @Lambda.Factory Core.CoreLParams := Core.Factory)
    : EIO String Unit := do
  let phase := Core.procedureInliningPipelinePhase
    { doInline := (fun _caller callee _ => callee ≠ "main"), maxIters := some 10 }
  let inlined ← match Core.Transform.run program (fun prog => do
      let (_, prog') ← phase.transform prog; return prog') with
    | .ok r => pure r
    | .error msg => throw (toString msg)
  let (tcPgm, Env) ← match typeCheckCore inlined factory with
    | .ok r => pure r
    | .error msg => throw msg
  coreToGotoFiles tcPgm Env baseName sourceText entryPoints

end -- public section

end Strata
