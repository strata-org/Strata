/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import Strata.Backends.CBMC.GOTO.HoistFnApps
import Strata.Transform.ProcedureInlining
public import Strata.Languages.Core.Factory
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.DefaultSymbols
import Strata.Languages.Core.ProgramType
import Strata.Util.Json

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

/-- Rewrite a `Core.CoreIdent` according to a name-substitution map. Names absent
from `rn` pass through unchanged; metadata is preserved. -/
def renameIdent (rn : Std.HashMap String String) (id : Core.CoreIdent) : Core.CoreIdent :=
  match rn[id.name]? with
  | some new => ⟨new, id.metadata⟩
  | none => id

/-- Rewrite all free variable names in a `Core.Expression.Expr` according to `rn`.
Recurses through binders and other expression forms; bound-variable indices are
unchanged. -/
partial def renameExpr
    (rn : Std.HashMap String String)
    : Core.Expression.Expr → Core.Expression.Expr
  | .fvar m name ty => .fvar m (renameIdent rn name) ty
  | .app m f e => .app m (renameExpr rn f) (renameExpr rn e)
  | .abs m name ty e => .abs m name ty (renameExpr rn e)
  | .quant m qk name ty tr e => .quant m qk name ty (renameExpr rn tr) (renameExpr rn e)
  | .ite m c t e => .ite m (renameExpr rn c) (renameExpr rn t) (renameExpr rn e)
  | .eq m e1 e2 => .eq m (renameExpr rn e1) (renameExpr rn e2)
  | e => e

/-- Apply a name-substitution map to identifiers and expressions inside an
`Imperative.Cmd` over Core expressions. -/
def renameCmd
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
        let lhs := Imperative.CallArg.getLhs callArgs
        let args := Core.CallArg.getInputExprs callArgs
        let renamedLhs := lhs.map (renameIdent rn)
        let renamedArgs := args.map (renameExpr rn)
        -- Inout args arrive as typeless fvars; `toGotoExprCtx` only accepts
        -- `(some ty)`, so recover the type from the typing env.
        let typedArgs := renamedArgs.map fun e => match e with
          | .fvar m id none =>
            match trans.T.context.types.find? id with
            | some lty => Lambda.LExpr.fvar m id (some lty.toMonoTypeUnsafe)
            | none => e
          | _ => e
        let argExprs ← typedArgs.mapM toExpr
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
          if !invariants.isEmpty then
            -- CBMC stores the individual loop-invariant clauses as the operands
            -- of the `#spec_loop_invariant` annotation (cf. the C front end).
            let invExprs ← invariants.mapM (fun (_, inv) => toExpr (renameExpr rn inv))
            let invAnnotation : CProverGOTO.Expr :=
              { id := .multiary .And, type := CProverGOTO.Ty.Boolean,
                operands := invExprs }
            backGuard := backGuard.setNamedField "#spec_loop_invariant" invAnnotation
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
Translate a Core procedure into a CProver GOTO context. Axioms and distinct
declarations are emitted as ASSUME instructions at the start of the
body. Procedure contracts (requires/ensures) are attached
as named sub-expressions on the code type.
-/
def procedureToGotoCtx
    (Env : Core.Expression.TyEnv) (p : Core.Procedure)
    (sourceText : Option String := none)
    (axioms : List Core.Axiom := [])
    (distincts :
      List (Core.Expression.Ident × List Core.Expression.Expr) := [])
    : Except Std.Format CoreToGOTO.CProverGOTO.Context := do
  -- TODO: This translation could be split into a two-stage transformation:
  -- 1. structured → cfg (via StructuredToUnstructured)
  -- 2. cfg → CProverGOTO (always operates on CFG, no pattern matching needed)
  let body ← p.body.getStructured.mapError fun s => f!"{s}"
  let pname := Core.CoreIdent.toPretty p.header.name
  if !p.header.typeArgs.isEmpty then
    .error f!"[procedureToGotoCtx] Polymorphic procedures unsupported."
  let ret_ty := CProverGOTO.Ty.Empty
  let formals := p.header.inputs.keys.map Core.CoreIdent.toPretty
  let formals_tys ← p.header.inputs.values.mapM Lambda.LMonoTy.toGotoType
  let new_formals := formals.map (CProverGOTO.mkFormalSymbol pname ·)
  let formals_tys : Map String CProverGOTO.Ty := formals.zip formals_tys
  -- Inout params are in both `inputs` and `outputs`; drop them from `outputs`
  -- so their local-symbol entry can't shadow the formal binding in `rn`.
  let formalsSet : Std.HashSet String := formals.foldl (·.insert ·) ∅
  let pureOutputPairs := (p.header.outputs.keys.map Core.CoreIdent.toPretty).zip
    p.header.outputs.values |>.filter fun (n, _) => !formalsSet.contains n
  let outputs := pureOutputPairs.map (·.1)
  let outputTys := pureOutputPairs.map (·.2)
  let new_outputs := outputs.map (CProverGOTO.mkLocalSymbol pname ·)
  let locals := (Imperative.Block.definedVars body false).map Core.CoreIdent.toPretty
  let new_locals := locals.map (CProverGOTO.mkLocalSymbol pname ·)
  -- Base-name substitutions (`x → test::1::x`, etc.).
  let basePairs := formals.zip new_formals ++ outputs.zip new_outputs ++ locals.zip new_locals
  -- Core encodes `old(x)` as a single fvar named `"old x"` (`CoreIdent.mkOld`).
  -- Mirror every base entry with its `old`-prefixed counterpart so `renameExpr`
  -- rewrites `"old x" → "old test::1::x"` before `oldAwareSymbol` strips the
  -- `"old "` prefix; otherwise the pre-state operand is emitted as the bare,
  -- unnamespaced `symbol("x")`, which is unbound in cprover's namespace.
  let oldPairs := basePairs.map fun (k, v) =>
    (Core.CoreIdent.oldStr ++ k, Core.CoreIdent.oldStr ++ v)
  let rn : Std.HashMap String String :=
    (basePairs ++ oldPairs).foldl
      (init := {}) fun m (k, v) => m.insert k v
  -- Seed the type environment with renamed input and output parameter types
  let inputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_formals.zip p.header.inputs.values).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let outputEntries : Map Core.Expression.Ident Core.Expression.Ty :=
    (new_outputs.zip outputTys).map fun (n, ty) =>
      (((n : Core.CoreIdent)), .forAll [] ty)
  let Env' : Core.Expression.TyEnv :=
    Lambda.TEnv.addInNewestContext (T := ⟨Core.ExpressionMetadata, Unit⟩)
      Env (Strata.Util.HMap.ofList (inputEntries ++ outputEntries))
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
  let output_tys ← outputTys.mapM Lambda.LMonoTy.toGotoType
  let localTypes : Std.HashMap String CProverGOTO.Ty :=
    (outputs.zip output_tys).foldl (init := {}) fun m (k, v) => m.insert k v
  let ctx : CoreToGOTO.CProverGOTO.Context :=
    { program := pgm, formals := formals_tys, ret := ret_ty,
      locals := outputs ++ locals, contracts := contracts,
      localTypes := localTypes }
  return ctx

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
Translate the transitive closure of eligible top-level Core functions
reachable — via `function_application` nodes — from the seed names. A
function is *eligible* when it is monomorphic and carries a body; its GOTO
translation is a real function body (`functionToGotoCtx`) that CBMC's symex
can execute once call sites are hoisted (`Context.hoistFnApps`). This
closure includes recursive functions; `collectHoistableFuncCtxs` decides
whether they keep their bodies. Bodiless functions are not emitted: their
applications remain uninterpreted. A function whose body fails to translate is
skipped (left uninterpreted) rather than failing the pipeline; the skipped
names are returned so the caller can warn, since a silently uninterpreted
call otherwise looks like a clean verification result.
-/
private partial def collectUsedFuncCtxs
    (Env : Core.Expression.TyEnv)
    (eligible : Std.HashMap String Core.Function)
    (queue : List String) (defined : Std.HashSet String)
    (acc : List (String × CoreToGOTO.CProverGOTO.Context))
    (dropped : List (String × Std.Format)) :
    List (String × CoreToGOTO.CProverGOTO.Context) × Std.HashSet String
      × List (String × Std.Format) :=
  match queue with
  | [] => (acc, defined, dropped)
  | n :: rest =>
    if defined.contains n then
      collectUsedFuncCtxs Env eligible rest defined acc dropped
    else
      match eligible.get? n with
      | none => collectUsedFuncCtxs Env eligible rest defined acc dropped
      | some f =>
        match functionToGotoCtx Env f with
        | .error e =>
          collectUsedFuncCtxs Env eligible rest defined acc ((n, e) :: dropped)
        | .ok fctx =>
          let more := (CProverGOTO.collectFnApps fctx.program).map (·.name)
          collectUsedFuncCtxs Env eligible (rest ++ more) (defined.insert n)
            (acc ++ [(n, fctx)]) dropped

/--
Names of the emitted functions that lie on a call cycle among themselves:
`n` is recursive when it reaches itself through the defined callees of the
emitted bodies. Calls to functions outside `defined` stay uninterpreted, so
they do not close a cycle.
-/
private def recursiveFuncs
    (usedCtxs : List (String × CoreToGOTO.CProverGOTO.Context))
    (defined : Std.HashSet String) : List String :=
  let callees : Std.HashMap String (List String) :=
    usedCtxs.foldl (init := {}) fun m (n, c) =>
      m.insert n ((CProverGOTO.collectFnApps c.program).map (·.name) |>.filter defined.contains)
  -- Depth-first reachability, bounded by the number of emitted functions.
  let reaches (start : String) : Bool := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut stack := callees.getD start []
    for _ in [0:usedCtxs.length * usedCtxs.length + 1] do
      match stack with
      | [] => return false
      | n :: rest =>
        stack := rest
        if n == start then return true
        if !seen.contains n then
          seen := seen.insert n
          stack := callees.getD n [] ++ stack
    return false
  usedCtxs.filterMap fun (n, _) => if reaches n then some n else none

/--
Like `collectUsedFuncCtxs`, but additionally keeps out of `defined` every
function that has an application hoisting must leave in place — under a
quantifier, in a spec annotation (`CProverGOTO.residualFnApps`), or in the
procedure's contracts. Such an application needs its callee to remain a
`mathematical_function` symbol, which a function with an emitted GOTO body
cannot also be, so such a function stays uninterpreted everywhere and none
of its applications is hoisted.

Unless `hoistRecursive` is set, functions on a call cycle
(`recursiveFuncs`) are kept out of `defined` as well. Symex unwinds a
recursive GOTO call just as it unwinds a loop, so a call whose recursion
depth is symbolic (e.g. a list-processing prelude function on a list of
symbolic length) diverges unless cbmc is given an `--unwind` bound; only
callers that supply one should opt in.

Excluding a function can only shrink the set of emitted bodies, so the loop
terminates.
-/
private partial def collectHoistableFuncCtxs
    (Env : Core.Expression.TyEnv)
    (eligible : Std.HashMap String Core.Function)
    (ctx : CoreToGOTO.CProverGOTO.Context)
    (hoistRecursive : Bool) :
    List (String × CoreToGOTO.CProverGOTO.Context) × Std.HashSet String
      × List (String × Std.Format) :=
  let seeds := (CProverGOTO.collectFnApps ctx.program).map (·.name)
  let (usedCtxs, defined, dropped) := collectUsedFuncCtxs Env eligible seeds {} [] []
  let residual := CProverGOTO.residualFnApps ctx.program
    ++ ctx.contracts.flatMap (fun (_, j) => CProverGOTO.jsonFnAppNames j)
    ++ usedCtxs.flatMap (fun (_, c) => CProverGOTO.residualFnApps c.program)
  let recursive := if hoistRecursive then [] else recursiveFuncs usedCtxs defined
  let excluded := (residual ++ recursive).filter defined.contains
  if excluded.isEmpty then (usedCtxs, defined, dropped)
  else
    collectHoistableFuncCtxs Env (excluded.foldl (init := eligible) (·.erase ·)) ctx
      hoistRecursive

/--
Emit a procedure context and its associated functions as combined
symtab/goto JSON. Emits a real GOTO function body for every eligible
top-level function in `topLevelFuncs` reachable from the procedure
(`collectHoistableFuncCtxs`), then hoists their applications to statement-level
`FUNCTION_CALL` instructions (`Context.hoistFnApps`) so CBMC executes the
bodies instead of treating the calls as uninterpreted. With the default
`topLevelFuncs := []` nothing is hoisted. `Env` is the type environment the
function bodies are translated in. Recursive functions stay uninterpreted
unless `hoistRecursive` is set; set it only when cbmc runs with an
`--unwind` bound.
-/
def emitProc (procName : String)
    (ctx : CoreToGOTO.CProverGOTO.Context)
    (extraSyms : Lean.Json) (moduleName : String)
    (topLevelFuncs : List Core.Function := [])
    (Env : Core.Expression.TyEnv := Lambda.TEnv.default)
    (hoistRecursive : Bool := false)
    : IO (Lean.Json × Lean.Json) := do
  let eligible : Std.HashMap String Core.Function :=
    topLevelFuncs.foldl (init := {}) fun m f =>
      if f.body.isSome && f.typeArgs.isEmpty then
        m.insert (Core.CoreIdent.toPretty f.name) f
      else m
  let (usedCtxs, defined, dropped) := collectHoistableFuncCtxs Env eligible ctx hoistRecursive
  for (n, e) in dropped do
    IO.eprintln s!"warning: top-level function {n} could not be translated to GOTO ({e}); its applications remain uninterpreted"
  let ctx := ctx.hoistFnApps defined procName
  let allFuncCtxs := usedCtxs.map fun (n, c) =>
    (n, c.hoistFnApps defined n)
  let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
  let mut symtabObj := match json.symtab with | .obj m => m | _ => .empty
  let mut gotoFns := match json.goto with
    | .obj m => match m.toList.find? (·.1 == "functions") with
      | some (_, .arr fns) => fns | _ => #[]
    | _ => #[]
  for (funcName, fctx) in allFuncCtxs do
    let fjson ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName fctx)
    match fjson.symtab with
    | .obj m => for (k, v) in m.toList do
        -- A defined function's key is written only by its own context: any other
        -- context's entry under that key is a nil-valued symbol synthesized for a
        -- hoisted call's callee reference (`Context.toJson`'s `extraSymbols`), and
        -- inserting it would clobber the real function symbol whenever the
        -- reference is processed after the definition. Definitions win,
        -- independent of emission order.
        if k == funcName || !defined.contains k then
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
    `<baseName>.symtab.json` and `<baseName>.goto.json`. Recursive top-level
    functions get GOTO bodies only with `hoistRecursive` (see `emitProc`). -/
public def coreToGotoFiles (tcPgm : Core.Program) (Env : Core.Expression.TyEnv)
    (baseName : String)
    (sourceText : Option String := none)
    (entryPoints : List String := ["main", "__main__"])
    (hoistRecursive : Bool := false)
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
  | .ok ctx =>
    let extraSyms ← match collectExtraSymbols tcPgm with
      | .ok s => pure (Lean.toJson s)
      | .error e => throw s!"{e}"
    let topLevelFuncs := tcPgm.decls.flatMap fun d => match d with
      | .func f _ => [f]
      | .recFuncBlock fs _ => fs
      | _ => []
    let (symtab, goto) ←
      match ← emitProc procName ctx extraSyms (moduleName := baseName)
              (topLevelFuncs := topLevelFuncs) (Env := Env)
              (hoistRecursive := hoistRecursive) |>.toBaseIO with
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

/-- Build a `void main()` verification harness for a parameter-carrying entry
    procedure `entry`: havoc its parameters, `assume` its preconditions, then
    call it. The procedure inliner then inlines `entry` into this harness,
    yielding a parameterless `main` that `goto-cc`/CBMC/cprover accept, with the
    precondition assumed — matching Core's "preconditions are assumed for the
    body" semantics (otherwise the back-end's synthesized harness leaves inputs
    unconstrained and reports spurious failures). -/
private def mkVerificationHarness (entry : Core.Procedure) : Core.Procedure :=
  let md : Imperative.MetaData Core.Expression := #[]
  let inKeys := entry.header.inputs.keys
  let outKeys := entry.header.outputs.keys
  let inDecls : List Core.Statement := entry.header.inputs.toList.map (fun (id, ty) =>
    .cmd (.cmd (.init id (.forAll [] ty) .nondet md)))
  let outOnlyDecls : List Core.Statement :=
    (entry.header.outputs.toList.filter (fun (id, _) => id ∉ inKeys)).map (fun (id, ty) =>
      .cmd (.cmd (.init id (.forAll [] ty) .nondet md)))
  let assumes : List Core.Statement := entry.spec.preconditions.toList.mapIdx (fun i (_, chk) =>
    .cmd (.cmd (.assume s!"harness_pre_{i}" chk.expr md)))
  let inArgs : List (Imperative.CallArg Core.Expression) := entry.header.inputs.toList.map (fun (id, _) =>
    if id ∈ outKeys then .inoutArg id else .inArg (.fvar default id none))
  let outArgs : List (Imperative.CallArg Core.Expression) :=
    (entry.header.outputs.toList.filter (fun (id, _) => id ∉ inKeys)).map (fun (id, _) =>
      .outArg id)
  let callStmt : Core.Statement :=
    .call (Core.CoreIdent.toPretty entry.header.name) (inArgs ++ outArgs) md
  { header := { name := ⟨"main", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured (inDecls ++ outOnlyDecls ++ assumes ++ [callStmt]) }

/--
Inline procedures, type-check, and emit CProver GOTO JSON files.
-/
public def inlineCoreToGotoFiles (program : Core.Program)
    (baseName : String)
    (sourceText : Option String := none)
    (entryPoints : List String := ["main", "__main__"])
    (factory : @Lambda.Factory Core.CoreLParams := Core.Factory)
    (hoistRecursive : Bool := false)
    : EIO String Unit := do
  -- If the chosen entry carries parameters, wrap it in a parameterless `main`
  -- verification harness (havoc params + assume preconditions + call); the
  -- inliner then folds the entry in. Keeps existing void `main` entries as-is.
  let findEntry (name : String) := program.decls.find? fun d =>
    match d with | .proc p _ => Core.CoreIdent.toPretty p.header.name == name | _ => false
  let program := match entryPoints.findSome? findEntry with
    | some (.proc p _) =>
      if !p.header.inputs.isEmpty && Core.CoreIdent.toPretty p.header.name != "main" then
        { program with decls := program.decls ++ [.proc (mkVerificationHarness p) #[]] }
      else program
    | _ => program
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
    (hoistRecursive := hoistRecursive)

end -- public section

end Strata
