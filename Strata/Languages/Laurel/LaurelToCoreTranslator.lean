/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Options
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CorePrelude
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intDivTOp intModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighTypeMd) : LMonoTy :=
  match _h : ty.val with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TString => LMonoTy.string
  | .TVoid => LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => .tcons "Heap" []
  | .TTypedField _ => .tcons "Field" []
  | .TSet elementType => Core.mapTy (translateType elementType) LMonoTy.bool
  | .UserDefined _ => .tcons "Composite" []
  | .TCore s => .tcons s []
  | _ => panic s!"unsupported type {ToFormat.format ty}"
termination_by ty.val
decreasing_by cases elementType; term_by_mem

def lookupType (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateType ty
  | none => panic s!"could not find variable {name} in environment"

def isConstant (constants : List Constant) (name : Identifier) : Bool :=
  constants.any (fun c => c.name == name)

/-- Set of names that are translated to Core functions (not procedures) -/
abbrev FunctionNames := List Identifier

def isCoreFunction (funcNames : FunctionNames) (name : Identifier) : Bool :=
  -- readField, updateField, and Box constructors/destructors are always functions
  name == "readField" || name == "updateField" || name == "increment" ||
  name == "MkHeap" || name == "Heap..data" || name == "Heap..nextReference" ||
  name == "BoxInt" || name == "BoxBool" || name == "BoxFloat64" || name == "BoxComposite" ||
  name == "Box..intVal" || name == "Box..boolVal" || name == "Box..float64Val" || name == "Box..compositeVal" ||
  funcNames.contains name

/--
Translate Laurel StmtExpr to Core Expression, also returning any diagnostics for disallowed
constructs (assignments, loops, procedure calls) that are not valid in expression position.

`isPureContext` should be `true` when translating function bodies or contract expressions.
In that case, disallowed constructs emit `DiagnosticModel`
errors. When `false` (inside a procedure body statement), disallowed constructs `panic!`
because `liftImperativeExpressions` should have already removed them.

`boundVars` tracks names bound by enclosing Forall/Exists quantifiers (innermost first).
When an Identifier matches a bound name at index `i`, it becomes `bvar i` (de Bruijn index)
instead of `fvar`.
-/
def translateExpr (constants : List Constant) (funcNames : FunctionNames) (env : TypeEnv) (expr : StmtExprMd)
    (boundVars : List Identifier := []) (isPureContext : Bool := false)
    : Core.Expression.Expr × List DiagnosticModel :=
  -- Dummy expression used as placeholder when an error is emitted in pure context
  let dummy := .fvar () (Core.CoreIdent.locl s!"DUMMY_VAR_{env.length}") none
  -- Emit an error in pure context; panic in impure context (lifting invariant violated)
  let disallowed (e : StmtExprMd) (msg : String) : Core.Expression.Expr × List DiagnosticModel :=
    if isPureContext then
      (dummy, [e.md.toDiagnostic msg])
    else
      panic! s!"translateExpr: {msg} (should have been lifted): {Std.Format.pretty (Std.ToFormat.format e)}"
  -- Helper: combine diagnostics from two translated sub-expressions
  let combine2 (r1 r2 : Core.Expression.Expr × List DiagnosticModel)
      (f : Core.Expression.Expr → Core.Expression.Expr → Core.Expression.Expr)
      : Core.Expression.Expr × List DiagnosticModel :=
    (f r1.1 r2.1, r1.2 ++ r2.2)
  match h: expr.val with
  | .LiteralBool b => (.const () (.boolConst b), [])
  | .LiteralInt i => (.const () (.intConst i), [])
  | .LiteralString s => (.const () (.strConst s), [])
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          (.bvar () idx, [])
      | none =>
          -- Check if this is a constant (field constant) or local variable
          if isConstant constants name then
            let ident := Core.CoreIdent.unres name
            (.op () ident none, [])
          else
            let ident := Core.CoreIdent.locl name
            (.fvar () ident (some (lookupType env name)), [])
  | .PrimitiveOp op [e] =>
    match op with
    | .Not =>
      let (re, ds) := translateExpr constants funcNames env e boundVars isPureContext
      (.app () boolNotOp re, ds)
    | .Neg =>
      let (re, ds) := translateExpr constants funcNames env e boundVars isPureContext
      (.app () intNegOp re, ds)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let (re1, ds1) := translateExpr constants funcNames env e1 boundVars isPureContext
    let (re2, ds2) := translateExpr constants funcNames env e2 boundVars isPureContext
    let ds := ds1 ++ ds2
    let binOp (bop : Core.Expression.Expr) : Core.Expression.Expr × List DiagnosticModel :=
      (LExpr.mkApp () bop [re1, re2], ds)
    match op with
    | .Eq => (.eq () re1 re2, ds)
    | .Neq => (.app () boolNotOp (.eq () re1 re2), ds)
    | .And => binOp boolAndOp
    | .Or => binOp boolOrOp
    | .Implies => binOp boolImpliesOp
    | .Add => binOp intAddOp
    | .Sub => binOp intSubOp
    | .Mul => binOp intMulOp
    | .Div => binOp intDivOp
    | .Mod => binOp intModOp
    | .DivT => binOp intDivTOp
    | .ModT => binOp intModTOp
    | .Lt => binOp intLtOp
    | .Leq => binOp intLeOp
    | .Gt => binOp intGtOp
    | .Geq => binOp intGeOp
    | _ => panic! s!"translateExpr: Invalid binary op: {repr op}"
  | .PrimitiveOp op args =>
    panic! s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch =>
      let (bcond, ds0) := translateExpr constants funcNames env cond boundVars isPureContext
      let (bthen, ds1) := translateExpr constants funcNames env thenBranch boundVars isPureContext
      let (belse, ds2) : Core.Expression.Expr × List DiagnosticModel :=
        match elseBranch with
        | none => panic "if-then without else expression not yet implemented"
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := WithMetadata.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr constants funcNames env e boundVars isPureContext
      (.ite () bcond bthen belse, ds0 ++ ds1 ++ ds2)
  | .StaticCall name args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !isCoreFunction funcNames name then
        disallowed expr "calls to procedures are not supported in functions or contracts"
      else
        let ident := Core.CoreIdent.unres name
        let fnOp := .op () ident none
        let (result, ds) := args.attach.foldl (fun (acc, accDs) ⟨arg, _⟩ =>
          let (re, ds) := translateExpr constants funcNames env arg boundVars isPureContext
          (.app () acc re, accDs ++ ds)) (fnOp, [])
        (result, ds)
  | .Block [single] _ => translateExpr constants funcNames env single boundVars isPureContext
  | .Block _ _ => panic "block expression not yet implemented"
  | .LocalVariable _ _ _ => panic "local variable expression not yet implemented"
  | .Return _ => disallowed expr "return expression not yet implemented"

  | .Forall name ty body =>
      let coreTy := translateType ty
      let (coreBody, ds) := translateExpr constants funcNames env body (name :: boundVars) isPureContext
      (LExpr.all () (some coreTy) coreBody, ds)
  | .Exists name ty body =>
      let coreTy := translateType ty
      let (coreBody, ds) := translateExpr constants funcNames env body (name :: boundVars) isPureContext
      (LExpr.exist () (some coreTy) coreBody, ds)
  | .Hole => (dummy, [])
  | .ReferenceEquals e1 e2 =>
      combine2 (translateExpr constants funcNames env e1 boundVars isPureContext)
               (translateExpr constants funcNames env e2 boundVars isPureContext)
               (fun l r => .eq () l r)
  | .Assign _ _ =>
      disallowed expr "destructive assignments are not supported in functions or contracts"
  | .While _ _ _ _ =>
      disallowed expr "loops are not supported in functions or contracts"
  | .Exit _ => disallowed expr "exit is not supported in expression position"

  | .IsType _ _ => panic "IsType should have been lowered"
  | .FieldSelect target fieldName =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      panic! s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldName}"

  | .AsType target _ => panic "AsType expression not implemented"
  | .Assigned _ => panic "assigned expression not implemented"
  | .Old value => panic "old expression not implemented"
  | .Fresh _ => panic "fresh expression not implemented"
  | .Assert _ => panic "assert expression not implemented"
  | .Assume _ => panic "assume expression not implemented"
  | .ProveBy value _ => panic "proveBy expression not implemented"
  | .ContractOf _ _ => panic "contractOf expression not implemented"
  | .Abstract => panic "abstract expression not implemented"
  | .All => panic "all expression not implemented"
  | .InstanceCall _ _ _ => panic "InstanceCall not implemented"
  | .PureFieldUpdate _ _ _ => panic "This expression not implemented"
  | .New _ => panic "New expression not implemented"
  | .This => panic "This expression not implemented"
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (panic "getNameFromMd bug")
  s!"({fileRange.range.start})"

def defaultExprForType (ty : HighTypeMd) : Core.Expression.Expr :=
  match ty.val with
  | .TInt => .const () (.intConst 0)
  | .TBool => .const () (.boolConst false)
  | .TString => .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy := translateType ty
    .fvar () (Core.CoreIdent.locl "$default") (some coreTy)

/--
Translate Laurel StmtExpr to Core Statements
Takes the constants list, type environment, output parameter names, and set of function names
-/
def translateStmt (constants : List Constant) (functionNames : FunctionNames) (env : TypeEnv)
  (outputParams : List Parameter) (stmt : StmtExprMd) : TypeEnv × List Core.Statement :=
  let md := stmt.md
  match h : stmt.val with
  | @StmtExpr.Assert cond =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let (coreExpr, _) := translateExpr constants functionNames env cond [] (isPureContext := true)
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md])
  | @StmtExpr.Assume cond =>
      let (coreExpr, _) := translateExpr constants functionNames env cond [] (isPureContext := true)
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.attach.foldl (fun (e, acc) ⟨s, _hs⟩ =>
        let (e', ss) := translateStmt constants functionNames e outputParams s
        (e', acc ++ ss)) (env, [])
      (env', stmtsList)
  | .LocalVariable name ty initializer =>
      let env' := (name, ty) :: env
      let boogieMonoType := translateType ty
      let boogieType := LTy.forAll [] boogieMonoType
      let ident := Core.CoreIdent.locl name
      match initializer with
      | some (⟨ .StaticCall callee args, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if isCoreFunction functionNames callee then
            -- Translate as expression (function application)
            let (boogieExpr, _) := translateExpr constants functionNames env (⟨ .StaticCall callee args, callMd ⟩)
            (env', [Core.Statement.init ident boogieType (some boogieExpr) md])
          else
            -- Translate as: var name; call name := callee(args)
            let coreArgs := args.map (fun a => (translateExpr constants functionNames env a).1)
            let defaultExpr := defaultExprForType ty
            let initStmt := Core.Statement.init ident boogieType (some defaultExpr)
            let callStmt := Core.Statement.call [ident] callee coreArgs
            (env', [initStmt, callStmt])
      | some initExpr =>
          let (coreExpr, _) := translateExpr constants functionNames env initExpr
          (env', [Core.Statement.init ident boogieType (some coreExpr)])
      | none =>
          let defaultExpr := defaultExprForType ty
          (env', [Core.Statement.init ident boogieType (some defaultExpr)])
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier name, _ ⟩] =>
          let ident := Core.CoreIdent.locl name
          -- Check if RHS is a procedure call (not a function)
          match value.val with
          | .StaticCall callee args =>
              if isCoreFunction functionNames callee then
                -- Functions are translated as expressions
                let (boogieExpr, _) := translateExpr constants functionNames env value
                (env, [Core.Statement.set ident boogieExpr])
              else
                -- Procedure calls need to be translated as call statements
                let coreArgs := args.map (fun a => (translateExpr constants functionNames env a).1)
                (env, [Core.Statement.call [ident] callee coreArgs])
          | _ =>
              let (boogieExpr, _) := translateExpr constants functionNames env value
              (env, [Core.Statement.set ident boogieExpr])
      | _ =>
          -- Parallel assignment: (var1, var2, ...) := expr
          -- Example use is heap-modifying procedure calls: (result, heap) := f(heap, args)
          match value.val with
          | .StaticCall callee args =>
              let coreArgs := args.map (fun a => (translateExpr constants functionNames env a).1)
              let lhsIdents := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (Core.CoreIdent.locl name)
                | _ => none
              (env, [Core.Statement.call lhsIdents callee coreArgs value.md])
          | _ =>
              panic "Assignments with multiple target but without a RHS call should not be constructed"
  | .IfThenElse cond thenBranch elseBranch =>
      let (bcond, _) := translateExpr constants functionNames env cond
      let (_, bthen) := translateStmt constants functionNames env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt constants functionNames env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .StaticCall name args =>
      -- Check if this is a function or procedure
      if isCoreFunction functionNames name then
        -- Functions as statements have no effect (shouldn't happen in well-formed programs)
        (env, [])
      else
        let boogieArgs := args.map (fun a => (translateExpr constants functionNames env a).1)
        (env, [Core.Statement.call [] name boogieArgs])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Core.CoreIdent.locl outParam.name
          let (coreExpr, _) := translateExpr constants functionNames env value
          let assignStmt := Core.Statement.set ident coreExpr
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [assignStmt, noFallThrough])
      | none, _ =>
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [noFallThrough])
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | .While cond invariants decreasesExpr body =>
      let (condExpr, _) := translateExpr constants functionNames env cond
      -- Combine multiple invariants with && for Core (which expects single invariant)
      let translatedInvariants := invariants.map (fun inv => (translateExpr constants functionNames env inv).1)
      let invExpr := match translatedInvariants with
        | [] => none
        | [single] => some single
        | first :: rest => some (rest.foldl (fun acc inv => LExpr.mkApp () boolAndOp [acc, inv]) first)
      let decreasingExprCore := decreasesExpr.map (fun d => (translateExpr constants functionNames env d).1)
      let (_, bodyStmts) := translateStmt constants functionNames env outputParams body
      (env, [Imperative.Stmt.loop condExpr decreasingExprCore invExpr bodyStmts md])
  | _ => (env, [])
  termination_by sizeOf stmt
  decreasing_by
    all_goals
      have hlt := WithMetadata.sizeOf_val_lt stmt
      cases stmt; term_by_mem

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := Core.CoreIdent.locl param.name
  let ty := translateType param.type
  (ident, ty)

/--
Translate Laurel Procedure to Core Procedure, also returning any diagnostics from
disallowed constructs in preconditions or postconditions.
-/
def translateProcedure (constants : List Constant) (funcNames : FunctionNames) (proc : Procedure)
    : Core.Procedure × List DiagnosticModel :=
  let inputPairs := proc.inputs.map translateParameterToCore
  let inputs := inputPairs

  let outputs := proc.outputs.map translateParameterToCore

  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           constants.map (fun c => (c.name, c.type))
  -- Translate precondition if it's not just LiteralBool true
  let (preconditions, precondDiags) : ListMap Core.CoreLabel Core.Procedure.Check × List DiagnosticModel :=
    match proc.precondition with
    | ⟨ .LiteralBool true, _ ⟩ => ([], [])
    | precond =>
        let (e, ds) := translateExpr constants funcNames initEnv precond [] (isPureContext := true)
        let check : Core.Procedure.Check := { expr := e, md := precond.md }
        ([("requires", check)], ds)
  -- Translate postconditions for Opaque bodies
  let (postconditions, postcondDiags) : ListMap Core.CoreLabel Core.Procedure.Check × List DiagnosticModel :=
    match proc.body with
    | .Opaque postconds _ _ =>
        let (_, result, diags) := postconds.foldl (fun (i, acc, accDs) postcond =>
          let label := if postconds.length == 1 then "postcondition" else s!"postcondition_{i}"
          let (e, ds) := translateExpr constants funcNames initEnv postcond [] (isPureContext := true)
          let check : Core.Procedure.Check := { expr := e, md := postcond.md }
          (i + 1, acc ++ [(label, check)], accDs ++ ds)) (0, [], [])
        (result, diags)
    | _ => ([], [])
  let modifies : List Core.Expression.Ident := []
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => (translateStmt constants funcNames initEnv proc.outputs bodyExpr).2
    | .Opaque _postconds (some impl) _ => (translateStmt constants funcNames initEnv proc.outputs impl).2
    | _ => [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
  let spec : Core.Procedure.Spec := {
    modifies,
    preconditions,
    postconditions,
  }
  ({
    header := header
    spec := spec
    body := body
  }, precondDiags ++ postcondDiags)

def translateConstant (c : Constant) : Core.Decl :=
  match c.type.val with
  | .TTypedField _ =>
      .func {
        name := Core.CoreIdent.unres c.name
        typeArgs := []
        inputs := []
        output := .tcons "Field" []
        body := none
      }
  | _ =>
      let ty := translateType c.type
      .func {
        name := Core.CoreIdent.unres c.name
        typeArgs := []
        inputs := []
        output := ty
        body := none
      }

/--
Check if a StmtExpr is a pure expression (can be used as a Core function body).
Pure expressions don't contain statements like assignments, loops, or local variables.
A Block with a single pure expression is also considered pure.
-/
private def isPureExpr(expr: StmtExprMd): Bool :=
  match _h : expr.val with
  | .LiteralBool _ => true
  | .LiteralInt _ => true
  | .LiteralString _ => true
  | .Identifier _ => true
  | .PrimitiveOp _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .IfThenElse c t none => isPureExpr c && isPureExpr t
  | .IfThenElse c t (some e) => isPureExpr c && isPureExpr t && isPureExpr e
  | .StaticCall _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .New _ => false
  | .ReferenceEquals e1 e2 => isPureExpr e1 && isPureExpr e2
  | .Block [single] _ => isPureExpr single
  | _ => false
  termination_by sizeOf expr
  decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

/-- Check if a pure-marked procedure can actually be represented as a Core function:
    transparent body that is a pure expression and has exactly one output. -/
private def canBeCoreFunctionBody (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent bodyExpr =>
    isPureExpr bodyExpr &&
    proc.outputs.length == 1
  | .Opaque _ bodyExprOption _ =>
    (bodyExprOption.map isPureExpr).getD true &&
    proc.outputs.length == 1
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable), also returning any
diagnostics emitted for disallowed constructs in the function body.
-/
def translateProcedureToFunction (constants : List Constant) (funcNames : FunctionNames) (proc : Procedure)
    : Core.Decl × List DiagnosticModel :=
  let inputs := proc.inputs.map translateParameterToCore
  let outputTy := match proc.outputs.head? with
    | some p => translateType p.type
    | none => LMonoTy.int
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type))
  let (body, bodyDiags) := match proc.body with
    | .Transparent bodyExpr =>
      let (e, ds) := translateExpr constants funcNames initEnv bodyExpr [] (isPureContext := true)
      (some e, ds)
    | _ => (none, [])
  (.func {
    name := Core.CoreIdent.unres proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  }, bodyDiags)

/--
Try to translate a Laurel Procedure marked `isFunctional` to a Core Function.
Returns `.error` with diagnostics if the procedure body contains disallowed constructs
(destructive assignments, loops, or procedure calls).
-/
def tryTranslatePureToFunction (constants : List Constant) (funcNames : FunctionNames) (proc : Procedure)
    : Except (Array DiagnosticModel) Core.Decl :=
  let (decl, diags) := translateProcedureToFunction constants funcNames proc
  if diags.isEmpty then
    .ok decl
  else
    .error diags.toArray

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) (Core.Program × Array DiagnosticModel) := do
  let program := heapParameterization program
  let (program, modifiesDiags) := modifiesClausesTransform program
  dbg_trace "===  Program after heapParameterization + modifiesClausesTransform ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  dbg_trace "================================="
  let program := liftImperativeExpressions program
  -- Procedures marked isFunctional are translated to Core functions; all others become Core procedures.
  let (markedPure, procProcs) := program.staticProcedures.partition (·.isFunctional)
  -- Try to translate each isFunctional procedure to a Core function, collecting errors for failures
  let funcNames : FunctionNames := markedPure.map (·.name)
  let (pureErrors, pureFuncDecls) := markedPure.foldl (fun (errs, decls) p =>
    match tryTranslatePureToFunction program.constants funcNames p with
    | .error es => (errs ++ es.toList, decls)
    | .ok d     => (errs, decls.push d)) ([], #[])
  -- Translate procedures, collecting any diagnostics from preconditions/postconditions
  let (procedures, procDiags) := procProcs.foldl (fun (procs, diags) p =>
    let (proc, ds) := translateProcedure program.constants funcNames p
    (procs ++ [proc], diags ++ ds)) ([], [])
  -- Collect ALL errors from both functions and procedures before deciding whether to fail
  let allErrors := pureErrors ++ procDiags
  if !allErrors.isEmpty then
    .error allErrors.toArray
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let constDecls := program.constants.map translateConstant
  let preludeDecls := corePrelude.decls
  pure ({ decls := preludeDecls ++ constDecls ++ pureFuncDecls.toList ++ procDecls }, modifiesDiags)

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (program : Program)
    (options : Options := Options.default)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let (strataCoreProgram, translateDiags) ← match translate program with
    | .error translateErrorDiags => return .error translateErrorDiags
    | .ok result => pure result

  -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Strata Core program
  dbg_trace "=== Generated Strata Core Program ==="
  dbg_trace (toString (Std.Format.pretty (Strata.Core.formatProgram strataCoreProgram) 100))
  dbg_trace "================================="
  let runner tempDir :=
    EIO.toIO (fun f => IO.Error.userError (toString f))
        (Core.verify strataCoreProgram tempDir .none options)
  let ioResult ← match options.vcDirectory with
    | .none => IO.FS.withTempDir runner
    | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩
  if translateDiags.isEmpty then
    return .ok ioResult
  else
    return .error (translateDiags ++ ioResult.filterMap toDiagnosticModel)


def verifyToDiagnostics (files: Map Strata.Uri Lean.FileMap) (program : Program)
    (options : Options := Options.default): IO (Array Diagnostic) := do
  let results <- verifyToVcResults program options
  match results with
  | .error errors => return errors.map (fun dm => dm.toDiagnostic files)
  | .ok results => return results.filterMap (fun dm => dm.toDiagnostic files)


def verifyToDiagnosticModels (program : Program) (options : Options := Options.default) : IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults program options
  match results with
  | .error errors => return errors
  | .ok results => return results.filterMap toDiagnosticModel

end Laurel
