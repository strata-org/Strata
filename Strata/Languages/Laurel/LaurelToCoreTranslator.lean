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
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.TypeHierarchy
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CorePrelude
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intDivTOp intModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)

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
  | .TMap keyType valueType => Core.mapTy (translateType keyType) (translateType valueType)
  | .UserDefined _ => .tcons "Composite" []
  | .TCore s => .tcons s []
  | _ => panic s!"unsupported type {ToFormat.format ty}"
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateType ty
  | none => panic s!"could not find variable {name} in environment '{Std.format env}'"

def isFieldName (fieldNames : List Identifier) (name : Identifier) : Bool :=
  fieldNames.contains name

/-- Set of names that are translated to Core functions (not procedures) -/
abbrev FunctionNames := List Identifier

def isCoreFunction (funcNames : FunctionNames) (name : Identifier) : Bool :=
  -- readField, updateField, and Box constructors/destructors are always functions
  name == "readField" || name == "updateField" || name == "increment" ||
  name == "MkHeap" || name == "Heap..data" || name == "Heap..nextReference" ||
  name == "MkComposite" || name == "Composite..ref" || name == "Composite..typeTag" ||
  name == "BoxInt" || name == "BoxBool" || name == "BoxFloat64" || name == "BoxComposite" ||
  name == "Box..intVal" || name == "Box..boolVal" || name == "Box..float64Val" || name == "Box..compositeVal" ||
  funcNames.contains name

/--
Translate Laurel StmtExpr to Core Expression.

`boundVars` tracks names bound by enclosing Forall/Exists quantifiers (innermost first).
When an Identifier matches a bound name at index `i`, it becomes `bvar i` (de Bruijn index)
instead of `fvar`.
-/
def translateExpr (fieldNames : List Identifier) (env : TypeEnv) (expr : StmtExprMd)
    (boundVars : List Identifier := []) : Core.Expression.Expr :=
  match h: expr.val with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .LiteralString s => .const () (.strConst s)
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          .bvar () idx
      | none =>
          -- Check if this is a field name (datatype constructor) or local variable
          if isFieldName fieldNames name then
            let ident := Core.CoreIdent.unres name
            .op () ident none
          else
            let ident := Core.CoreIdent.locl name
            .fvar () ident (some (lookupType env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr fieldNames env e boundVars)
    | .Neg => .app () intNegOp (translateExpr fieldNames env e boundVars)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr fieldNames env e1 boundVars, translateExpr fieldNames env e2 boundVars]
    match op with
    | .Eq => .eq () (translateExpr fieldNames env e1 boundVars) (translateExpr fieldNames env e2 boundVars)
    | .Neq => .app () boolNotOp (.eq () (translateExpr fieldNames env e1 boundVars) (translateExpr fieldNames env e2 boundVars))
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
    | .StrConcat => binOp strConcatOp
    | _ => panic! s!"translateExpr: Invalid binary op: {repr op}"
  | .PrimitiveOp op args =>
    panic! s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr fieldNames env cond boundVars
      let bthen := translateExpr fieldNames env thenBranch boundVars
      let belse := match elseBranch with
                  | some e => translateExpr fieldNames env e boundVars
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value => translateExpr fieldNames env value boundVars
  | .StaticCall name args =>
      let ident := Core.CoreIdent.unres name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr fieldNames env arg boundVars)) fnOp
  | .Block [single] _ => translateExpr fieldNames env single boundVars
  | .Forall name ty body =>
      let coreTy := translateType ty
      let coreBody := translateExpr fieldNames env body (name :: boundVars)
      LExpr.all () (some coreTy) coreBody
  | .Exists name ty body =>
      let coreTy := translateType ty
      let coreBody := translateExpr fieldNames env body (name :: boundVars)
      LExpr.exist () (some coreTy) coreBody
  | .FieldSelect target fieldName =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      panic! s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldName}"
  | .IsType _ _ =>
      panic! s!"IsType should have been eliminated by typeHierarchyTransform"
  | .New _ =>
      panic! s!"New should have been eliminated by typeHierarchyTransform"
  | .Hole => .fvar () (Core.CoreIdent.locl s!"DUMMY_VAR_{env.length}") none
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
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
def translateStmt (fieldNames : List Identifier) (funcNames : FunctionNames) (env : TypeEnv)
  (outputParams : List Parameter) (stmt : StmtExprMd) : TypeEnv × List Core.Statement :=
  let md := stmt.md
  match h : stmt.val with
  | @StmtExpr.Assert cond =>
      let boogieExpr := translateExpr fieldNames env cond
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md])
  | @StmtExpr.Assume cond =>
      let boogieExpr := translateExpr fieldNames env cond
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.attach.foldl (fun (e, acc) ⟨s, _hs⟩ =>
        let (e', ss) := translateStmt fieldNames funcNames e outputParams s
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
          if isCoreFunction funcNames callee then
            -- Translate as expression (function application)
            let boogieExpr := translateExpr fieldNames env (⟨ .StaticCall callee args, callMd ⟩)
            (env', [Core.Statement.init ident boogieType (some boogieExpr) md])
          else
            -- Translate as: var name; call name := callee(args)
            let boogieArgs := args.map (translateExpr fieldNames env)
            let defaultExpr := defaultExprForType ty
            let initStmt := Core.Statement.init ident boogieType (some defaultExpr) md
            let callStmt := Core.Statement.call [ident] callee boogieArgs md
            (env', [initStmt, callStmt])
      | some initExpr =>
          let boogieExpr := translateExpr fieldNames env initExpr
          (env', [Core.Statement.init ident boogieType (some boogieExpr) md])
      | none =>
          let defaultExpr := defaultExprForType ty
          (env', [Core.Statement.init ident boogieType (some defaultExpr) md])
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier name, _ ⟩] =>
          let ident := Core.CoreIdent.locl name
          -- Check if RHS is a procedure call (not a function)
          match value.val with
          | .StaticCall callee args =>
              if isCoreFunction funcNames callee then
                -- Functions are translated as expressions
                let boogieExpr := translateExpr fieldNames env value
                (env, [Core.Statement.set ident boogieExpr md])
              else
                -- Procedure calls need to be translated as call statements
                let boogieArgs := args.map (translateExpr fieldNames env)
                (env, [Core.Statement.call [ident] callee boogieArgs md])
          | _ =>
              let boogieExpr := translateExpr fieldNames env value
              (env, [Core.Statement.set ident boogieExpr md])
      | _ =>
          -- Parallel assignment: (var1, var2, ...) := expr
          -- Example use is heap-modifying procedure calls: (result, heap) := f(heap, args)
          match value.val with
          | .StaticCall callee args =>
              let boogieArgs := args.map (translateExpr fieldNames env)
              let lhsIdents := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (Core.CoreIdent.locl name)
                | _ => none
              (env, [Core.Statement.call lhsIdents callee boogieArgs value.md])
          | _ =>
              panic "Assignments with multiple target but without a RHS call should not be constructed"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr fieldNames env cond
      let (_, bthen) := translateStmt fieldNames funcNames env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt fieldNames funcNames env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .StaticCall name args =>
      -- Check if this is a function or procedure
      if isCoreFunction funcNames name then
        -- Functions as statements have no effect (shouldn't happen in well-formed programs)
        (env, [])
      else
        let boogieArgs := args.map (translateExpr fieldNames env)
        (env, [Core.Statement.call [] name boogieArgs md])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Core.CoreIdent.locl outParam.name
          let boogieExpr := translateExpr fieldNames env value
          let assignStmt := Core.Statement.set ident boogieExpr md
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [assignStmt, noFallThrough])
      | none, _ =>
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [noFallThrough])
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | .While cond invariants decreasesExpr body =>
      let condExpr := translateExpr fieldNames env cond
      let invExprs := invariants.map (translateExpr fieldNames env)
      let decreasingExprCore := decreasesExpr.map (translateExpr fieldNames env)
      let (_, bodyStmts) := translateStmt fieldNames funcNames env outputParams body
      (env, [Imperative.Stmt.loop condExpr decreasingExprCore invExprs bodyStmts md])
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
Translate Laurel Procedure to Core Procedure
-/
def translateProcedure (fieldNames : List Identifier) (funcNames : FunctionNames) (proc : Procedure) : Core.Procedure :=
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
                           proc.outputs.map (fun p => (p.name, p.type))
  -- Translate preconditions
  let preconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    let (_, result) := proc.preconditions.foldl (fun (i, acc) precond =>
        let label := if proc.preconditions.length == 1 then "requires" else s!"requires_{i}"
        let check : Core.Procedure.Check := { expr := translateExpr fieldNames initEnv precond, md := precond.md }
        (i + 1, acc ++ [(label, check)])) (0, [])
    result
  -- Translate postconditions for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.body with
    | .Opaque postconds _ _ =>
        let (_, result) := postconds.foldl (fun (i, acc) postcond =>
          let label := if postconds.length == 1 then "postcondition" else s!"postcondition_{i}"
          let check : Core.Procedure.Check := { expr := translateExpr fieldNames initEnv postcond, md := postcond.md }
          (i + 1, acc ++ [(label, check)])) (0, [])
        result
    | _ => []
  let modifies : List Core.Expression.Ident := []
  -- For bodyless opaque procedures (no implementation), we use `assume false`
  -- so postcondition asserts are vacuously true. The postconditions are kept in
  -- the spec so they are assumed at call sites via call elimination.
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => (translateStmt fieldNames funcNames initEnv proc.outputs bodyExpr).2
    | .Opaque _postconds (some impl) _ => (translateStmt fieldNames funcNames initEnv proc.outputs impl).2
    -- because Core does not support procedures without a body, we add an assume false
    | _ => [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
  let spec : Core.Procedure.Spec := {
    modifies,
    preconditions,
    postconditions,
  }
  {
    header := header
    spec := spec
    body := body
  }

def translateProcedureToFunction (fieldNames : List Identifier) (proc : Procedure) : Core.Decl :=
  let inputs := proc.inputs.map translateParameterToCore
  let outputTy := match proc.outputs.head? with
    | some p => translateType p.type
    | none => LMonoTy.int
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type))
  let body := match proc.body with
    | .Transparent bodyExpr => some (translateExpr fieldNames initEnv bodyExpr)
    | _ => none
  .func {
    name := Core.CoreIdent.unres proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  }
/--
Check if a Laurel expression is pure (contains no side effects).
Used to determine if a procedure can be translated as a Core function.
-/
def isPureExpr(expr: StmtExprMd): Bool :=
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
  | .Block _ _ => false
  -- Statement-like
  | .LocalVariable .. => true
  | .While .. => false
  | .Exit .. => false
  | .Return .. => false
  -- Expression-like
  | .Assign .. => false
  | .FieldSelect .. => true
  | .PureFieldUpdate .. => true
  -- Instance related
  | .This => panic s!"isPureExpr not implemented for This"
  | .AsType .. => panic s!"isPureExpr not supported for AsType"
  | .IsType .. => panic s!"isPureExpr not supported for IsType"
  | .InstanceCall .. => panic s!"isPureExpr not implemented for InstanceCall"
  -- Verification specific
  | .Forall .. => panic s!"isPureExpr not implemented for Forall"
  | .Exists .. => panic s!"isPureExpr not implemented for Exists"
  | .Assigned .. => panic s!"isPureExpr not supported for AsType"
  | .Old .. => panic s!"isPureExpr not supported for AsType"
  | .Fresh .. => panic s!"isPureExpr not supported for AsType"
  | .Assert .. => panic s!"isPureExpr not implemented for Assert"
  | .Assume .. => panic s!"isPureExpr not implemented for Assume"
  | .ProveBy .. => panic s!"isPureExpr not implemented for ProveBy"
  | .ContractOf .. => panic s!"isPureExpr not implemented for ContractOf"
  | .Abstract => panic s!"isPureExpr not implemented for Abstract"
  | .All => panic s!"isPureExpr not implemented for All"
  -- Dynamic / closures
  | .Hole => true
  termination_by sizeOf expr
  decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)


/--
Check if a procedure can be translated as a Core function.
A procedure can be a function if:
- It has a transparent body that is a pure expression
- It has no precondition (or just `true`)
- It has exactly one output parameter (the return type)
-/
def canBeBoogieFunction (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent bodyExpr =>
    isPureExpr bodyExpr &&
    proc.preconditions.isEmpty &&
    proc.outputs.length == 1
  | _ => false

/--
Translate a Laurel DatatypeDefinition to a Core type declaration.
Zero constructors produces an opaque (abstract) type; otherwise a Core datatype.
-/
def translateDatatypeDefinition (dt : DatatypeDefinition) : Core.Decl :=
  match h : dt.constructors with
  | [] =>
    -- Zero constructors: opaque type
    Core.Decl.type (.con { name := dt.name, numargs := dt.typeArgs.length })
  | first :: rest =>
    let constrs : List (Lambda.LConstr Core.Visibility) := (first :: rest).map fun c =>
      { name := Core.CoreIdent.unres c.name
        args := c.args.map fun (n, ty) => (Core.CoreIdent.unres n, translateType ty) }
    let ldt : Lambda.LDatatype Core.Visibility := {
      name := dt.name
      typeArgs := dt.typeArgs
      constrs := constrs
      constrs_ne := by simp [constrs]
    }
    Core.Decl.type (.data [ldt])

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) (Core.Program × Array DiagnosticModel) := do
  let program := heapParameterization program
  let program := typeHierarchyTransform program
  let (program, modifiesDiags) := modifiesClausesTransform program
  dbg_trace "===  Program after heapParameterization + modifiesClausesTransform ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  dbg_trace "================================="
  let program := liftExpressionAssignments program
  -- Collect field names from the Field datatype (generated by heapParameterization)
  let fieldNames : List Identifier := program.types.foldl (fun acc td =>
    match td with
    | .Datatype dt => if dt.name == "Field" then acc ++ dt.constructors.map (·.name) else acc
    | _ => acc) []
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := program.staticProcedures.partition canBeBoogieFunction
  -- Build the set of function names for use during translation
  let funcNames : FunctionNames := funcProcs.map (·.name)
  let procedures := procProcs.map (translateProcedure fieldNames funcNames)
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let laurelFuncDecls := funcProcs.map (translateProcedureToFunction fieldNames)
  -- Filter out the Field and TypeTag opaque types. These are only in the prelude to satisfy the DDM type checker.
  let preludeDecls := corePrelude.decls.filter fun d =>
    d.name.name != "Field" && d.name.name != "TypeTag"
  -- Translate Laurel constants to Core function declarations (0-ary functions)
  let constantDecls := program.constants.map fun c =>
    let coreTy := translateType c.type
    let body := c.initializer.map (translateExpr fieldNames [] ·)
    Core.Decl.func {
      name := Core.CoreIdent.unres c.name
      typeArgs := []
      inputs := []
      output := coreTy
      body := body
    }
  -- Translate Laurel datatype definitions to Core datatype declarations
  let laurelDatatypeDecls := program.types.filterMap fun td => match td with
    | .Datatype dt => some (translateDatatypeDefinition dt)
    | _ => none
  pure ({ decls := laurelDatatypeDecls ++ preludeDecls ++ constantDecls ++ laurelFuncDecls ++ procDecls }, modifiesDiags)

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
  -- Validate for diamond-inherited field accesses before translation
  let uri := files.keys.head!
  let diamondErrors := validateDiamondFieldAccesses uri program
  if !diamondErrors.isEmpty then
    return diamondErrors.map (fun dm => dm.toDiagnostic files)
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
