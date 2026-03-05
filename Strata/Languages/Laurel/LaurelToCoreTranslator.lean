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
import Strata.Languages.Laurel.TypeHierarchy
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

open Core (VCResult VCResults VerifyOptions)
open Core (intAddOp intSubOp intMulOp intSafeDivOp intSafeModOp intSafeDivTOp intSafeModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Core Type
-/
def translateType (model : SemanticModel) (ty : HighTypeMd) : LMonoTy :=
  match _h : ty.val with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TString => LMonoTy.string
  | .TVoid => LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => .tcons "Heap" []
  | .TTypedField _ => .tcons "Field" []
  | .TSet elementType => Core.mapTy (translateType model elementType) LMonoTy.bool
  | .TMap keyType valueType => Core.mapTy (translateType model keyType) (translateType model valueType)
  | .UserDefined name =>
    -- Composite types map to "Composite"; datatypes map to their own name
    match name.uniqueId.bind model.refToDef.get? with
    | some (.compositeType _) => .tcons "Composite" []
    | some (.datatypeDefinition dt) => .tcons dt.name.text []
    | _ => .tcons "Composite" [] -- fallback for unresolved refs
  | .TCore s => .tcons s []
  | .TFloat64 => LMonoTy.real -- Incorrect?
  | _ => panic s!"translateType: unsupported type {ToFormat.format ty}"
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (model : SemanticModel) (name : Identifier) : LMonoTy :=
  match (model.get name).getType with
  | .some ty => translateType model ty
  | none => panic s!"no type for {name}"

def isFieldName (fieldNames : List Identifier) (name : Identifier) : Bool :=
  fieldNames.contains name

/-- Set of names that are translated to Core functions (not procedures) -/
abbrev FunctionNames := List Identifier

/-- State threaded through expression and statement translation -/
structure TranslateState where
  /-- Diagnostics accumulated during translation -/
  diagnostics : List DiagnosticModel := []
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Constants known to the program (field constants, etc.) -/
  model : SemanticModel

/-- The translation monad: state over Id -/
abbrev TranslateM := StateT TranslateState Id

/-- Emit a diagnostic into the translation state -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Run a `TranslateM` action, returning the result and final state -/
def runTranslateM (s : TranslateState) (m : TranslateM α) : α × TranslateState :=
  m s

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/--
Translate Laurel StmtExpr to Core Expression using the `TranslateM` monad.
Diagnostics for disallowed constructs are emitted into the monad state.

`isPureContext` should be `true` when translating function bodies or contract expressions.
In that case, disallowed constructs emit `DiagnosticModel` errors into the state.
When `false` (inside a procedure body statement), disallowed constructs `panic!`
because `liftImperativeExpressions` should have already removed them.

`boundVars` tracks names bound by enclosing Forall/Exists quantifiers (innermost first).
When an Identifier matches a bound name at index `i`, it becomes `bvar i` (de Bruijn index)
instead of `fvar`.
-/
def translateExpr (expr : StmtExprMd)
    (boundVars : List Identifier := []) (isPureContext : Bool := false)
    : TranslateM Core.Expression.Expr := do
  let s ← get
  let model := s.model
  -- Dummy expression used as placeholder when an error is emitted in pure context
  let dummy := .fvar () (⟨s!"DUMMY_VAR_{← freshId}", ()⟩) none
  -- Emit an error in pure context; panic in impure context (lifting invariant violated)
  let disallowed (e : StmtExprMd) (msg : String) : TranslateM Core.Expression.Expr := do
    if isPureContext then
      emitDiagnostic (e.md.toDiagnostic msg)
      return dummy
    else
      panic! s!"translateExpr: {msg} (should have been lifted): {Std.Format.pretty (Std.ToFormat.format e)}"
  match h: expr.val with
  | .LiteralBool b => return .const () (.boolConst b)
  | .LiteralInt i => return .const () (.intConst i)
  | .LiteralString s => return .const () (.strConst s)
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          return .bvar () idx
      | none =>
        match model.get name with
        | .field _ f =>
            return .op () ⟨f.name.text, ()⟩ none
        | astNode =>
            return .fvar () ⟨name.text, ()⟩ (some (translateType model $ astNode.getType.getD (panic! "LaurelToCore.translateExpr")))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not =>
      let re ← translateExpr e boundVars isPureContext
      return .app () boolNotOp re
    | .Neg =>
      let re ← translateExpr e boundVars isPureContext
      return .app () intNegOp re
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let re1 ← translateExpr e1 boundVars isPureContext
    let re2 ← translateExpr e2 boundVars isPureContext
    let binOp (bop : Core.Expression.Expr) : Core.Expression.Expr :=
      LExpr.mkApp () bop [re1, re2]
    match op with
    | .Eq => return .eq () re1 re2
    | .Neq => return .app () boolNotOp (.eq () re1 re2)
    | .And => return binOp boolAndOp
    | .Or => return binOp boolOrOp
    | .Implies => return binOp boolImpliesOp
    | .Add => return binOp intAddOp
    | .Sub => return binOp intSubOp
    | .Mul => return binOp intMulOp
    | .Div => return binOp intSafeDivOp
    | .Mod => return binOp intSafeModOp
    | .DivT => return binOp intSafeDivTOp
    | .ModT => return binOp intSafeModTOp
    | .Lt => return binOp intLtOp
    | .Leq => return binOp intLeOp
    | .Gt => return binOp intGtOp
    | .Geq => return binOp intGeOp
    | .StrConcat => return binOp strConcatOp
    | _ => panic! s!"translateExpr: Invalid binary op: {repr op}"
  | .PrimitiveOp op args =>
    panic! s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond boundVars isPureContext
      let bthen ← translateExpr thenBranch boundVars isPureContext
      let belse ← match elseBranch with
        | none => panic "if-then without else expression not yet implemented"
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := WithMetadata.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite () bcond bthen belse
  | .StaticCall callee args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !model.isFunction callee then
        disallowed expr "calls to procedures are not supported in functions or contracts"
      else
        let fnOp : Core.Expression.Expr := .op () ⟨callee.text, ()⟩ none
        args.attach.foldlM (fun acc ⟨arg, _⟩ => do
          let re ← translateExpr arg boundVars isPureContext
          return .app () acc re) fnOp
  | .Block [single] _ => translateExpr single boundVars isPureContext
  | .Forall ⟨ name, ty ⟩ body =>
      let coreTy := translateType model ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      return LExpr.all () name.text (some coreTy) coreBody
  | .Exists ⟨ name, ty ⟩ body =>
      let coreTy := translateType model ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      return LExpr.exist () name.text (some coreTy) coreBody
  | .Hole => return dummy
  | .ReferenceEquals e1 e2 =>
      let re1 ← translateExpr e1 boundVars isPureContext
      let re2 ← translateExpr e2 boundVars isPureContext
      return .eq () re1 re2
  | .Assign _ _ =>
      disallowed expr "destructive assignments are not supported in functions or contracts"
  | .While _ _ _ _ =>
      disallowed expr "loops are not supported in functions or contracts"
  | .Exit _ => disallowed expr "exit is not supported in expression position"

  | .IsType _ _ => panic "IsType should have been lowered"
  | .New _ => panic! s!"New should have been eliminated by typeHierarchyTransform"
  | .FieldSelect target fieldId =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      panic! s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldId.text}"

  | .Block _ _ => panic "block expression not yet implemented (should be lowered in a separate pass)"
  | .LocalVariable _ _ _ => panic "local variable expression not yet implemented (should be lowered in a separate pass)"
  | .Return _ => disallowed expr "return expression not yet implemented (should be lowered in a separate pass)"

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
  | .This => panic "This expression not implemented"
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (panic "getNameFromMd bug")
  s!"({fileRange.range.start})"

def defaultExprForType (model : SemanticModel) (ty : HighTypeMd) : Core.Expression.Expr :=
  match ty.val with
  | .TInt => .const () (.intConst 0)
  | .TBool => .const () (.boolConst false)
  | .TString => .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy := translateType model ty
    .fvar () (⟨"$default", ()⟩) (some coreTy)

/--
Translate Laurel StmtExpr to Core Statements using the `TranslateM` monad.
Diagnostics are emitted into the monad state.
-/
def translateStmt (outputParams : List Parameter) (stmt : StmtExprMd)
    : TranslateM (List Core.Statement) := do
  let s ← get
  let model := s.model
  let md := stmt.md
  match _h : stmt.val with
  | @StmtExpr.Assert cond =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md]
  | @StmtExpr.Assume cond =>
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts _ => stmts.flatMapM (fun s => translateStmt outputParams s)
  | .LocalVariable id ty initializer =>
      let coreMonoType := translateType model ty
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨id.text, ()⟩
      match initializer with
      | some (⟨ .StaticCall callee args, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if model.isFunction callee then
            -- Translate as expression (function application)
            let coreExpr ← translateExpr (⟨ .StaticCall callee args, callMd ⟩)
            return [Core.Statement.init ident coreType (some coreExpr) md]
          else
            -- Translate as: var name; call name := callee(args)
            let coreArgs ← args.mapM (fun a => translateExpr a)
            let defaultExpr := defaultExprForType model ty
            let initStmt := Core.Statement.init ident coreType (some defaultExpr) md
            let callStmt := Core.Statement.call [ident] callee.text coreArgs md
            return [initStmt, callStmt]
      | some initExpr =>
          let coreExpr ← translateExpr initExpr
          return [Core.Statement.init ident coreType (some coreExpr) md]
      | none =>
          let defaultExpr := defaultExprForType model ty
          return [Core.Statement.init ident coreType (some defaultExpr) md]
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier targetId, _ ⟩] =>
          let ident := ⟨targetId.text, ()⟩
          -- Check if RHS is a procedure call (not a function)
          match value.val with
          | .StaticCall callee args =>
              if model.isFunction callee then
                -- Functions are translated as expressions
                let coreExpr ← translateExpr value
                return [Core.Statement.set ident coreExpr md]
              else
                -- Procedure calls need to be translated as call statements
                let coreArgs ← args.mapM (fun a => translateExpr a)
                return [Core.Statement.call [ident] callee.text coreArgs md]
          | _ =>
              let coreExpr ← translateExpr value
              return [Core.Statement.set ident coreExpr md]
      | _ =>
          -- Parallel assignment: (var1, var2, ...) := expr
          -- Example use is heap-modifying procedure calls: (result, heap) := f(heap, args)
          match value.val with
          | .StaticCall callee args =>
              let coreArgs ← args.mapM (fun a => translateExpr a)
              let lhsIdents := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (⟨name.text, ()⟩)
                | _ => none
              return [Core.Statement.call lhsIdents callee.text coreArgs value.md]
          | _ =>
              panic "Assignments with multiple target but without a RHS call should not be constructed"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond
      let bthen ← translateStmt outputParams thenBranch
      let belse ← match elseBranch with
                  | some e => translateStmt outputParams e
                  | none => pure []
      return [Imperative.Stmt.ite bcond bthen belse .empty]
  | .StaticCall callee args =>
      -- Check if this is a function or procedure
      if model.isFunction callee then
        -- Functions as statements have no effect (shouldn't happen in well-formed programs)
        return []
      else
        let coreArgs ← args.mapM (fun a => translateExpr a)
        return [Core.Statement.call [] callee.text coreArgs md]
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := ⟨outParam.name.text, ()⟩
          let coreExpr ← translateExpr value
          let assignStmt := Core.Statement.set ident coreExpr md
          return [assignStmt, .exit (some "$body") md]
      | none, _ =>
          return [.exit (some "$body") md]
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | .While cond invariants decreasesExpr body =>
      let condExpr ← translateExpr cond
      let invExprs ← invariants.mapM (translateExpr)
      let decreasingExprCore ← decreasesExpr.mapM (translateExpr)
      let bodyStmts ← translateStmt outputParams body
      return [Imperative.Stmt.loop condExpr decreasingExprCore invExprs bodyStmts md]
  | _ => return []
  termination_by sizeOf stmt
  decreasing_by
    all_goals
      have hlt := WithMetadata.sizeOf_val_lt stmt
      cases stmt; term_by_mem

/--
Translate a list of checks (preconditions or postconditions) to Core checks.
Each check gets a label like `"requires"` or `"requires_0"`, `"requires_1"`, etc.
-/
private def translateChecks (checks : List StmtExprMd) (labelBase : String)
    : TranslateM (ListMap Core.CoreLabel Core.Procedure.Check) :=
  checks.mapIdxM (fun i check => do
    let label := if checks.length == 1 then labelBase else s!"{labelBase}_{i}"
    let checkExpr ← translateExpr check [] (isPureContext := true)
    let c : Core.Procedure.Check := { expr := checkExpr, md := check.md }
    return (label, c))

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (model : SemanticModel) (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := ⟨param.name.text, ()⟩
  let ty := translateType model param.type
  (ident, ty)

/--
Translate Laurel Procedure to Core Procedure using `TranslateM`.
Diagnostics from disallowed constructs in preconditions, postconditions, and body
are emitted into the monad state.
-/
def translateProcedure (proc : Procedure) : TranslateM Core.Procedure := do
  let inputPairs := proc.inputs.map (translateParameterToCore (← get).model)
  let inputs := inputPairs
  let outputs := proc.outputs.map (translateParameterToCore (← get).model)
  let header : Core.Procedure.Header := {
    name := proc.name.text
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  -- Translate preconditions
  let preconditions ← translateChecks proc.preconditions "requires"

  -- Translate postconditions for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ =>
        translateChecks postconds "postcondition"
    | _ => pure []
  let modifies : List Core.Expression.Ident := []
  let bodyStmts : List Core.Statement ←
    match proc.body with
    | .Transparent bodyExpr => translateStmt proc.outputs bodyExpr
    | .Opaque _postconds (some impl) _ => translateStmt proc.outputs impl
    | _ => pure [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  let body : List Core.Statement := [.block "$body" bodyStmts .empty]
  let spec : Core.Procedure.Spec := { modifies, preconditions, postconditions }
  return { header, spec, body }

/--
Check if a Laurel expression is pure (contains no side effects).
Used to determine if a procedure can be translated as a Core function.
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
  | .External => false
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable) using `TranslateM`.
Diagnostics for disallowed constructs in the function body are emitted into the monad state.
-/
def translateProcedureToFunction (proc : Procedure) : TranslateM Core.Decl := do
  let model := (← get).model
  let inputs := proc.inputs.map (translateParameterToCore model)
  let outputTy := match proc.outputs.head? with
    | some p => translateType model p.type
    | none => LMonoTy.int
  -- Translate precondition to FuncPrecondition (skip trivial `true`)
  let preconditions ← proc.preconditions.mapM (fun precondition => do
    let checkExpr ← translateExpr precondition [] true
    return { expr := checkExpr, md := () })

  let body ← match proc.body with
    | .Transparent bodyExpr => some <$> translateExpr bodyExpr [] (isPureContext := true)
    | .Opaque _ (some bodyExpr) _ =>
      emitDiagnostic (proc.md.toDiagnostic "functions with postconditions are not yet supported")
      some <$> translateExpr bodyExpr [] (isPureContext := true)
    | _ => pure none
  return .func {
    name := ⟨proc.name.text, ()⟩
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
    preconditions := preconditions
  }

/--
Translate a Laurel DatatypeDefinition to a Core type declaration.
Zero constructors produces an opaque (abstract) type; otherwise a Core datatype.
-/
def translateDatatypeDefinition (model : SemanticModel) (dt : DatatypeDefinition) : Core.Decl :=
  match h : dt.constructors with
  | [] =>
    -- Zero constructors: opaque type
    Core.Decl.type (.con { name := dt.name.text, numargs := dt.typeArgs.length })
  | first :: rest =>
    let constrs : List (Lambda.LConstr Unit) := (first :: rest).map fun c =>
      { name := ⟨c.name.text, ()⟩
        args := c.args.map fun ⟨ n, ty ⟩ => (⟨n.text, ()⟩, translateType model ty) }
    let ldt : Lambda.LDatatype Unit := {
      name := dt.name.text
      typeArgs := dt.typeArgs.map (fun id => id.text)
      constrs := constrs
      constrs_ne := by simp [constrs]
    }
    Core.Decl.type (.data [ldt])

/--
Try to translate a Laurel Procedure marked `isFunctional` to a Core Function.
Returns `.error` with diagnostics if the procedure body contains disallowed constructs
(destructive assignments, loops, or procedure calls).
-/
def tryTranslatePureToFunction (proc : Procedure) (initState : TranslateState)
    : Except (Array DiagnosticModel) Core.Decl :=
  let (decl, finalState) := runTranslateM initState (translateProcedureToFunction proc)
  if finalState.diagnostics.isEmpty then
    .ok decl
  else
    .error finalState.diagnostics.toArray

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) (Core.Program × Array DiagnosticModel) := do
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
  }

  let result := resolve program
  let (program, model) := (result.program, result.model)
  let mut _resolutionDiags := result.errors
  let diamondErrors := validateDiamondFieldAccesses model program

  let program := heapParameterization model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  _resolutionDiags := _resolutionDiags ++ result.errors

  let program := typeHierarchyTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  _resolutionDiags := _resolutionDiags ++ result.errors
  let (program, modifiesDiags) := modifiesClausesTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  _resolutionDiags := _resolutionDiags ++ result.errors
  -- dbg_trace "=== Program after heapParameterization + modifiesClausesTransform ==="
  -- dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  -- dbg_trace "================================="
  let program := liftExpressionAssignments model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  _resolutionDiags := _resolutionDiags ++ result.errors

  -- Procedures marked isFunctional are translated to Core functions; all others become Core procedures.
  -- External procedures are completely ignored (not translated to Core).
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let (markedPure, procProcs) := nonExternal.partition (·.isFunctional)
  let initState : TranslateState := { model := model }
  -- Try to translate each isFunctional procedure to a Core function, collecting errors for failures
  let (pureErrors, pureFuncDecls) := markedPure.foldl (fun (errs, decls) p =>
    match tryTranslatePureToFunction p initState with
    | .error es => (errs ++ es.toList, decls)
    | .ok d     => (errs, decls.push d)) ([], #[])
  -- Translate procedures using the monad, collecting diagnostics from the final state
  let (procedures, procState) := runTranslateM initState do
    procProcs.mapM translateProcedure
  let procDiags := procState.diagnostics

  -- Translate Laurel constants to Core function declarations (0-ary functions)
  let (constantDecls, constantsState) := runTranslateM initState $ program.constants.mapM fun c => do
    let coreTy := translateType model c.type
    let body ← c.initializer.mapM (translateExpr ·)
    return Core.Decl.func {
      name := ⟨c.name.text, ()⟩
      typeArgs := []
      inputs := []
      output := coreTy
      body := body
    }

  -- Collect ALL errors from both functions, procedures, and resolution before deciding whether to fail
  let allErrors :=
    -- Not including resolution diagnostics yet because the Python through Laurel pipeline
    -- does not resolve yet.
    -- resolutionDiags.toList ++
    pureErrors ++ procDiags ++ constantsState.diagnostics
  if !allErrors.isEmpty then
    .error allErrors.toArray
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)

  -- Translate Laurel datatype definitions to Core datatype declarations
  let laurelDatatypeDecls := program.types.filterMap fun td => match td with
    | .Datatype dt => some (translateDatatypeDefinition model dt)
    | _ => none
  let program := {
    decls := laurelDatatypeDecls ++ constantDecls ++ pureFuncDecls.toList ++ procDecls
  }

  -- dbg_trace "=== Generated Strata Core Program ==="
  -- dbg_trace (toString (Std.Format.pretty (Strata.Core.formatProgram program) 100))
  -- dbg_trace "================================="
  pure (program, diamondErrors ++ modifiesDiags)

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (program : Program)
    (options : VerifyOptions := .default)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let (strataCoreProgram, translateDiags) ← match translate program with
    | .error translateErrorDiags => return .error translateErrorDiags
    | .ok result => pure result

  -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Strata Core program
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
    (options : VerifyOptions := .default): IO (Array Diagnostic) := do
  let results <- verifyToVcResults program options
  match results with
  | .error errors => return errors.map (fun dm => dm.toDiagnostic files)
  | .ok results => return results.filterMap (fun dm => dm.toDiagnostic files)


def verifyToDiagnosticModels (program : Program) (options : VerifyOptions := .default) : IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults program options
  match results with
  | .error errors => return errors
  | .ok results => return results.filterMap toDiagnosticModel

end Laurel
