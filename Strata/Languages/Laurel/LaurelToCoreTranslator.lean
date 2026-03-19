/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Options
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.DesugarShortCircuit
public import Strata.Languages.Laurel.InferHoleTypes
public import Strata.Languages.Laurel.EliminateHoles
import Strata.Languages.Laurel.EliminateReturnsInExpression
public import Strata.Languages.Laurel.HeapParameterization
public import Strata.Languages.Laurel.TypeHierarchy
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.ModifiesClauses
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.DatatypeGrouping
import Strata.DDM.Util.DecimalRat
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Util.Tactics

open Core (VCResult VCResults VerifyOptions)
open Core (intAddOp intSubOp intMulOp intSafeDivOp intSafeModOp intSafeDivTOp intSafeModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)
open Core (realAddOp realSubOp realMulOp realDivOp realNegOp realLtOp realLeOp realGtOp realGeOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

public section

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
  | .TReal => LMonoTy.real
  | .Unknown => .tcons "Any" [] -- TODO, abort execution since there is no valid Core type to translate Unknown to
  | _ => .tcons "NotSupportedYet" [] -- TODO, abort execution since there is no valid Core type to translate Unknown to
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (model : SemanticModel) (name : Identifier) : LMonoTy :=
  translateType model (model.get name).getType

def isFieldName (fieldNames : List Identifier) (name : Identifier) : Bool :=
  fieldNames.contains name

/-- Set of names that are translated to Core functions (not procedures) -/
@[expose] abbrev FunctionNames := List Identifier

/-- State threaded through expression and statement translation -/
structure TranslateState where
  /-- Diagnostics accumulated during translation -/
  diagnostics : List DiagnosticModel := []
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Constants known to the program (field constants, etc.) -/
  model : SemanticModel
  /-- Do not process the produces Core program, since it has superfluous errors -/
  coreProgramHasSuperfluousErrors: Bool := false

/-- The translation monad: state over Except, allowing both accumulated diagnostics and hard failures -/
@[expose] abbrev TranslateM := OptionT (StateM TranslateState)

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Run a `TranslateM` action, returning either a hard error or the result and final state -/
def runTranslateM (s : TranslateState) (m : TranslateM α) : (Option α × TranslateState) :=
  m s

def returnNone: TranslateM α :=
  StateT.pure none

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Throw a hard diagnostic error, aborting the current translation -/
def throwExprDiagnostic (d : DiagnosticModel): TranslateM Core.Expression.Expr := do
  emitDiagnostic d
  modify fun s => { s with coreProgramHasSuperfluousErrors := true }
  let id ← freshId
  return LExpr.fvar () (⟨s!"DUMMY_VAR_{id}", ()⟩) none

/--
Translate Laurel StmtExpr to Core Expression using the `TranslateM` monad.
Diagnostics for disallowed constructs are emitted into the monad state.

`isPureContext` should be `true` when translating function bodies or contract expressions.
In that case, disallowed constructs emit `DiagnosticModel` errors into the state.
When `false` (inside a procedure body statement), disallowed constructs throw a diagnostic
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
  let dummy := .fvar Strata.SourceRange.none (⟨s!"DUMMY_VAR_{← freshId}", ()⟩) none
  -- Emit an error in pure context; panic in impure context (lifting invariant violated)
  let disallowed (md : MetaData) (msg : String) : TranslateM Core.Expression.Expr := do
    if isPureContext then
      throwExprDiagnostic $ md.toDiagnostic msg
    else
      throwExprDiagnostic $ md.toDiagnostic s!"{msg} (should have been lifted)" DiagnosticType.StrataBug

  match h: expr.val with
  | .LiteralBool b => return .const Strata.SourceRange.none (.boolConst b)
  | .LiteralInt i => return .const Strata.SourceRange.none (.intConst i)
  | .LiteralString s => return .const Strata.SourceRange.none (.strConst s)
  | .LiteralDecimal d => return .const Strata.SourceRange.none (.realConst (Strata.Decimal.toRat d))
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          return .bvar Strata.SourceRange.none idx
      | none =>
        match model.get name with
        | .field _ f =>
            return .op Strata.SourceRange.none ⟨f.name.text, ()⟩ none
        | astNode =>
            return .fvar Strata.SourceRange.none ⟨name.text, ()⟩ (some (translateType model $ astNode.getType.getD (panic! "LaurelToCore.translateExpr"))) -- nopanic:ok)
  | .PrimitiveOp op [e] =>
    match op with
    | .Not =>
      let re ← translateExpr e boundVars isPureContext
      return .app Strata.SourceRange.none boolNotOp re
    | .Neg =>
      let re ← translateExpr e boundVars isPureContext
      let isReal := match (computeExprType model e).val with
        | .TReal => true | _ => false
      return .app Strata.SourceRange.none (if isReal then realNegOp else intNegOp) re
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}" -- nopanic:ok
  | .PrimitiveOp op [e1, e2] =>
    let re1 ← translateExpr e1 boundVars isPureContext
    let re2 ← translateExpr e2 boundVars isPureContext
    let binOp (bop : Core.Expression.Expr) : Core.Expression.Expr :=
      LExpr.mkApp Strata.SourceRange.none bop [re1, re2]
    let isReal := match (computeExprType model e1).val, (computeExprType model e2).val with
      | .TReal, _ | _, .TReal => true
      | _, _ => false
    match op with
    | .Eq => return .eq Strata.SourceRange.none re1 re2
    | .Neq => return .app Strata.SourceRange.none boolNotOp (.eq Strata.SourceRange.none re1 re2)
    | .And => return binOp boolAndOp
    | .Or => return binOp boolOrOp
    | .AndThen => return .ite Strata.SourceRange.none re1 re2 (.boolConst Strata.SourceRange.none false)
    | .OrElse => return .ite Strata.SourceRange.none re1 (.boolConst Strata.SourceRange.none true) re2
    | .Implies => return .ite Strata.SourceRange.none re1 re2 (.boolConst Strata.SourceRange.none true)
    | .Add => return binOp (if isReal then realAddOp else intAddOp)
    | .Sub => return binOp (if isReal then realSubOp else intSubOp)
    | .Mul => return binOp (if isReal then realMulOp else intMulOp)
    | .Div => return binOp (if isReal then realDivOp else intSafeDivOp)
    | .Mod => return binOp intSafeModOp
    | .DivT => return binOp intSafeDivTOp
    | .ModT => return binOp intSafeModTOp
    | .Lt => return binOp (if isReal then realLtOp else intLtOp)
    | .Leq => return binOp (if isReal then realLeOp else intLeOp)
    | .Gt => return binOp (if isReal then realGtOp else intGtOp)
    | .Geq => return binOp (if isReal then realGeOp else intGeOp)
    | .StrConcat => return binOp strConcatOp
    | _ =>
        throwExprDiagnostic $ md.toDiagnostic s!"Invalid binary op: {repr op}" DiagnosticType.NotYetImplemented
  | .PrimitiveOp op args =>
      throwExprDiagnostic $ md.toDiagnostic s!"PrimitiveOp {repr op} with {args.length} args is not supported" DiagnosticType.UserError
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond boundVars isPureContext
      let bthen ← translateExpr thenBranch boundVars isPureContext
      let belse ← match elseBranch with
        | none =>
            throwExprDiagnostic $ md.toDiagnostic s!"if-then without else expression" DiagnosticType.NotYetImplemented
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := WithMetadata.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite Strata.SourceRange.none bcond bthen belse
  | .StaticCall callee args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !model.isFunction callee then
        disallowed expr.md "calls to procedures are not supported in functions or contracts"
      else
        let fnOp : Core.Expression.Expr := .op Strata.SourceRange.none ⟨callee.text, ()⟩ none
        args.attach.foldlM (fun acc ⟨arg, _⟩ => do
          let re ← translateExpr arg boundVars isPureContext
          return .app Strata.SourceRange.none acc re) fnOp
  | .Block [single] _ => translateExpr single boundVars isPureContext
  | .Forall ⟨ name, ty ⟩ trigger body =>
      let coreTy := translateType model ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.allTr Strata.SourceRange.none name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.all Strata.SourceRange.none name.text (some coreTy) coreBody
  | .Exists ⟨ name, ty ⟩ trigger body =>
      let coreTy := translateType model ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.existTr Strata.SourceRange.none name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.exist Strata.SourceRange.none name.text (some coreTy) coreBody
  | .Hole _ _ =>
      -- Holes should have been eliminated before translation.
      disallowed expr.md "holes should have been eliminated before translation"
  | .ReferenceEquals e1 e2 =>
      let re1 ← translateExpr e1 boundVars isPureContext
      let re2 ← translateExpr e2 boundVars isPureContext
      return .eq Strata.SourceRange.none re1 re2
  | .Assign _ _ =>
      disallowed expr.md "destructive assignments are not supported in functions or contracts"
  | .While _ _ _ _ =>
      disallowed expr.md "loops are not supported in functions or contracts"
  | .Exit _ => disallowed expr.md "exit is not supported in expression position"

  | .Block (⟨ .Assert _, md⟩ :: rest) label => do
    _ ← disallowed md "asserts are not YET supported in functions or contracts"
    translateExpr ⟨ StmtExpr.Block rest label, md ⟩ boundVars isPureContext
  | .Block (⟨ .Assume _, md⟩ :: rest) label =>
    _ ← disallowed md "assumes are not YET supported in functions or contracts"
    translateExpr ⟨ StmtExpr.Block rest label, md ⟩ boundVars isPureContext
  | .Block (⟨ .LocalVariable name ty (some initializer), md⟩ :: rest) label => do
      let valueExpr ← translateExpr  initializer boundVars isPureContext
      let bodyExpr ← translateExpr ⟨ StmtExpr.Block rest label, md ⟩ (name :: boundVars) isPureContext
      disallowed md "local variables in functions are not YET supported"
      -- This doesn't work because of a limitation in Core.
      -- let coreMonoType := translateType ty
      -- return .app Strata.SourceRange.none (.abs () (some coreMonoType) bodyExpr) valueExpr
  | .Block (⟨ .LocalVariable name ty none, md⟩ :: rest) label =>
    disallowed md "local variables in functions must have initializers"
  | .Block (⟨ .IfThenElse cond thenBranch (some elseBranch), md⟩ :: rest) label =>
    disallowed md "if-then-else only supported as the last statement in a block"

  | .IsType _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "IsType should have been lowered" DiagnosticType.StrataBug
  | .New _ => throwExprDiagnostic $ md.toDiagnostic s!"New should have been eliminated by typeHierarchyTransform" DiagnosticType.StrataBug
  | .FieldSelect target fieldId =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      throwExprDiagnostic $ md.toDiagnostic s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldId.text}" DiagnosticType.StrataBug
  | .Block _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "block expression should have been lowered in a separate pass" DiagnosticType.StrataBug
  | .LocalVariable _ _ _ =>
      throwExprDiagnostic $ md.toDiagnostic "local variable expression should be lowered in a separate pass" DiagnosticType.StrataBug
  | .Return _ => disallowed expr.md "return expression should be lowered in a separate pass"

  | .AsType target _ => throwExprDiagnostic $ md.toDiagnostic "AsType expression translation" DiagnosticType.NotYetImplemented
  | .Assigned _ => throwExprDiagnostic $ md.toDiagnostic "assigned expression translation" DiagnosticType.NotYetImplemented
  | .Old value => throwExprDiagnostic $ md.toDiagnostic "old expression translation" DiagnosticType.NotYetImplemented
  | .Fresh _ => throwExprDiagnostic $ md.toDiagnostic "fresh expression translation" DiagnosticType.NotYetImplemented
  | .Assert _ => throwExprDiagnostic $ md.toDiagnostic "assert expression translation" DiagnosticType.NotYetImplemented
  | .Assume _ => throwExprDiagnostic $ md.toDiagnostic "assume expression translation" DiagnosticType.NotYetImplemented
  | .ProveBy value _ => throwExprDiagnostic $ md.toDiagnostic "proveBy expression translation" DiagnosticType.NotYetImplemented
  | .ContractOf _ _ => throwExprDiagnostic $ md.toDiagnostic "contractOf expression translation" DiagnosticType.NotYetImplemented
  | .Abstract => throwExprDiagnostic $ md.toDiagnostic "abstract expression translation" DiagnosticType.NotYetImplemented
  | .All => throwExprDiagnostic $ md.toDiagnostic "all expression translation" DiagnosticType.NotYetImplemented
  | .InstanceCall target callee args => throwExprDiagnostic $ md.toDiagnostic "instance call expression translation" DiagnosticType.NotYetImplemented
  | .PureFieldUpdate _ _ _ => throwExprDiagnostic $ md.toDiagnostic "pure field update expression translation" DiagnosticType.NotYetImplemented
  | .This => throwExprDiagnostic $ md.toDiagnostic "this expression translation" DiagnosticType.NotYetImplemented
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (dbg_trace "BUG: metadata without a filerange"; default)
  s!"({fileRange.range.start})"

def defaultExprForType (model : SemanticModel) (ty : HighTypeMd) : Core.Expression.Expr :=
  match ty.val with
  | .TInt => .const Strata.SourceRange.none (.intConst 0)
  | .TBool => .const Strata.SourceRange.none (.boolConst false)
  | .TString => .const Strata.SourceRange.none (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy := translateType model ty
    .fvar Strata.SourceRange.none (⟨"$default", ()⟩) (some coreTy)

/--
Translate an expression in statement position into a `var $unused_N := expr` init.
Preserves the expression so it is not silently dropped from the Core output.
-/
private def exprAsUnusedInit (expr : StmtExprMd) (md : Imperative.MetaData Core.Expression)
    : TranslateM (List Core.Statement) := do
  let coreExpr ← translateExpr expr
  let id ← freshId
  let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
  let tyVarName := s!"$__ty_unused_{id}"
  let coreType := LTy.forAll [tyVarName] (.ftvar tyVarName)
  return [Core.Statement.init ident coreType (some coreExpr) md]

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
  | .Assert cond =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md]
  | .Assume cond =>
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts label =>
      let innerStmts ← stmts.flatMapM (fun s => translateStmt outputParams s)
      match label with
      | some l => return [Imperative.Stmt.block l innerStmts md]
      | none   => return innerStmts
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
      | some (⟨ .InstanceCall .., _⟩) =>
          -- Instance method call as initializer: var name := target.method(args)
          -- Havoc the result since instance methods may be on unmodeled types
          let initStmt := Core.Statement.init ident coreType none md
          return [initStmt]
      | some (⟨ .Hole _ _, _⟩) =>
          -- Hole initializer: treat as havoc (init without value)
          return [Core.Statement.init ident coreType none md]
      | some initExpr =>
          let coreExpr ← translateExpr initExpr
          return [Core.Statement.init ident coreType (some coreExpr) md]
      | none =>
          return [Core.Statement.init ident coreType none md]
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
          | .InstanceCall .. =>
              -- Instance method call: havoc the target variable
              return [Core.Statement.havoc ident md]
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
          | .InstanceCall .. =>
              -- Instance method call: havoc all target variables
              let havocStmts := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (Core.Statement.havoc ⟨name.text, ()⟩ md)
                | _ => none
              return (havocStmts)
          | _ =>
              emitDiagnostic $ md.toDiagnostic "Assignments with multiple target but without a RHS call should not be constructed"
              returnNone
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
        -- Function call in statement position: preserve as unused init
        exprAsUnusedInit stmt md
      else
        let coreArgs ← args.mapM (fun a => translateExpr a)
        return [Core.Statement.call [] callee.text coreArgs md]
  | .InstanceCall .. =>
      -- Instance method call as statement: no return value, treated as no-op
      return ([])
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
          emitDiagnostic $ md.toDiagnostic "Return statement with value but procedure has no output parameters"
          return [.exit (some "$body") md]
  | .While cond invariants decreasesExpr body =>
      let condExpr ← translateExpr cond
      let invExprs ← invariants.mapM (translateExpr)
      let decreasingExprCore ← decreasesExpr.mapM (translateExpr)
      let bodyStmts ← translateStmt outputParams body
      return [Imperative.Stmt.loop condExpr decreasingExprCore invExprs bodyStmts md]
  | .Exit target =>
      return [Imperative.Stmt.exit (some target) md]
  | _ =>
      -- Expression in statement position: preserve as an unused variable init
      exprAsUnusedInit stmt md
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
    | _ => pure [Core.Statement.assume "no_body" (.const Strata.SourceRange.none (.boolConst false)) .empty]
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  let body : List Core.Statement := [.block "$body" bodyStmts .empty]
  let spec : Core.Procedure.Spec := { modifies, preconditions, postconditions }
  return { header, spec, body }

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
    return { expr := checkExpr, md := Strata.SourceRange.none })

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
Translate a Laurel DatatypeDefinition to an `LDatatype Unit`.
-/
def translateDatatypeDefinition (model : SemanticModel) (dt : DatatypeDefinition)
    : Lambda.LDatatype Unit :=
  let constrs : List (Lambda.LConstr Unit) := dt.constructors.map fun c =>
    { name := ⟨c.name.text, ()⟩
      args := c.args.map fun ⟨ n, ty ⟩ => (⟨n.text, ()⟩, translateType model ty)
      testerName := s!"{dt.name}..is{c.name}" }
  -- Zero-constructor datatypes (e.g. TypeTag with no composite types) get a synthetic
  -- unit constructor so the type is valid and can be referenced by other datatypes.
  let constrs := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
  { name := dt.name.text
    typeArgs := dt.typeArgs.map (fun id => id.text)
    constrs := constrs
    constrs_ne := by simp [constrs]; grind
  }

structure LaurelTranslateOptions where
  emitResolutionErrors : Bool := true

abbrev TranslateResult := (Option Core.Program) × (List DiagnosticModel)
/--
Translate Laurel Program to Core Program
-/
def translate (options: LaurelTranslateOptions) (program : Program): TranslateResult :=
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
  }

  let result := resolve program
  let (program, model) := (result.program, result.model)
  let diamondErrors := validateDiamondFieldAccesses model program

  let program := heapParameterization model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)

  let program := typeHierarchyTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let (program, modifiesDiags) := modifiesClausesTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  -- dbg_trace "=== Program after heapParameterization + modifiesClausesTransform ==="
  -- dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
