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
import Strata.Languages.Laurel.EliminateValueReturns
public import Strata.Languages.Laurel.HeapParameterization
public import Strata.Languages.Laurel.TypeHierarchy
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.ModifiesClauses
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel
public import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.DDM.Util.DecimalRat
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
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

private def mdWithUnknownLoc : Imperative.MetaData Core.Expression :=
  #[⟨Imperative.MetaData.fileRange, .fileRange FileRange.unknown⟩]

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
  /-- Overflow check configuration -/
  overflowChecks : Core.OverflowChecks := {}
  /-- Do not process the produces Core program, since it has superfluous errors -/
  coreProgramHasSuperfluousErrors: Bool := false

/-- The translation monad: state over Except, allowing both accumulated diagnostics and hard failures -/
@[expose] abbrev TranslateM := OptionT (StateM TranslateState)

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Abort the Core program by setting the superfluous-errors flag and returning a dummy type. -/
private def throwTypeDiagnostic (ty : HighTypeMd) (msg : String) : TranslateM LMonoTy := do
  emitDiagnostic ((astNodeToCoreMd ty).toDiagnostic msg)
  modify fun s => { s with coreProgramHasSuperfluousErrors := true }
  return .tcons "Error" []

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighTypeMd) : TranslateM LMonoTy := do
  let model := (← get).model
  match _h : ty.val with
  | .TInt => return LMonoTy.int
  | .TBool => return LMonoTy.bool
  | .TString => return LMonoTy.string
  | .TBv n => return LMonoTy.bitvec n
  | .TVoid => return LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => return .tcons "Heap" []
  | .TTypedField _ => return .tcons "Field" []
  | .TSet elementType => return Core.mapTy (← translateType elementType) LMonoTy.bool
  | .TMap keyType valueType => return Core.mapTy (← translateType keyType) (← translateType valueType)
  | .UserDefined name =>
    match name.uniqueId.bind model.refToDef.get? with
    | some (.compositeType _) => return .tcons "Composite" []
    | some (.datatypeDefinition dt) => return .tcons dt.name.text []
    | some (.datatypeConstructor typeName _) => return .tcons typeName.text []
    | _ => do -- resolution should have already emitted a diagnostic
      modify fun s => { s with coreProgramHasSuperfluousErrors := true }
      return .tcons "Composite" []
  | .TCore s => return .tcons s []
  | .TReal => return LMonoTy.real
  | .Unknown => throwTypeDiagnostic ty "could not infer type"
  | _ => throwTypeDiagnostic ty "cannot translate type to Core: not supported yet"
termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (name : Identifier) : TranslateM LMonoTy := do
  translateType ((← get).model.get name).getType

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
  return LExpr.fvar Strata.SourceRange.none (⟨s!"DUMMY_VAR_{id}", ()⟩) none

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
  let md := astNodeToCoreMd expr
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
            return .fvar Strata.SourceRange.none ⟨name.text, ()⟩ (some (← translateType astNode.getType))
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
    | _ =>
      throwExprDiagnostic $ md.toDiagnostic s!"translateExpr: Invalid unary op: {repr op}" DiagnosticType.StrataBug
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
              have := AstNode.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite Strata.SourceRange.none bcond bthen belse
  | .StaticCall callee args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !model.isFunction callee then
        disallowed md "calls to procedures are not supported in functions or contracts"
      else
        let fnOp : Core.Expression.Expr := .op Strata.SourceRange.none ⟨callee.text, ()⟩ none
        args.attach.foldlM (fun acc ⟨arg, _⟩ => do
          let re ← translateExpr arg boundVars isPureContext
          return .app Strata.SourceRange.none acc re) fnOp
  | .Block [single] _ => translateExpr single boundVars isPureContext
  | .Forall ⟨ name, ty ⟩ trigger body =>
      let coreTy ← translateType ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.allTr Strata.SourceRange.none name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.all Strata.SourceRange.none name.text (some coreTy) coreBody
  | .Exists ⟨ name, ty ⟩ trigger body =>
      let coreTy ← translateType ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        return LExpr.existTr Strata.SourceRange.none name.text (some coreTy) coreTrig coreBody
      | none =>
        return LExpr.exist Strata.SourceRange.none name.text (some coreTy) coreBody
  | .Hole _ _ =>
      -- Holes should have been eliminated before translation.
      disallowed md "holes should have been eliminated before translation"
  | .ReferenceEquals e1 e2 =>
      let re1 ← translateExpr e1 boundVars isPureContext
      let re2 ← translateExpr e2 boundVars isPureContext
      return .eq Strata.SourceRange.none re1 re2
  | .Assign _ _ =>
      disallowed md "destructive assignments are not supported in functions or contracts"
  | .While _ _ _ _ =>
      disallowed md "loops are not supported in functions or contracts"
  | .Exit _ => disallowed md "exit is not supported in expression position"

  | .Block (⟨ .Assert _, innerSrc, innerMd⟩ :: rest) label => do
    _ ← disallowed (fileRangeToCoreMd innerSrc innerMd) "asserts are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc, md := innerMd } boundVars isPureContext
  | .Block (⟨ .Assume _, innerSrc, innerMd⟩ :: rest) label =>
    _ ← disallowed (fileRangeToCoreMd innerSrc innerMd) "assumes are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc, md := innerMd } boundVars isPureContext
  | .Block (⟨ .LocalVariable name ty (some initializer), innerSrc, innerMd⟩ :: rest) label => do
      let valueExpr ← translateExpr  initializer boundVars isPureContext
      let bodyExpr ← translateExpr { val := StmtExpr.Block rest label, source := innerSrc, md := innerMd } (name :: boundVars) isPureContext
      disallowed (fileRangeToCoreMd innerSrc innerMd) "local variables in functions are not YET supported"
      -- This doesn't work because of a limitation in Core.
      -- let coreMonoType := translateType ty
      -- return .app Strata.SourceRange.none (.abs Strata.SourceRange.none (some coreMonoType) bodyExpr) valueExpr
  | .Block (⟨ .LocalVariable name ty none, innerSrc, innerMd⟩ :: rest) label =>
    disallowed (fileRangeToCoreMd innerSrc innerMd) "local variables in functions must have initializers"
  | .Block (⟨ .IfThenElse cond thenBranch (some elseBranch), innerSrc, innerMd⟩ :: rest) label =>
    disallowed (fileRangeToCoreMd innerSrc innerMd) "if-then-else only supported as the last statement in a block"

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
  | .Return _ => disallowed md "return expression should be lowered in a separate pass"

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
    all_goals (have := AstNode.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (dbg_trace "BUG: metadata without a filerange"; default)
  s!"({fileRange.range.start})"

def defaultExprForType (ty : HighTypeMd) : TranslateM Core.Expression.Expr := do
  match ty.val with
  | .TInt => return .const Strata.SourceRange.none (.intConst 0)
  | .TBool => return .const Strata.SourceRange.none (.boolConst false)
  | .TString => return .const Strata.SourceRange.none (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy ← translateType ty
    return .fvar Strata.SourceRange.none (⟨"$default", ()⟩) (some coreTy)

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
  return [Core.Statement.init ident coreType (.det coreExpr) md]

/--
Translate Laurel StmtExpr to Core Statements using the `TranslateM` monad.
Diagnostics are emitted into the monad state.
-/
def translateStmt (stmt : StmtExprMd)
    : TranslateM (List Core.Statement) := do
  let s ← get
  let model := s.model
  let md := astNodeToCoreMd stmt
  match _h : stmt.val with
  | .Assert cond =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md]
  | .Assume cond =>
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts label =>
      let innerStmts ← stmts.flatMapM (fun s => translateStmt s)
      match label with
      | some l => return [Imperative.Stmt.block l innerStmts md]
      | none   => return innerStmts
  | .LocalVariable id ty initializer =>
      let coreMonoType ← translateType ty
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨id.text, ()⟩
      match initializer with
      | some (⟨ .StaticCall callee args, callSrc, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if model.isFunction callee then
            -- Translate as expression (function application)
            let coreExpr ← translateExpr { val := .StaticCall callee args, source := callSrc, md := callMd }
            return [Core.Statement.init ident coreType (.det coreExpr) md]
          else
            -- Translate as: var name; call name := callee(args)
            let coreArgs ← args.mapM (fun a => translateExpr a)
            let defaultExpr ← defaultExprForType ty
            let initStmt := Core.Statement.init ident coreType (.det defaultExpr) md
            let callStmt := Core.Statement.call [ident] callee.text coreArgs md
            return [initStmt, callStmt]
      | some (⟨ .InstanceCall .., _, _⟩) =>
          -- Instance method call as initializer: var name := target.method(args)
          -- Havoc the result since instance methods may be on unmodeled types
          let initStmt := Core.Statement.init ident coreType .nondet md
          return [initStmt]
      | some (⟨ .Hole _ _, _, _⟩) =>
          -- Hole initializer: treat as havoc (init without value)
          return [Core.Statement.init ident coreType .nondet md]
      | some initExpr =>
          let coreExpr ← translateExpr initExpr
          return [Core.Statement.init ident coreType (.det coreExpr) md]
      | none =>
          return [Core.Statement.init ident coreType .nondet md]
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier targetId, _, _ ⟩] =>
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
                -- Synthesize throwaway LHS variables for any outputs beyond the
                -- assigned target (e.g. void-returns-Any adds an extra output).
                let outputs := match model.get callee with
                  | .staticProcedure proc => proc.outputs
                  | .instanceProcedure _ proc => proc.outputs
                  | _ => []
                let mut inits : List Core.Statement := []
                let mut lhs : List Core.CoreIdent := [ident]
                for out in outputs.drop 1 do
                  let id ← freshId
                  let unusedIdent : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
                  let coreType := LTy.forAll [] (← translateType out.type)
                  inits := inits ++ [Core.Statement.init unusedIdent coreType .nondet md]
                  lhs := lhs ++ [unusedIdent]
                return inits ++ [Core.Statement.call lhs callee.text coreArgs md]
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
              return [Core.Statement.call lhsIdents callee.text coreArgs (astNodeToCoreMd value)]
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
      let bthen ← translateStmt thenBranch
      let belse ← match elseBranch with
                  | some e => translateStmt e
                  | none => pure []
      return [Imperative.Stmt.ite (.det bcond) bthen belse md]
  | .StaticCall callee args =>
      -- Check if this is a function or procedure
      if model.isFunction callee then
        -- Function call in statement position: preserve as unused init
        exprAsUnusedInit stmt md
      else
        let coreArgs ← args.mapM (fun a => translateExpr a)
        -- Synthesize throwaway LHS variables so Core arity checking
        -- passes (lhs.length == outputs.length).
        let outputs := match model.get callee with
          | .staticProcedure proc => proc.outputs
          | .instanceProcedure _ proc => proc.outputs
          | _ => []
        let mut inits : List Core.Statement := []
        let mut lhs : List Core.CoreIdent := []
        for out in outputs do
          let id ← freshId
          let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
          let coreType := LTy.forAll [] (← translateType out.type)
          inits := inits ++ [Core.Statement.init ident coreType .nondet md]
          lhs := lhs ++ [ident]
        return inits ++ [Core.Statement.call lhs callee.text coreArgs md]
  | .InstanceCall .. =>
      -- Instance method call as statement: no return value, treated as no-op
      return ([])
  | .Return valueOpt =>
      match valueOpt with
      | none =>
          return [.exit (some "$body") md]
      | some _ =>
          emitDiagnostic $ md.toDiagnostic "Return statement with value should have been eliminated by EliminateValueReturns pass" DiagnosticType.StrataBug
          modify fun s => { s with coreProgramHasSuperfluousErrors := true }
          return [.exit (some "$body") md]
  | .While cond invariants decreasesExpr body =>
      let condExpr ← translateExpr cond
      let invExprs ← invariants.mapM (translateExpr)
      let decreasingExprCore ← decreasesExpr.mapM (translateExpr)
      let bodyStmts ← translateStmt body
      return [Imperative.Stmt.loop (.det condExpr) decreasingExprCore invExprs bodyStmts md]
  | .Exit target =>
      return [Imperative.Stmt.exit (some target) md]
  | _ =>
      -- Expression in statement position: preserve as an unused variable init
      exprAsUnusedInit stmt md
  termination_by sizeOf stmt
  decreasing_by
    all_goals
      have hlt := AstNode.sizeOf_val_lt stmt
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
    let c : Core.Procedure.Check := { expr := checkExpr, md := astNodeToCoreMd check }
    return (label, c))

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (param : Parameter) : TranslateM (Core.CoreIdent × LMonoTy) := do
  let ident := ⟨param.name.text, ()⟩
  let ty ← translateType param.type
  return (ident, ty)

/--
Translate Laurel Procedure to Core Procedure using `TranslateM`.
Diagnostics from disallowed constructs in preconditions, postconditions, and body
are emitted into the monad state.
-/
def translateProcedure (proc : Procedure) : TranslateM Core.Procedure := do
  let inputPairs ← proc.inputs.mapM translateParameterToCore
  let inputs := inputPairs
  let outputs ← proc.outputs.mapM translateParameterToCore
  let header : Core.Procedure.Header := {
    name := proc.name.text
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  -- Translate preconditions
  let preconditions ← translateChecks proc.preconditions "requires"

  -- Translate postconditions for Opaque and Abstract bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds =>
        translateChecks postconds "postcondition"
    | _ => pure []
  let modifies : List Core.Expression.Ident := []
  let bodyStmts : List Core.Statement ←
    match proc.body with
    | .Transparent bodyExpr => translateStmt bodyExpr
    | .Opaque _postconds (some impl) _ => translateStmt impl
    | _ =>
      -- Bodiless procedure: assume postconditions so that verification of the
      -- procedure itself passes trivially, and inlining only introduces the
      -- postconditions as assumptions (not the unsound `assume false`).
      pure (postconditions.map fun (label, check) =>
        Core.Statement.assume label check.expr mdWithUnknownLoc)
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  let body : List Core.Statement := [.block "$body" bodyStmts mdWithUnknownLoc]
  let spec : Core.Procedure.Spec := { modifies, preconditions, postconditions }
  return { header, spec, body }

def translateInvokeOnAxiom (proc : Procedure) (trigger : StmtExprMd)
    : TranslateM (Option Core.Decl) := do
  let postconds := match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds => postconds
    | _ => []
  if postconds.isEmpty then return none
  -- All input param names become bound variables.
  -- buildQuants nests ∀ p1, ∀ p2, ..., ∀ pn :: body, so inside body the innermost
  -- binder (pn) is de Bruijn index 0, and the outermost (p1) is index n-1.
  -- translateExpr uses findIdx? on boundVars, so we must list params innermost-first
  -- (i.e. reversed) so that pn → 0, ..., p1 → n-1.
  let boundVars := proc.inputs.reverse.map (·.name)
  -- Translate postconditions and trigger with the full bound-var context
  let postcondExprs ← postconds.mapM (fun pc => translateExpr pc boundVars (isPureContext := true))
  let bodyExpr : Core.Expression.Expr := match postcondExprs with
    | [] => .const Strata.SourceRange.none (.boolConst true)
    | [e] => e
    | e :: rest => rest.foldl (fun acc x => LExpr.mkApp Strata.SourceRange.none boolAndOp [acc, x]) e
  let triggerExpr ← translateExpr trigger boundVars (isPureContext := true)
  -- Wrap in ∀ from outermost (first param) to innermost (last param).
  -- The trigger is placed on the innermost quantifier.
  let quantified ← buildQuants proc.inputs bodyExpr triggerExpr
  return some (.ax { name := s!"invokeOn_{proc.name.text}", e := quantified } proc.name.md)
where
  /-- Build `∀ p1 ... pn :: { trigger } body`. The trigger is on the innermost quantifier. -/
  buildQuants (params : List Parameter)
      (body : Core.Expression.Expr) (trigger : Core.Expression.Expr)
      : TranslateM Core.Expression.Expr := do
    match params with
    | [] => return body
    | [p] =>
      return LExpr.allTr Strata.SourceRange.none p.name.text (some (← translateType p.type)) trigger body
    | p :: rest => do
      let inner ← buildQuants rest body trigger
      return LExpr.all Strata.SourceRange.none p.name.text (some (← translateType p.type)) inner

structure LaurelTranslateOptions where
  emitResolutionErrors : Bool := true
  inlineFunctionsWhenPossible : Bool := false
  overflowChecks : Core.OverflowChecks := {}
  profile : Bool := false

/--
Translate a Laurel Procedure to a Core Function (when applicable) using `TranslateM`.
Diagnostics for disallowed constructs in the function body are emitted into the monad state.
-/
def translateProcedureToFunction (options: LaurelTranslateOptions) (isRecursive: Bool) (proc : Procedure) : TranslateM Core.Decl := do
  let inputs ← proc.inputs.mapM translateParameterToCore
  let outputTy ← match proc.outputs.head? with
    | some p => translateType p.type
    | none => pure LMonoTy.int
  -- Translate precondition to FuncPrecondition (skip trivial `true`)
  let preconditions ← proc.preconditions.mapM (fun precondition => do
    let checkExpr ← translateExpr precondition [] true
    return { expr := checkExpr, md := Strata.SourceRange.none })

  -- For recursive functions, infer the @[cases] parameter index: the first input
  -- whose type is a user-defined datatype (has constructors). This is the argument
  -- the evaluator will case-split on to unfold the recursion.
  -- TODO: Use the decreases of the function to determine where to put @[cases]
  -- First step should be to only support a decreases clause that is exactly one datatype parameter
  -- Since that's what Core supports
  let model := (← get).model
  let casesIdx : Option Nat :=
    if !isRecursive then none
    else proc.inputs.findIdx? fun p =>
      match p.type.val with
      | .UserDefined name => match model.get name with
        | .datatypeDefinition _ => true
        | _ => false
      | _ => false
  let attr : Array Strata.DL.Util.FuncAttr :=
    match casesIdx with
    | some i => #[.inlineIfConstr i]
    | none => if options.inlineFunctionsWhenPossible then #[.inline] else #[]

  let body ← match proc.body with
    | .Transparent bodyExpr => some <$> translateExpr bodyExpr [] (isPureContext := true)
    | .Opaque _ (some bodyExpr) _ =>
      emitDiagnostic (proc.name.md.toDiagnostic "functions with postconditions are not yet supported")
      some <$> translateExpr bodyExpr [] (isPureContext := true)
    | _ => pure none
  let f : Core.Function := {
    name := ⟨proc.name.text, ()⟩
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
    preconditions := preconditions
    isRecursive := isRecursive
    attr := attr
  }
  return .func f proc.name.md

/--
Translate a Laurel DatatypeDefinition to an `LDatatype Unit`.
-/
def translateDatatypeDefinition (dt : DatatypeDefinition)
    : TranslateM (Lambda.LDatatype Unit) := do
  let constrs ← dt.constructors.mapM fun c => do
    let args ← c.args.mapM fun ⟨ n, ty ⟩ => do
      return (⟨n.text, ()⟩, ← translateType ty)
    return { name := ⟨c.name.text, ()⟩
             args := args
             testerName := s!"{dt.name}..is{c.name}" : Lambda.LConstr Unit }
  -- Zero-constructor datatypes (e.g. TypeTag with no composite types) get a synthetic
  -- unit constructor so the type is valid and can be referenced by other datatypes.
  let constrs := if constrs.isEmpty then
      [{ name := ⟨s!"Mk{dt.name.text}", ()⟩, args := [] }]
    else constrs
  return {
    name := dt.name.text
    typeArgs := dt.typeArgs.map (fun id => id.text)
    constrs := constrs
    constrs_ne := by simp [constrs]; grind
    : Lambda.LDatatype Unit
  }

abbrev TranslateResult := (Option Core.Program) × (List DiagnosticModel)

/--
Translate an `OrderedLaurel` program to a `Core.Program`.
The `program` parameter is the lowered Laurel program, used for type definitions.
-/
def translateLaurelToCore (options: LaurelTranslateOptions) (program : Program) (ordered : OrderedLaurel): TranslateM Core.Program := do

  let coreDecls ← ordered.decls.flatMapM fun
    | .procs procs isRecursive => do
      -- For each SCC, determine if it is purely functional or contains procedures.
      let isFuncSCC := procs.all (·.isFunctional)
      if isFuncSCC then
        let funcs ← procs.mapM (translateProcedureToFunction options isRecursive)
        if isRecursive then
          let coreFuncs := funcs.filterMap (fun d => match d with
            | .func f _ => some f
            | _ => none)
          return [Core.Decl.recFuncBlock coreFuncs mdWithUnknownLoc]
        else
          return funcs
      else
        let procDecls ← procs.flatMapM fun proc => do
          let procDecl ← translateProcedure proc
          -- Turn free postconditions into axioms placed right behind the related procedure
          let axiomDecls : List Core.Decl ← match proc.invokeOn with
            | none => pure []
            | some trigger => do
              let axDecl? ← translateInvokeOnAxiom proc trigger
              pure axDecl?.toList
          return [Core.Decl.proc procDecl proc.name.md] ++ axiomDecls
        return procDecls
    | .datatypes dts => do
      let ldatatypes ← dts.mapM translateDatatypeDefinition
      return [Core.Decl.type (.data ldatatypes) mdWithUnknownLoc]
    | .constant c => do
      let coreTy ← translateType c.type
      let body ← c.initializer.mapM (translateExpr ·)
      return [Core.Decl.func {
        name := ⟨c.name.text, ()⟩
        typeArgs := []
        inputs := []
        output := coreTy
        body := body
      } mdWithUnknownLoc]


  -- Emit diagnostics for composite types with instance procedures.
  for td in program.types do
    if let .Composite ct := td then
      for proc in ct.instanceProcedures do
        emitDiagnostic $ proc.name.md.toDiagnostic
          s!"Instance procedure '{proc.name.text}' on composite type '{ct.name.text}' is not yet supported"
          DiagnosticType.NotYetImplemented
  pure { decls := coreDecls }

end -- public section
end Laurel
