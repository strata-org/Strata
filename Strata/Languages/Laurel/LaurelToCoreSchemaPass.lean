/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Options
public import Strata.Languages.Laurel.PushOldInward
public import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
public import Strata.Languages.Laurel.Resolution
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.Languages.Core.Factory
import Strata.Languages.Laurel.LaurelTypes

open Core (VerifyOptions)
open Core (intAddOp intSubOp intMulOp intDivOp intSafeDivOp intModOp intSafeModOp intDivTOp intSafeDivTOp intModTOp intSafeModTOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp strConcatOp)
open Core (realAddOp realSubOp realMulOp realDivOp realNegOp realLtOp realLeOp realGtOp realGeOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

public section

private def mdWithUnknownLoc : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofProvenance (.synthesized .laurelToCore)

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
  /-- Inout parameter names of the procedure currently being translated.
      Used by the `.Old (Var (Local n))` arm to defensively check `n` against
      the procedure's inout list. Empty when not translating a procedure body. -/
  currentProcInouts : List String := []
  /-- Diagnostics that indicate the Core program should not be processed further.
      When non-empty, the produced Core program is suppressed. Each entry records
      why the program was deemed invalid so that if no other diagnostics explain
      the suppression, these can be surfaced to the user. -/
  coreDiagnostics : List DiagnosticModel := []

/-- The translation monad: state over Except, allowing both accumulated diagnostics and hard failures -/
@[expose] abbrev TranslateM := OptionT (StateM TranslateState)

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Emit a core diagnostic that flags the Core program as invalid. -/
def emitCoreDiagnostic (d : DiagnosticModel) : TranslateM Unit :=
  modify fun s => { s with coreDiagnostics := s.coreDiagnostics ++ [d] }

private def invalidCoreType (source : Option FileRange) (reason : String) : TranslateM LMonoTy := do
  emitCoreDiagnostic (diagnosticFromSource source reason DiagnosticType.StrataBug)
  return .tcons s!"LaurelResolutionErrorPlaceholder" []

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
  | .TSet elementType => return Core.mapTy (← translateType elementType) LMonoTy.bool
  | .TMap keyType valueType => return Core.mapTy (← translateType keyType) (← translateType valueType)
  | .UserDefined name =>
    match model.get? name with
    | some (.datatypeDefinition dt) => return .tcons dt.name.text []
    | some (.datatypeConstructor typeName _) => return .tcons typeName.text []
    | _ => do -- resolution should have already emitted a diagnostic
      emitCoreDiagnostic (diagnosticFromSource ty.source s!"UserDefined type {name} could not be resolved to a composite or datatype" DiagnosticType.StrataBug)
      return .tcons "Composite" []
  | .TCore s => return .tcons s []
  | .TReal => return LMonoTy.real
  | .MultiValuedExpr _ => invalidCoreType ty.source "MultiValuedExpr type encountered during Core translation"
  | .Unknown => invalidCoreType ty.source "Unknown type encountered during Core translation"
  | _ => do
    invalidCoreType ty.source s!"cannot translate type to Core: not supported yet"

termination_by ty.val
decreasing_by all_goals (first | (cases elementType; term_by_mem) | (cases keyType; term_by_mem) | (cases valueType; term_by_mem))

def lookupType (name : Identifier) : TranslateM LMonoTy := do
  translateType ((← get).model.get name).getType

/-- Run a `TranslateM` action, returning either a hard error or the result and final state -/
def runTranslateM (s : TranslateState) (m : TranslateM α) : (Option α × TranslateState) :=
  m s

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Throw a hard diagnostic error, aborting the current translation -/
def throwExprDiagnostic (d : DiagnosticModel): TranslateM Core.Expression.Expr := do
  emitDiagnostic d
  emitCoreDiagnostic d
  return default

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
  let disallowed (source : Option FileRange) (msg : String) : TranslateM Core.Expression.Expr := do
      throwExprDiagnostic $ diagnosticFromSource source msg

  match h: expr.val with
  | .LiteralBool b => return .const () (.boolConst b)
  | .LiteralInt i => return .const () (.intConst i)
  | .LiteralString s => return .const () (.strConst s)
  | .LiteralDecimal d => return .const () (.realConst (StrataDDM.Decimal.toRat d))
  | .LiteralBv value width => return .const () (.bitvecConst width (BitVec.ofNat width value))
  | .Var (.Local name) =>
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
            return .fvar () ⟨name.text, ()⟩ (some (← translateType astNode.getType))
  | .Var (.Declare _) =>
      throwExprDiagnostic $ md.toDiagnostic "variable declaration in expression context should have been lowered" DiagnosticType.StrataBug
  | .PrimitiveOp op [e] _ =>
    match op with
    | .Not =>
      let re ← translateExpr e boundVars isPureContext
      return .app () boolNotOp re
    | .Neg =>
      let re ← translateExpr e boundVars isPureContext
      let isReal := match (computeExprType model e).val with
        | .TReal => true | _ => false
      return .app () (if isReal then realNegOp else intNegOp) re
    | _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source s!"translateExpr: Invalid unary op: {repr op}" DiagnosticType.StrataBug
  | .PrimitiveOp op [e1, e2] skipProof =>
    let re1 ← translateExpr e1 boundVars isPureContext
    let re2 ← translateExpr e2 boundVars isPureContext
    let binOp (bop : Core.Expression.Expr) : Core.Expression.Expr :=
      LExpr.mkApp () bop [re1, re2]
    let isReal := match (computeExprType model e1).val, (computeExprType model e2).val with
      | .TReal, _ | _, .TReal => true
      | _, _ => false
    match op with
    | .Eq => return .eq () re1 re2
    | .Neq => return .app () boolNotOp (.eq () re1 re2)
    | .And => return binOp boolAndOp
    | .Or => return binOp boolOrOp
    | .AndThen => return .ite () re1 re2 (.boolConst () false)
    | .OrElse => return .ite () re1 (.boolConst () true) re2
    | .Implies => return .ite () re1 re2 (.boolConst () true)
    | .Add => return binOp (if isReal then realAddOp else intAddOp)
    | .Sub => return binOp (if isReal then realSubOp else intSubOp)
    | .Mul => return binOp (if isReal then realMulOp else intMulOp)
    | .Div => return binOp (if isReal then realDivOp else if skipProof then intDivOp else intSafeDivOp )
    | .Mod => return binOp (if skipProof then intModOp else intSafeModOp)
    | .DivT => return binOp (if skipProof then intDivTOp else intSafeDivTOp)
    | .ModT => return binOp (if skipProof then intModTOp else intSafeModTOp)
    | .Lt => return binOp (if isReal then realLtOp else intLtOp)
    | .Leq => return binOp (if isReal then realLeOp else intLeOp)
    | .Gt => return binOp (if isReal then realGtOp else intGtOp)
    | .Geq => return binOp (if isReal then realGeOp else intGeOp)
    | .StrConcat => return binOp strConcatOp
    | _ =>
        throwExprDiagnostic $ diagnosticFromSource expr.source s!"Invalid binary op: {repr op}" DiagnosticType.NotYetImplemented
  | .PrimitiveOp op args _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source s!"PrimitiveOp {repr op} with {args.length} args is not supported" DiagnosticType.UserError
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond boundVars isPureContext
      let bthen ← translateExpr thenBranch boundVars isPureContext
      let belse ← match elseBranch with
        | none =>
            throwExprDiagnostic $ diagnosticFromSource expr.source s!"if-then without else expression" DiagnosticType.NotYetImplemented
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := AstNode.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite () bcond bthen belse
  | .StaticCall callee args =>
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && !model.isFunction callee then
        disallowed expr.source s!"calls to procedures are not supported in functions or contracts"
      else
        let fnOp : Core.Expression.Expr := .op () ⟨callee.text, ()⟩ none
        args.attach.foldlM (fun acc ⟨arg, _⟩ => do
          let re ← translateExpr arg boundVars isPureContext
          return .app () acc re) fnOp
  | .Block [single] _ => translateExpr single boundVars isPureContext
  | .Quantifier mode ⟨ name, ty ⟩ trigger body =>
      let coreTy ← translateType ty
      let coreBody ← translateExpr body (name :: boundVars) isPureContext
      match _: trigger with
      | some trig =>
        let coreTrig ← translateExpr trig (name :: boundVars) isPureContext
        match mode with
        | .Forall => return LExpr.allTr () name.text (some coreTy) coreTrig coreBody
        | .Exists => return LExpr.existTr () name.text (some coreTy) coreTrig coreBody
      | none =>
        match mode with
        | .Forall => return LExpr.all () name.text (some coreTy) coreBody
        | .Exists => return LExpr.exist () name.text (some coreTy) coreBody
  | .Hole _ _ =>
      -- Holes should have been eliminated before translation.
      disallowed expr.source "holes should have been eliminated before translation"
  | .ReferenceEquals e1 e2 =>
      let re1 ← translateExpr e1 boundVars isPureContext
      let re2 ← translateExpr e2 boundVars isPureContext
      return .eq () re1 re2
  | .Assign _ _ =>
      disallowed expr.source "destructive assignments are not supported in transparent bodies or contracts"
  | .IncrDecr _ _ _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source
        "IncrDecr should have been eliminated by EliminateIncrDecr pass" DiagnosticType.StrataBug
  | .While _ _ _ _ _ =>
      disallowed expr.source "loops are not supported in functions or contracts"
  | .Exit _ => disallowed expr.source "exit is not supported in expression position"

  | .Block (⟨ .Assert _, innerSrc⟩ :: rest) label => do
    _ ← disallowed innerSrc "asserts are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .Assume _, innerSrc⟩ :: rest) label =>
    _ ← disallowed innerSrc "assumes are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .Assign [⟨ .Declare ⟨name, ty ⟩, _source⟩] initializer, innerSrc⟩ :: rest) label => do
      let valueExpr ← translateExpr initializer boundVars isPureContext
      let bodyExpr ← translateExpr { val := StmtExpr.Block rest label, source := innerSrc } (name :: boundVars) isPureContext
      let coreMonoType ← translateType ty
      return .app () (.abs () name.text (some coreMonoType) bodyExpr) valueExpr
  | .Block (⟨ .Var (.Declare _), innerSrc⟩ :: rest) label => do
    _ ← disallowed innerSrc "local variables in functions must have initializers"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .IfThenElse cond thenBranch (some elseBranch), innerSrc⟩ :: rest) label =>
    disallowed innerSrc "if-then-else only supported as the last statement in a block"

  | .Var (.Field target fieldId) =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      throwExprDiagnostic $ diagnosticFromSource expr.source s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldId.text}" DiagnosticType.StrataBug
  | .Block (⟨ .Assign _ _, assignSource⟩ :: tail) _ =>
      disallowed assignSource "destructive assignments are not supported in transparent bodies or contracts"
  | .Block (⟨ .While _ _ _ _ _, whileSource⟩ :: tail) _ =>
      disallowed whileSource "loops are not supported in functions or contracts"
  | .Block (head :: tail) _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source s!"block expression starting with {head.val.constructorName} should have been lowered in a separate pass" DiagnosticType.StrataBug
  | .Block [] _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source "empty block expression should have been lowered in a separate pass" DiagnosticType.StrataBug
  | .Return _ => disallowed expr.source "return expression should be lowered in a separate pass"
  | .IsType _ _ =>
      throwExprDiagnostic $ diagnosticFromSource expr.source "IsType should have been lowered" DiagnosticType.StrataBug
  | .New _ => throwExprDiagnostic $ diagnosticFromSource expr.source s!"New should have been eliminated by typeHierarchyTransform" DiagnosticType.StrataBug
  | .AsType target _ => throwExprDiagnostic $ diagnosticFromSource expr.source "AsType expression translation" DiagnosticType.NotYetImplemented
  | .Assigned _ => throwExprDiagnostic $ diagnosticFromSource expr.source "assigned expression translation" DiagnosticType.NotYetImplemented
  | .Old value =>
      -- `pushOldInward` is expected to leave every `Old` wrapping `Var (Local n)`
      -- with `n` an inout parameter of the enclosing procedure. We do not rely on
      -- a static proof of this; the guarantee is enforced at translate time: if
      -- PushOldInward has a bug or a later pass mutates the AST, we emit a
      -- StrataBug diagnostic instead of silently producing a dangling `mkOld n`
      -- name.
      match value.val with
      | .Var (.Local name) =>
          let inouts := s.currentProcInouts
          if !inouts.contains name.text then
            throwExprDiagnostic $ diagnosticFromSource expr.source
              s!"old({name.text}) refers to a name that is not an inout parameter \
                 of the enclosing procedure (inouts: {inouts}). This violates the \
                 pushOldInward normalization invariant."
              DiagnosticType.StrataBug
          else
            let coreTy ← translateType (model.get name).getType
            return .fvar () (Core.CoreIdent.mkOld name.text) (some coreTy)
      | _ =>
          throwExprDiagnostic $ diagnosticFromSource expr.source
            "old(...) should have been pushed inward to a variable reference. \
             This violates the pushOldInward normalization invariant."
            DiagnosticType.StrataBug
  | .Fresh _ => throwExprDiagnostic $ diagnosticFromSource expr.source "fresh expression translation" DiagnosticType.NotYetImplemented
  | .Assert _ => throwExprDiagnostic $ diagnosticFromSource expr.source "assert expression translation" DiagnosticType.NotYetImplemented
  | .Assume _ => throwExprDiagnostic $ diagnosticFromSource expr.source "assume expression translation" DiagnosticType.NotYetImplemented
  | .ProveBy value _ => throwExprDiagnostic $ diagnosticFromSource expr.source "proveBy expression translation" DiagnosticType.NotYetImplemented
  | .ContractOf _ _ => throwExprDiagnostic $ diagnosticFromSource expr.source "contractOf expression translation" DiagnosticType.NotYetImplemented
  | .Abstract => throwExprDiagnostic $ diagnosticFromSource expr.source "abstract expression translation" DiagnosticType.NotYetImplemented
  | .All => throwExprDiagnostic $ diagnosticFromSource expr.source "all expression translation" DiagnosticType.NotYetImplemented
  | .InstanceCall target callee args => throwExprDiagnostic $ diagnosticFromSource expr.source "instance call expression translation" DiagnosticType.NotYetImplemented
  | .PureFieldUpdate _ _ _ => throwExprDiagnostic $ diagnosticFromSource expr.source "pure field update expression translation" DiagnosticType.NotYetImplemented
  | .This => throwExprDiagnostic $ diagnosticFromSource expr.source "this expression translation" DiagnosticType.NotYetImplemented
  termination_by expr
  decreasing_by
    all_goals (have := AstNode.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  match Imperative.getProvenance md with
  | some (.loc _ range) => s!"({range.start})"
  | some (.synthesized _) => "(0)"
  | none => "(unknown)"

def defaultExprForType (ty : HighTypeMd) : TranslateM Core.Expression.Expr := do
  match ty.val with
  | .TInt => return .const () (.intConst 0)
  | .TBool => return .const () (.boolConst false)
  | .TString => return .const () (.strConst "")
  | _ =>
    -- For types without a natural default (arrays, composites, etc.),
    -- use a fresh free variable. This is only used when the value is
    -- immediately overwritten by a procedure call.
    let coreTy ← translateType ty
    return .fvar () (⟨"$default", ()⟩) (some coreTy)

/--
Translate an expression in statement position into a `var $unused_N := expr` init.
Preserves the expression so it is not silently dropped from the Core output.
-/
private def exprAsUnusedInit (expr : StmtExprMd) (md : Imperative.MetaData Core.Expression)
    : TranslateM (List Core.Statement) := do
  let coreExpr ← translateExpr expr
  let id ← freshId
  let model := (← get).model
  let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
  let ty ← translateType (computeExprType model expr)
  -- The empty type-variable list is valid because Laurel does not currently
  -- support polymorphism. If polymorphism is added, this will need updating.
  let coreType := LTy.forAll [] ty
  return [Core.Statement.init ident coreType (.det coreExpr) md]

def throwStmtDiagnostic (d : DiagnosticModel): TranslateM (List Core.Statement) := do
  emitDiagnostic d
  emitCoreDiagnostic d
  return []

/--
Look up the callee's signature and convert positional `coreArgs` into Core
`CallArg`s, emitting `.inoutArg ident` for parameters that appear in both
inputs and outputs (true inout) and `.inArg` otherwise. Returns the call args
along with the callee's outputs and inout names so the caller can build the
matching `.outArg` list. `md` locates the StrataBug diagnostic emitted when
an inout argument is not a variable reference.
-/
private def buildCallArgs (calleeId : Identifier) (coreArgs : List Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : TranslateM (List (Core.CallArg Core.Expression) × List Parameter × List String) := do
  let s ← get
  let (calleeInputs, calleeOutputs) := match s.model.get calleeId with
    | .staticProcedure proc => (proc.inputs, proc.outputs)
    | .instanceProcedure _ proc => (proc.inputs, proc.outputs)
    | _ => ([], [])
  let calleeInputNames := calleeInputs.map (·.name.text)
  let calleeOutputNames := calleeOutputs.map (·.name.text)
  let calleeInoutNames := calleeInputNames.filter (calleeOutputNames.contains ·)
  let inoutInputIndices := calleeInputNames.zipIdx.filterMap fun (name, i) =>
    if calleeInoutNames.contains name then some i else none
  let mut callArgs : List (Core.CallArg Core.Expression) := []
  for (arg, i) in coreArgs.zipIdx do
    if inoutInputIndices.contains i then
      match arg with
      | .fvar _ ident _ => callArgs := callArgs ++ [.inoutArg ident]
      | _ =>
        -- Non-fvar inout arg can't be wired as `.inoutArg`; flag it.
        emitDiagnostic $ md.toDiagnostic
          s!"inout argument at index {i} of call to '{calleeId.text}' is not a \
             variable reference, so the output side of the inout cannot be \
             wired through. This should not happen after the preceding passes."
          DiagnosticType.StrataBug
        modify fun st => { st with coreProgramHasSuperfluousErrors := true }
        callArgs := callArgs ++ [.inArg arg]
    else
      callArgs := callArgs ++ [.inArg arg]
  return (callArgs, calleeOutputs, calleeInoutNames)

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
      let coreExpr ← translateExpr cond.condition [] (isPureContext := true)
      let md' := match cond.summary with
        | some msg => md.pushElem Imperative.MetaData.propertySummary (.msg msg)
        | none => md
      return [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md']
  | .Assume cond =>
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      return [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts label =>
      let innerStmts ← stmts.flatMapM (fun s => translateStmt s)
      match label with
      | some l => return [Imperative.Stmt.block l innerStmts md]
      | none   => return innerStmts
  | .Var (.Declare param) =>
      let coreMonoType ← translateType param.type
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨param.name.text, ()⟩
      return [Core.Statement.init ident coreType .nondet md]
  | .Assign targets value =>
      -- Check if any target is a Field — these should have been lowered already
      let hasField := targets.any fun t => match t.val with | .Field _ _ => true | _ => false
      if hasField then
        throwStmtDiagnostic $ md.toDiagnostic "Field targets in assignment should have been lowered by heap parameterization" DiagnosticType.StrataBug
      else
      -- Dispatch over targets, calling onDeclare/onLocal per target type.
      let dispatchTargets
          (onDeclare : Core.CoreIdent → LTy → TranslateM (List Core.Statement))
          (onLocal : Core.CoreIdent → TranslateM (List Core.Statement))
          : TranslateM (List Core.Statement) := do
        let mut result : List Core.Statement := []
        for target in targets do
          match target.val with
          | .Declare param =>
            let coreType := LTy.forAll [] (← translateType param.type)
            let ident : Core.CoreIdent := ⟨param.name.text, ()⟩
            result := result ++ (← onDeclare ident coreType)
          | .Local name =>
            let ident : Core.CoreIdent := ⟨name.text, ()⟩
            result := result ++ (← onLocal ident)
          | .Field _ _ => pure () -- already handled above
        return result
      -- Partition targets into init-nondet statements and CoreIdent list (for procedure calls).
      let initTargetsNondet : TranslateM (List Core.Statement × List Core.CoreIdent) := do
        let mut inits : List Core.Statement := []
        let mut lhs : List Core.CoreIdent := []
        for target in targets do
          match target.val with
          | .Declare param =>
            let coreType := LTy.forAll [] (← translateType param.type)
            let ident : Core.CoreIdent := ⟨param.name.text, ()⟩
            inits := inits ++ [Core.Statement.init ident coreType .nondet md]
            lhs := lhs ++ [ident]
          | .Local name =>
            let ident : Core.CoreIdent := ⟨name.text, ()⟩
            lhs := lhs ++ [ident]
          | .Field _ _ => pure () -- already handled above
        return (inits, lhs)
      -- Translate a procedure/instance call: init Declare targets with nondet, then emit call.
      let translateCallTargets (calleeId : Identifier) (args : List StmtExprMd) : TranslateM (List Core.Statement) := do
        let coreArgs ← args.mapM (fun a => translateExpr a)
        let (inits, lhs) ← initTargetsNondet
        let (callArgs, _, calleeInoutNames) ← buildCallArgs calleeId coreArgs md
        let outArgs : List (Core.CallArg Core.Expression) :=
          lhs.filter (fun id => !calleeInoutNames.contains id.name) |>.map .outArg
        return inits ++ [Core.Statement.call calleeId.text (callArgs ++ outArgs) md]
      -- Match on the value to decide how to translate
      match _hv : value.val with
      | .StaticCall callee args =>
        if model.isFunction callee then
          -- Function call: translate as a normal expression assignment
          let coreExpr ← translateExpr value
          match targets with
          | [_target] =>
            let result ← dispatchTargets
              (onDeclare := fun ident coreType => pure [Core.Statement.init ident coreType (.det coreExpr) md])
              (onLocal := fun ident => pure [Core.Statement.set ident coreExpr md])
            return result
          | _ =>
            throwStmtDiagnostic $ md.toDiagnostic "function call without a single target" DiagnosticType.StrataBug
        else
          translateCallTargets callee args
      | .InstanceCall _target callee args =>
          translateCallTargets callee args
      | .Hole _ _ =>
          -- Hole RHS: havoc all targets (unmodeled call side-effect).
          dispatchTargets
            (onDeclare := fun ident coreType => pure [Core.Statement.init ident coreType .nondet md])
            (onLocal := fun ident => pure [Core.Statement.havoc ident md])
      | _ =>
        match targets with
        | [_target] =>
          let coreExpr ← translateExpr value
          dispatchTargets
            (onDeclare := fun ident coreType => pure [Core.Statement.init ident coreType (.det coreExpr) md])
            (onLocal := fun ident => pure [Core.Statement.set ident coreExpr md])
        | _ =>
          throwStmtDiagnostic $ md.toDiagnostic "Multi-target assignment need a call as a RHS" DiagnosticType.StrataBug
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
        let (callArgs, calleeOutputs, calleeInoutNames) ← buildCallArgs callee coreArgs md
        -- Generate throwaway LHS for output-only params so Core arity checking passes.
        let mut inits : List Core.Statement := []
        let mut outArgs : List (Core.CallArg Core.Expression) := []
        for out in calleeOutputs do
          if calleeInoutNames.contains out.name.text then continue
          let id ← freshId
          let ident : Core.CoreIdent := ⟨s!"$unused_{id}", ()⟩
          let coreType := LTy.forAll [] (← translateType out.type)
          inits := inits ++ [Core.Statement.init ident coreType .nondet md]
          outArgs := outArgs ++ [.outArg ident]
        return inits ++ [Core.Statement.call callee.text (callArgs ++ outArgs) md]
  | .InstanceCall .. =>
      -- Instance method call as statement: no return value, treated as no-op
      return ([])
  | .Return valueOpt =>
      match valueOpt with
      | none =>
          return [.exit bodyLabel md]
      | some _ =>
          let d := md.toDiagnostic "Return statement with value should have been eliminated by EliminateValueReturns pass" DiagnosticType.StrataBug
          emitCoreDiagnostic d
          return [.exit bodyLabel md]
  | .While cond invariants decreasesExpr body postTest =>
      if postTest then
        return ← throwStmtDiagnostic (diagnosticFromSource cond.source
          "post-test while (do-while) should have been eliminated by EliminateDoWhile pass" DiagnosticType.StrataBug)
      let condExpr ← translateExpr cond
      let invExprs ← invariants.mapM (fun i => do return ("", ← translateExpr i))
      let decreasingExprCore ← decreasesExpr.mapM (translateExpr)
      let bodyStmts ← translateStmt body
      -- Attach each invariant's source provenance to the loop metadata, in
      -- invariant order, so loop elimination can point an invariant's
      -- verification condition at the specific invariant rather than the whole
      -- loop. (The Core loop IR stores invariants as `(label, expr)` pairs with
      -- no per-invariant metadata slot, and Core expressions carry no source
      -- range, so we thread the ranges through the loop metadata instead.)
      let mdWithInvs := invariants.foldl
        (fun acc i => acc.pushInvariantProvenance (fileRangeToProvenance i.source)) md
      return [Imperative.Stmt.loop (.det condExpr) decreasingExprCore invExprs bodyStmts mdWithInvs]
  | .Exit target =>
      return [Imperative.Stmt.exit target md]
  | .Hole _ _ =>
      -- Hole in statement position: treat as havoc (no-op).
      -- This can occur when an unmodeled call's Block is flattened.
      return []
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
private def translateChecks (checks : List Condition) (labelBase : String) (overrideFree: Bool)
    (defaultSummary : Option String := none)
    : TranslateM (ListMap Core.CoreLabel Core.Procedure.Check) :=
  checks.mapIdxM (fun i check => do
    let label := if checks.length == 1 then labelBase else s!"{labelBase}_{i}"
    let checkExpr ← translateExpr check.condition [] (isPureContext := true)
    let baseMd := astNodeToCoreMd check.condition
    let md := match check.summary.orElse (fun _ => defaultSummary) with
      | some msg => baseMd.pushElem Imperative.MetaData.propertySummary (.msg msg)
      | none => baseMd
    let attr := if check.free || overrideFree then Core.Procedure.CheckAttr.Free else .Default
    let c : Core.Procedure.Check := { expr := checkExpr, attr, md }
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
  -- Track inout parameter names for the `.Old (Var (Local n))` defensive check.
  -- Reset to [] after the procedure so siblings start fresh.
  modify fun s => { s with currentProcInouts := procInoutNames proc }
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
  let preconditions ← translateChecks proc.preconditions "requires" false

  let bodyStmts : Option (List Core.Statement) ←
    match proc.body with
    | .Transparent bodyExpr =>
      let r ← translateStmt bodyExpr
      pure $ some r
    | .Opaque _postconds (some impl) _ =>
      let r ← translateStmt impl
      pure $ some r
    | _ =>
      pure none

  -- Translate postconditions for Opaque and Abstract bodies. A bodiless
  -- procedure (bodyStmts = none) gets its postconditions marked `free`
  -- (overrideFree) so they are assumed, not checked — and an empty body.
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds =>
        translateChecks postconds s!"postcondition" bodyStmts.isNone
          (defaultSummary := "postcondition")
    | _ => pure []
  -- Wrap body in a labeled block so early returns (exit) work correctly.
  -- `bodyLabel` is the shared "$body" constant the resolver pre-registers.
  let body : List Core.Statement := [.block bodyLabel (bodyStmts.getD []) mdWithUnknownLoc]
  let spec : Core.Procedure.Spec := { preconditions, postconditions }
  return { header, spec, body := .structured body }

structure LaurelVerifyOptions where
  translateOptions : LaurelTranslateOptions := {}
  verifyOptions : Core.VerifyOptions := .default

instance : Inhabited LaurelVerifyOptions where
  default := {}

/-- Unwrap the pattern produced by EliminateValuesInReturns + EliminateReturnStatements:
    `{ result := <expr>; exit "$return" } $return` → `<expr>` -/
private def unwrapReturnBlock (b : StmtExprMd) : StmtExprMd :=
  match b.val with
  | .Block [⟨.Assign [⟨.Local _, _⟩] value, _⟩, ⟨.Exit "$return", _⟩] (some "$return") => value
  | _ => b

/--
Translate a Laurel Procedure to a Core Function (when applicable) using `TranslateM`.
Diagnostics for disallowed constructs in the function body are emitted into the monad state.
-/
def translateProcedureToFunction (options: LaurelTranslateOptions) (isRecursive: Bool) (proc : Procedure) : TranslateM Core.Decl := do
  -- Functions are pure: no inout parameters, so the `.Old` defensive check
  -- will reject any old(...) reference (which is the correct behavior here).
  modify fun s => { s with currentProcInouts := [] }
  let inputs ← proc.inputs.mapM translateParameterToCore
  let outputTy ← match proc.outputs.head? with
    | some p => translateType p.type
    | none => pure LMonoTy.int
  -- Translate precondition to FuncPrecondition (skip trivial `true`)
  let preconditions ← proc.preconditions.mapM (fun precondition => do
    let checkExpr ← translateExpr precondition.condition [] true
    return { expr := checkExpr, md := () })

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
    | .Transparent bodyExpr =>
      some <$> translateExpr (unwrapReturnBlock bodyExpr) [] (isPureContext := true)
    | .Opaque _ (some bodyExpr) _ =>
      emitDiagnostic (diagnosticFromSource proc.name.source "functions with postconditions are not yet supported")
      some <$> translateExpr (unwrapReturnBlock bodyExpr) [] (isPureContext := true)
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
  return .func f (identifierToCoreMd proc.name)

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
Translate a `CoreWithLaurelTypes` program to a `Core.Program`.
-/
def translateLaurelToCore (options: LaurelTranslateOptions) (ordered : CoreWithLaurelTypes): TranslateM Core.Program := do

  let coreDecls ← ordered.decls.flatMapM fun
    | .funcs funcs isRecursive => do
      let nonExternal := funcs.filter (fun p => !p.body.isExternal)
      let coreFuncs ← nonExternal.mapM (translateProcedureToFunction options isRecursive)
      if isRecursive then
        let coreFuncValues := coreFuncs.filterMap (fun d => match d with
          | .func f _ => some f
          | _ => none)
        return [Core.Decl.recFuncBlock coreFuncValues mdWithUnknownLoc]
      else
        return coreFuncs
    | .procedure proc => do
      let procDecl ← translateProcedure proc
      -- Translate axioms (populated by the contract pass from invokeOn + ensures)
      let axiomDecls ← proc.axioms.mapM fun ax => do
        let coreExpr ← translateExpr ax [] (isPureContext := true)
        return Core.Decl.ax { name := s!"invokeOn_{proc.name.text}", e := coreExpr } (identifierToCoreMd proc.name)
      return [Core.Decl.proc procDecl (identifierToCoreMd proc.name)] ++ axiomDecls
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

  pure { decls := coreDecls }

public def laurelToCoreSchemaPass : LaurelPass CoreWithLaurelTypes Core.Program where
  name := "LaurelToCoreSchemaPass"
  comesBefore := []
  documentation := "Produce a `Core` program from a `CoreWithLaurelTypes` program. Intended to be dumb 1-to-1 translation. However, there are several smart translations still happening:
  - The @[cases] parameter is inferred for recursive functions.
  - Laurel parameter definitions are translated to Core ones.
  - Laurel calling conventions are translated to Core ones."
  run := fun p fnModel options =>
    let initState : TranslateState := { model := fnModel, overflowChecks := options.overflowChecks }
    let (coreProgramOption, translateState) :=
      runTranslateM initState (translateLaurelToCore options p)
    let diagnostics : List DiagnosticModel :=
      -- Because of the duplication between functions and procedures, this translation is liable to create duplicate diagnostics
      let d := translateState.diagnostics.eraseDups
      if d.isEmpty then translateState.coreDiagnostics else d
    (coreProgramOption.getD default, diagnostics, {})

end -- public section
end Laurel
