/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Options
public import Strata.Languages.Laurel.PushOldInward
public import Strata.Languages.Laurel.CoreGroupingAndOrdering
public import Strata.Languages.Laurel.EliminateReturnStatements
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
-- Signed bitvector comparisons, generated per width by `Factory.lean`'s
-- `DefBVOpFuncExprs [1, 8, 16, 32, 64]`.
open Core (bv1SLtOp bv1SLeOp bv1SGtOp bv1SGeOp)
open Core (bv8SLtOp bv8SLeOp bv8SGtOp bv8SGeOp)
open Core (bv16SLtOp bv16SLeOp bv16SGtOp bv16SGeOp)
open Core (bv32SLtOp bv32SLeOp bv32SGtOp bv32SGeOp)
open Core (bv64SLtOp bv64SLeOp bv64SGtOp bv64SGeOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

public section

private def mdWithUnknownLoc : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofProvenance (.synthesized .laurelToCore)

/-- Set of names that are translated to Core functions (not procedures) -/
@[expose] abbrev FunctionNames := List Identifier

/-- State threaded through expression and statement translation -/
structure TranslateState where
  /-- Diagnostics accumulated during translation -/
  diagnostics : List Message := []
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Constants known to the program (field constants, etc.) -/
  model : SemanticModel
  /-- Type names treated as gradual/dynamic-top (from options.gradualTypes). A `.UserDefined`
      whose name is here maps to Core `Any` instead of hard-erroring, matching the `.Unknown` arm. -/
  gradualTypes : Std.HashSet String := {}
  /-- Overflow check configuration -/
  overflowChecks : Core.OverflowChecks := {}
  /-- Do not process the produces Core program, since it has superfluous errors -/
  coreProgramHasSuperfluousErrors: Bool := false
  /-- Inout parameter names of the procedure currently being translated.
      Used by the `.Old (Var (Local n))` arm to defensively check `n` against
      the procedure's inout list. Empty when not translating a procedure body. -/
  currentProcInouts : List String := []
  /-- Type-parameter names in scope while translating a generic datatype's
      constructor argument types (e.g. `Val`/`Err` of `Result<Val, Err>`). A
      `UserDefined` name matching one of these lowers to a Core free type
      variable rather than a nullary type constructor. -/
  typeParams : List String := []
  /-- Diagnostics that indicate the Core program should not be processed further.
      When non-empty, the produced Core program is suppressed. Each entry records
      why the program was deemed invalid so that if no other diagnostics explain
      the suppression, these can be surfaced to the user. -/
  coreDiagnostics : List Message := []
  /-- Names of the program's (non-functional) procedures. A `StaticCall` whose
      callee is in this set is a procedure call; anything else (Core functions,
      the `$asFunction` twins produced by TransparencyPass, constants, etc.) is a
      pure function application. This is name-based on purpose: TransparencyPass
      redirects a call to `foo` into `foo$asFunction` while preserving the
      callee's `uniqueId`, so an id-based `model.isFunction` check would still
      resolve to the (now non-functional) base procedure and wrongly reject it. -/
  procedureNames : Std.HashSet String := {}

/-- The translation monad: state with string-error abort for internal failures. -/
@[expose] abbrev TranslateM := ExceptT String (StateM TranslateState)

def isFieldName (fieldNames : List Identifier) (name : Identifier) : TranslateM Bool :=
  fieldNames.anyM (fun f => liftM (m := Except String) (name.sameId f))

/-- Whether `name` refers to one of the program's procedures (as opposed to a
    pure function application). See `TranslateState.procedureNames`. -/
def containsProcedure (name : Identifier) : TranslateM Bool := do
  return (← get).procedureNames.contains name.text

/-- Emit a diagnostic into the translation state (soft warning, does not abort) -/
def emitDiagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [d] }

/-- Emit a core diagnostic that flags the Core program as invalid. -/
def emitCoreDiagnostic (d : Message) : TranslateM Unit :=
  modify fun s => { s with coreDiagnostics := s.coreDiagnostics ++ [d] }

private def invalidCoreType (source : FileRange) (reason : String) : TranslateM LMonoTy := do
  emitCoreDiagnostic (diagnosticFromSource source reason MessageKind.strataBug)
  return .tcons s!"LaurelResolutionErrorPlaceholder" []

/-- Allocate a fresh unique ID. -/
private def freshId : TranslateM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Allocate a fresh Core type variable. Used to fill in a datatype reference's
    (erased) type arguments so the emitted `tcons` matches the arity Core
    registered for that datatype; Core unification binds it to the real arg. -/
private def freshTVar : TranslateM LMonoTy := do
  return .ftvar s!"_t{← freshId}"

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighTypeMd) : TranslateM LMonoTy := do
  let model := (← get).model
  match ty with
  | AstNode.mk val _ =>
  match val with
  | .TInt => return LMonoTy.int
  | .TBool => return LMonoTy.bool
  | .TString => return LMonoTy.string
  | .TBv n => return LMonoTy.bitvec n
  | .TVoid => return LMonoTy.bool -- Using bool as placeholder for void
  | .TSet elementType => return Core.mapTy (← translateType elementType) LMonoTy.bool
  | .TMap keyType valueType => return Core.mapTy (← translateType keyType) (← translateType valueType)
  | .UserDefined name =>
    -- A `UserDefined` whose name is a primitive keyword lowers to that primitive
    -- (phantom `UserDefined "real"` etc. from name round-trips / stub types).
    if name.text == "real" then return LMonoTy.real
    else if name.text == "int" then return LMonoTy.int
    else if name.text == "bool" then return LMonoTy.bool
    else if name.text == "string" then return LMonoTy.string
    -- Check type parameters next (matching how resolution scopes them): a
    -- datatype's own type parameter (e.g. `Val`/`Err` of `Result<Val, Err>`)
    -- lowers to a Core free type variable. Checking `model.get?` first would
    -- mis-lower a parameter whose name collides with an in-scope type.
    else if (← get).typeParams.contains name.text then
      return .ftvar name.text
    else match model.get? name with
      -- A bare datatype reference (e.g. a constructor's erased result type,
      -- `Nothing() : Option`) must still carry one Core type argument per declared
      -- parameter, or Core's arity check rejects the `tcons`. Emit fresh type
      -- variables; Core unification binds them to the real argument types.
      | some (.datatypeDefinition dt) =>
        let args ← dt.typeArgs.mapM (fun _ => freshTVar)
        return .tcons dt.name.text args
      | some (.datatypeConstructor typeName _) =>
        let args ← match model.get? typeName with
          | some (.datatypeDefinition dt) => dt.typeArgs.mapM (fun _ => freshTVar)
          | _ => pure []
        return .tcons typeName.text args
      | _ => do
        -- A name registered gradual (e.g. a type imported from an unmodeled module like
        -- `botocore.model.OperationModel`) is dynamic-top: map it to Core `Any`, exactly as the
        -- `.Unknown` arm does, rather than hard-erroring. Otherwise resolution should already have
        -- emitted a diagnostic, so surface the unresolved-composite error.
        if (← get).gradualTypes.contains name.text then
          return .tcons "Any" []
        emitCoreDiagnostic (diagnosticFromSource ty.source s!"UserDefined type {name} could not be resolved to a composite or datatype" MessageKind.strataBug)
        return .tcons name.text []
  -- Generic type application, e.g. `Option<int>` → `.tcons "Option" [int]`.
  -- Core has real polymorphic datatypes, so the type arguments are forwarded.
  -- Produced by user-written generic type application (the grammar `appliedType`
  -- op) — see StrataTest/Languages/Laurel/EndToEndTests/Verification/Objects/GenericDatatype.lean.
  | .Applied base args =>
    match base.val with
    | .UserDefined n =>
      -- A type *parameter* cannot itself be applied to arguments (`C<int>` where
      -- `C` is a parameter): guard it like the plain `.UserDefined` arm so the
      -- invalid program is suppressed via a diagnostic rather than leaking a
      -- bogus `tcons`.
      if (← get).typeParams.contains n.text then
        invalidCoreType ty.source s!"type parameter '{n.text}' cannot be applied to type arguments"
      else
        let coreArgs ← args.mapM translateType
        return .tcons n.text coreArgs
    | _ => invalidCoreType ty.source "generic type application with a non-named base is not supported"
  | .TReal => return LMonoTy.real
  | .TFloat64 =>
    -- `float64` aliases to Core `real` ONLY in gradual mode (a frontend registered gradualTypes,
    -- e.g. Python): Core has no distinct IEEE-754 float64 sort, so a translated Python `float` is
    -- verified with real (arbitrary-precision) semantics — sound enough for the gradual frontend
    -- (float overflow is not modeled). In native Laurel (no gradualTypes) keep the clean
    -- unsupported-type error rather than aliasing to real and failing deep in Core with a cryptic
    -- unify error; revisit if Core gains a float64 sort with float-specific overflow checks.
    if (← get).gradualTypes.isEmpty then
      invalidCoreType ty.source "float64 not supported in native mode (no distinct Core float64 sort)"
    else
      return LMonoTy.real
  | .MultiValuedExpr _ => invalidCoreType ty.source "MultiValuedExpr type encountered during Core translation"
  | .Unknown =>
    -- `.Unknown` is a gradual hole: map it to Core `Any` ONLY when a frontend has registered
    -- gradual types (gradual mode). In native Laurel (no gradualTypes) `Any` is not a Core-native
    -- type, so keep the old hard error rather than emit a dangling `tcons "Any"`.
    if (← get).gradualTypes.isEmpty then
      invalidCoreType ty.source "cannot translate Unknown type to Core"
    else
      return .tcons "Any" []
  | _ => do
    invalidCoreType ty.source s!"cannot translate type to Core: not supported yet"

def lookupType (name : Identifier) : TranslateM LMonoTy := do
  translateType ((← get).model.get name).getType

/-- Compute the Core value type `V` of a `mapConst` argument, i.e. the type of
    `arg`. Nested `mapConst` calls have the `Box` placeholder as their declared
    return type, so `computeExprType` cannot recover their structural `Map` type;
    we reconstruct it here (`mapConst(x) : Map TypeTag (typeof x)`). -/
private partial def mapConstValTy (model : SemanticModel) (arg : StmtExprMd) : TranslateM LMonoTy := do
  match arg.val with
  | .StaticCall callee [inner] =>
      if callee.text == "mapConst" then
        return Core.mapTy (.tcons "TypeTag" []) (← mapConstValTy model inner)
      else translateType (computeExprType model arg)
  | _ => translateType (computeExprType model arg)

/-- Run a `TranslateM` action, returning either a hard error or the result and final state -/
def runTranslateM (s : TranslateState) (m : TranslateM α) : (Except String α × TranslateState) :=
  m.run s

/-- Emit a diagnostic and continue with a default expression (does not abort). -/
def emitExprDiagnostic (d : Message): TranslateM Core.Expression.Expr := do
  emitDiagnostic d
  emitCoreDiagnostic d
  return default

/-- The bitvector widths for which Core defines its bitvector operators
    (`Factory.lean`'s `DefBVOpFuncExprs [1, 8, 16, 32, 64]`). The comparison
    wrappers in `CoreDefinitionsForLaurel` are declared for exactly these
    widths, so the two lists must agree. -/
private def bvOperatorWidths : List Nat := [1, 8, 16, 32, 64]

/-- Signed bitvector comparisons, as `(externalProcSuffix, Core op)` pairs
    parameterized by width. Signed to match the pre-`StaticCall` lowering, which
    sent bitvector comparisons through the *integer* operators. -/
private def bvComparisonOp (width : Nat) (suffix : String) : Option Core.Expression.Expr :=
  match width, suffix with
  | 1, "SLt" => some bv1SLtOp   | 1, "SLe" => some bv1SLeOp
  | 1, "SGt" => some bv1SGtOp   | 1, "SGe" => some bv1SGeOp
  | 8, "SLt" => some bv8SLtOp   | 8, "SLe" => some bv8SLeOp
  | 8, "SGt" => some bv8SGtOp   | 8, "SGe" => some bv8SGeOp
  | 16, "SLt" => some bv16SLtOp | 16, "SLe" => some bv16SLeOp
  | 16, "SGt" => some bv16SGtOp | 16, "SGe" => some bv16SGeOp
  | 32, "SLt" => some bv32SLtOp | 32, "SLe" => some bv32SLeOp
  | 32, "SGt" => some bv32SGtOp | 32, "SGe" => some bv32SGeOp
  | 64, "SLt" => some bv64SLtOp | 64, "SLe" => some bv64SLeOp
  | 64, "SGt" => some bv64SGtOp | 64, "SGe" => some bv64SGeOp
  | _, _ => none

/-- Decode a bitvector comparison external's name (`bv32SLt`) into its Core
    operator, or `none` if `name` is not one.

    Widths are tried until one decodes rather than until one merely prefix-matches:
    `"1"` is a prefix of `"16SLt"`, so stopping at the first prefix match would
    reject every 16-bit name. -/
private def bvOperatorNamed (name : String) : Option Core.Expression.Expr := do
  guard (name.startsWith "bv")
  let rest := name.drop 2 |>.toString
  bvOperatorWidths.findSome? fun w =>
    let digits := toString w
    if rest.startsWith digits then
      bvComparisonOp w (rest.drop digits.length |>.toString)
    else none

/-- Strip the reserved `$` prefix from a prelude procedure name, or fail if it is
    absent.

    Every procedure `CoreDefinitionsForLaurel` declares lives in Laurel's reserved
    namespace, so that a user program declaring its own `intAdd`, `eq` or `select`
    does not collide with the prelude (the prelude is prepended to every program,
    and mixing a user procedure with an `external` overload of the same name is
    rejected outright). The matching below is written against the bare names, so
    the prefix is stripped once here rather than spelled into every arm.

    The prefix is *required*, not merely tolerated: an unprefixed `intAdd` is a
    user-declared procedure that happens to share a built-in's bare name, and
    lowering it to the Core operator would discard the user's body silently. So a
    name without the prefix is not an operator name at all. -/
private def dropReservedPrefix (name : String) : Option String :=
  if name.startsWith "$" then some (name.drop 1 |>.toString) else none

/-- Names of built-in operator procedures that `translateExpr` handles specially.
    Only `$`-prefixed names qualify — see `dropReservedPrefix`. -/
private def isOperatorProcName (name : String) : Bool :=
  match dropReservedPrefix name with
  | none => false
  | some name =>
  (bvOperatorNamed name).isSome ||
  name == "boolNot" || name == "intNeg" || name == "realNeg" ||
  -- `$eq`/`$neq` are external (polymorphic equality has no monomorphic Laurel
  -- signature), so unlike the other operators they reach here under their
  -- wrapper names as well as the underlying `$eq`/`$neq` delegates — which,
  -- after stripping the prefix, is the same spelling either way.
  name == "eq" || name == "neq" ||
  name == "andThen" || name == "orElse" ||
  name == "boolAnd" || name == "boolOr" || name == "boolImplies" ||
  name == "intAdd" || name == "intSub" || name == "intMul" ||
  name == "intDiv" || name == "intSafeDiv" ||
  name == "intMod" || name == "intSafeMod" ||
  name == "intDivT" || name == "intSafeDivT" ||
  name == "intModT" || name == "intSafeModT" ||
  name == "intLt" || name == "intLe" || name == "intGt" || name == "intGe" ||
  name == "realAdd" || name == "realSub" || name == "realMul" || name == "realDiv" ||
  name == "realLt" || name == "realLe" || name == "realGt" || name == "realGe" ||
  name == "strConcat"

/-- Map a binary operator procedure name to its Core operator expression.
    Only reached for `$`-prefixed names — see `dropReservedPrefix`. -/
private def binaryOperatorOp (name : String) : Core.Expression.Expr :=
  let name := (dropReservedPrefix name).getD name
  match bvOperatorNamed name with
  | some op => op
  | none =>
  match name with
  | "boolAnd" => boolAndOp
  | "boolOr" => boolOrOp
  | "boolImplies" => boolImpliesOp
  | "intAdd" => intAddOp
  | "intSub" => intSubOp
  | "intMul" => intMulOp
  | "intDiv" => intDivOp
  | "intSafeDiv" => intSafeDivOp
  | "intMod" => intModOp
  | "intSafeMod" => intSafeModOp
  | "intDivT" => intDivTOp
  | "intSafeDivT" => intSafeDivTOp
  | "intModT" => intModTOp
  | "intSafeModT" => intSafeModTOp
  | "intLt" => intLtOp
  | "intLe" => intLeOp
  | "intGt" => intGtOp
  | "intGe" => intGeOp
  | "realAdd" => realAddOp
  | "realSub" => realSubOp
  | "realMul" => realMulOp
  | "realDiv" => realDivOp
  | "realLt" => realLtOp
  | "realLe" => realLeOp
  | "realGt" => realGtOp
  | "realGe" => realGeOp
  | "strConcat" => strConcatOp
  | _ => panic! s!"binaryOperatorOp: unexpected operator name '{name}'"

/--
Translate Laurel StmtExpr to Core Expression using the `TranslateM` monad.
Diagnostics for disallowed constructs are emitted into the monad state.

`isPureContext` should be `true` when translating function bodies or contract expressions.
In that case, disallowed constructs emit `Message` errors into the state.
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

  let disallowed (source : FileRange) (msg : String) : TranslateM Core.Expression.Expr := do
      emitExprDiagnostic $ diagnosticFromSource source msg

  match h: expr.val with
  | .LiteralBool b => return .const () (.boolConst b)
  | .LiteralInt i => return .const () (.intConst i)
  | .LiteralString s => return .const () (.strConst s)
  | .LiteralDecimal d => return .const () (.realConst (StrataDDM.Decimal.toRat d))
  | .LiteralBv value width => return .const () (.bitvecConst width (BitVec.ofNat width value))
  | .Var (.Local name) =>
      -- First check if this name is bound by an enclosing quantifier
      let mut bvarIdx : Option Nat := none
      for bv in boundVars, idx in List.range boundVars.length do
        if ← liftM (m := Except String) (name.sameId bv) then
          bvarIdx := some idx
          break
      match bvarIdx with
      | some idx => return .bvar () idx
      | none =>
        match model.get name with
        | .field _ f => return .op () ⟨f.name.text, ()⟩ none
        | astNode => return .fvar () ⟨name.text, ()⟩ (some (← translateType astNode.getType))
  | .Var (.Declare _) =>
      emitExprDiagnostic $ md.toDiagnostic "variable declaration in expression context should have been lowered" MessageKind.strataBug
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond boundVars isPureContext
      let bthen ← translateExpr thenBranch boundVars isPureContext
      let belse ← match elseBranch with
        | none =>
            emitExprDiagnostic $ diagnosticFromSource expr.source s!"if-then without else expression" MessageKind.notYetImplemented
        | some e =>
            have : sizeOf e < sizeOf expr := by
              have := AstNode.sizeOf_val_lt expr
              cases expr; simp_all; omega
            translateExpr e boundVars isPureContext
      return .ite () bcond bthen belse
  | .StaticCall callee args =>
      if isOperatorProcName callee.text then
        -- Match on the bare name: every prelude procedure carries the reserved `$`
        -- prefix, and `$eq`/`$neq` additionally reach here under their wrapper
        -- names, which strip to the same spelling.
        match _h: (dropReservedPrefix callee.text).getD callee.text, args with
        | "boolNot", [e] =>
          have h_e : sizeOf e < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re ← translateExpr e boundVars isPureContext
          return .app () boolNotOp re
        | "intNeg", [e] =>
          have h_e : sizeOf e < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re ← translateExpr e boundVars isPureContext
          return .app () intNegOp re
        | "realNeg", [e] =>
          have h_e : sizeOf e < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re ← translateExpr e boundVars isPureContext
          return .app () realNegOp re
        | "eq", [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return .eq () re1 re2
        | "neq", [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return .app () boolNotOp (.eq () re1 re2)
        | "andThen", [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return .ite () re1 re2 (.boolConst () false)
        | "orElse", [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return .ite () re1 (.boolConst () true) re2
        -- `==>` short-circuits: its right operand must not be evaluated when the
        -- left one is `false`, or a guarded partial destructor such as
        -- `isfrom_int(v) ==> as_int!(v) != 0` would get stuck on a wrong-variant
        -- value. Lower to an `ite` rather than the strict `boolImpliesOp`.
        | "boolImplies", [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return .ite () re1 re2 (.boolConst () true)
        | _, [e1, e2] =>
          have h_e1 : sizeOf e1 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          have h_e2 : sizeOf e2 < sizeOf expr := by
            have := AstNode.sizeOf_val_lt expr; cases expr; simp_all; omega
          let re1 ← translateExpr e1 boundVars isPureContext
          let re2 ← translateExpr e2 boundVars isPureContext
          return LExpr.mkApp () (binaryOperatorOp callee.text) [re1, re2]
        | _, _ =>
          emitExprDiagnostic $ diagnosticFromSource expr.source
            s!"operator procedure '{callee.text}' called with wrong number of arguments" .userError
      else
      -- In a pure context, only Core functions (not procedures) are allowed
      if isPureContext && (← containsProcedure callee) then
        disallowed expr.source s!"calls to procedures are not supported in functions or contracts"
      else
        -- The `mapConst` constant-map builtin has no inferable key type, so we
        -- annotate its op with the concrete function type `V → Map K V` (from
        -- the resolved result type). This lets the pretty-printer emit the
        -- explicit `mapConst<K>(v)` syntax so the program round-trips.
        let fnOp : Core.Expression.Expr ←
          if callee.text == "mapConst" then
            -- `mapConst : V → Map TypeTag V`. Key type is always `TypeTag`
            -- (the type-tag domain of the ancestor tables); the value type is
            -- the type of the single argument.
            match args with
            | [valArg] =>
                let vTy ← mapConstValTy model valArg
                let kTy : LMonoTy := .tcons "TypeTag" []
                pure (.op () ⟨callee.text, ()⟩ (some (LMonoTy.mkArrow vTy [Core.mapTy kTy vTy])))
            | _ => pure (.op () ⟨callee.text, ()⟩ none)
          else pure (.op () ⟨callee.text, ()⟩ none)
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
      emitExprDiagnostic $ diagnosticFromSource expr.source
        "IncrDecr should have been eliminated by EliminateIncrDecrAndCompoundAssign pass" MessageKind.strataBug
  | .CompoundAssign _ _ _ =>
      emitExprDiagnostic $ diagnosticFromSource expr.source
        "CompoundAssign should have been eliminated by EliminateIncrDecrAndCompoundAssign pass" MessageKind.strataBug
  | .While _ _ _ _ _ =>
      disallowed expr.source "loops are not supported in transparent bodies or contracts"
  | .Exit _ => disallowed expr.source "exit is not supported in expression position"

  | .Block (⟨ .Assert .., innerSrc⟩ :: rest) label => do
    _ ← disallowed innerSrc "asserts are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .Assume _, innerSrc⟩ :: rest) label =>
    _ ← disallowed innerSrc "assumes are not YET supported in functions or contracts"
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .Assign [⟨ .Declare ⟨name, some ty⟩, _source⟩] initializer, innerSrc⟩ :: rest) label => do
      -- These translations are not used yet (see below), but are kept for their
      -- side effect of surfacing any nested diagnostics in the initializer/body.
      let _valueExpr ← translateExpr initializer boundVars isPureContext
      let _bodyExpr ← translateExpr { val := StmtExpr.Block rest label, source := innerSrc } (name :: boundVars) isPureContext
      let _coreMonoType ← translateType ty
      -- Local variables in transparent bodies are lowered away by
      -- `InlineLocalVariablesPass` before this pass runs, so reaching here means
      -- that pass missed one. Once Core supports let expressions we can drop the
      -- inline pass entirely and translate the declaration directly to the
      -- commented-out `.app`/`.abs` below.
      disallowed innerSrc "local variables in transparent bodies should have been eliminated by the InlineLocalVariablesPass"
      -- This doesn't work because of a limitation in Core.
      -- return .app () (.abs () (some _coreMonoType) _bodyExpr) _valueExpr
  | .Block (⟨ .Var (.Declare _), innerSrc⟩ :: rest) label => do
    _ ← disallowed innerSrc "local variables must have initializers in transparent bodies or contracts "
    translateExpr { val := StmtExpr.Block rest label, source := innerSrc } boundVars isPureContext
  | .Block (⟨ .IfThenElse cond thenBranch (some elseBranch), innerSrc⟩ :: rest) label =>
    disallowed innerSrc "if-then-else only supported as the last statement in a block"

  | .Var (.Field target fieldId) =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      emitExprDiagnostic $ diagnosticFromSource expr.source s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldId.text}" MessageKind.strataBug
  | .Block (⟨ .Assign _ _, assignSource⟩ :: tail) _ =>
      disallowed assignSource "destructive assignments are not supported in transparent bodies or contracts"
  | .Block (⟨ .While _ _ _ _ _, whileSource⟩ :: tail) _ =>
      disallowed whileSource "loops are not supported in functions or contracts"
  | .Block (head :: tail) _ =>
      emitExprDiagnostic $ diagnosticFromSource expr.source s!"block expression starting with {head.val.constructorName} should have been lowered in a separate pass" MessageKind.strataBug
  | .Block [] _ =>
      emitExprDiagnostic $ diagnosticFromSource expr.source "empty block expression should have been lowered in a separate pass" MessageKind.strataBug
  | .Return _ => emitExprDiagnostic $ diagnosticFromSource expr.source "return statement-expression should be lowered in a separate pass" MessageKind.strataBug
  | .IsType _ _ =>
      emitExprDiagnostic $ diagnosticFromSource expr.source "IsType should have been lowered" MessageKind.strataBug
  | .New _ => emitExprDiagnostic $ diagnosticFromSource expr.source s!"New should have been eliminated by typeHierarchyTransform" MessageKind.strataBug
  | .AsType target _ => emitExprDiagnostic $ diagnosticFromSource expr.source "AsType expression translation" MessageKind.notYetImplemented
  | .Assigned _ => emitExprDiagnostic $ diagnosticFromSource expr.source "assigned expression translation" MessageKind.notYetImplemented
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
            emitExprDiagnostic $ diagnosticFromSource expr.source
              s!"old({name.text}) refers to a name that is not an inout parameter \
                 of the enclosing procedure (inouts: {inouts}). This violates the \
                 pushOldInward normalization invariant."
              MessageKind.strataBug
          else
            let coreTy ← translateType (model.get name).getType
            return .fvar () (Core.CoreIdent.mkOld name.text) (some coreTy)
      | _ =>
          emitExprDiagnostic $ diagnosticFromSource expr.source
            "old(...) should have been pushed inward to a variable reference. \
             This violates the pushOldInward normalization invariant."
            MessageKind.strataBug
  | .Fresh _ => emitExprDiagnostic $ diagnosticFromSource expr.source "fresh expression translation" MessageKind.notYetImplemented
  | .Assert .. => emitExprDiagnostic $ diagnosticFromSource expr.source "assert expression translation" MessageKind.notYetImplemented
  | .Assume _ => emitExprDiagnostic $ diagnosticFromSource expr.source "assume expression translation" MessageKind.notYetImplemented
  | .ProveBy value _ => emitExprDiagnostic $ diagnosticFromSource expr.source "proveBy expression translation" MessageKind.notYetImplemented
  | .ContractOf _ _ => emitExprDiagnostic $ diagnosticFromSource expr.source "contractOf expression translation" MessageKind.notYetImplemented
  | .Abstract => emitExprDiagnostic $ diagnosticFromSource expr.source "abstract expression translation" MessageKind.notYetImplemented
  | .All => emitExprDiagnostic $ diagnosticFromSource expr.source "all expression translation" MessageKind.notYetImplemented
  | .InstanceCall target callee args => emitExprDiagnostic $ diagnosticFromSource expr.source "instance call expression translation" MessageKind.notYetImplemented
  | .PureFieldUpdate _ _ _ => emitExprDiagnostic $ diagnosticFromSource expr.source "pure field update expression translation" MessageKind.notYetImplemented
  | .This => emitExprDiagnostic $ diagnosticFromSource expr.source "this expression translation" MessageKind.notYetImplemented
  termination_by expr
  decreasing_by
    all_goals (have := AstNode.sizeOf_val_lt expr; term_by_mem)

/-- Build the parenthesized suffix that names an `assert`/`assume` after its
    source position.

    The result is a display name only — it is not required to be unique, and
    nothing resolves a failure back to source through it. Consumers use the
    statement's `MetaData`, which travels with the failure (see
    `Imperative.EvalError.AssertFail`) and carries both the `FileRange` and the
    property summary. -/
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

def throwStmtDiagnostic (d : Message): TranslateM (List Core.Statement) := do
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
          MessageKind.strataBug
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
  let md := astNodeToCoreMd stmt
  match _h : stmt.val with
  | .Assert cond summary =>
      -- Assert/assume bodies must be pure expressions (no assignments, loops, or procedure calls)
      let coreExpr ← translateExpr cond [] (isPureContext := true)
      let md' := match summary with
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
      -- Post-resolution every declaration is annotated; default to `Unknown`.
      let coreMonoType ← translateType (param.type.getD ⟨.Unknown, stmt.source⟩)
      let coreType := LTy.forAll [] coreMonoType
      let ident := ⟨param.name.text, ()⟩
      return [Core.Statement.init ident coreType .nondet md]
  | .Assign targets value =>
      -- Check if any target is a Field — these should have been lowered already
      let hasField := targets.any fun t => match t.val with | .Field _ _ => true | _ => false
      if hasField then
        throwStmtDiagnostic $ md.toDiagnostic "Field targets in assignment should have been lowered by heap parameterization" MessageKind.strataBug
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
            let coreType := LTy.forAll [] (← translateType (param.type.getD ⟨.Unknown, target.source⟩))
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
            let coreType := LTy.forAll [] (← translateType (param.type.getD ⟨.Unknown, target.source⟩))
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
        if (← containsProcedure callee) then
          translateCallTargets callee args
        else
          -- Function call: translate as a normal expression assignment
          let coreExpr ← translateExpr value
          match targets with
          | [_target] =>
            let result ← dispatchTargets
              (onDeclare := fun ident coreType => pure [Core.Statement.init ident coreType (.det coreExpr) md])
              (onLocal := fun ident => pure [Core.Statement.set ident coreExpr md])
            return result
          | _ =>
            throwStmtDiagnostic $ md.toDiagnostic "function call without a single target" MessageKind.strataBug
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
          throwStmtDiagnostic $ md.toDiagnostic "Multi-target assignment need a call as a RHS" MessageKind.strataBug
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond ← translateExpr cond
      let bthen ← translateStmt thenBranch
      let belse ← match elseBranch with
                  | some e => translateStmt e
                  | none => pure []
      return [Imperative.Stmt.ite (.det bcond) bthen belse md]
  | .StaticCall callee args =>
      -- Check if this is a function or procedure
      if !(← containsProcedure callee) then
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
  | .Return _ =>
      let d := md.toDiagnostic "Return statement should have been eliminated by EliminateReturnStatements pass" MessageKind.strataBug
      emitCoreDiagnostic d
      return default
  | .While cond invariants decreasesExpr body postTest =>
      if postTest then
        return ← throwStmtDiagnostic (diagnosticFromSource cond.source
          "post-test while (do-while) should have been eliminated by EliminateDoWhile pass" MessageKind.strataBug)
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
private def translateChecks (checks : List Condition) (labelBase : String)
    (defaultSummary : Option String := none)
    : TranslateM (ListMap Core.CoreLabel Core.Procedure.Check) :=
  checks.mapIdxM (fun i check => do
    let label := if checks.length == 1 then labelBase else s!"{labelBase}_{i}"
    let checkExpr ← translateExpr check.condition [] (isPureContext := true)
    let baseMd := astNodeToCoreMd check.condition
    let md := match check.summary.orElse (fun _ => defaultSummary) with
      | some msg => baseMd.pushElem Imperative.MetaData.propertySummary (.msg msg)
      | none => baseMd
    -- By the time conditions reach the Core schema pass, the contract pass has
    -- lowered every *checkable* pre/postcondition into explicit body
    -- assert/assume statements and cleared the procedures' condition lists. The
    -- only conditions that survive to here are the *free* (assume-only)
    -- postconditions added by the transparency pass (`r == foo$asFunction(...)`),
    -- which Core simply assumes at call sites. The schema pass therefore only
    -- supports free conditions and always emits `.Free`; a non-free condition
    -- reaching this point is a compiler-invariant violation, not user input.
    if check.mode != ConditionMode.Assume then
      let d := diagnosticFromSource check.condition.source
        s!"internal error: a non-free {labelBase} reached Core translation; the contract pass should have lowered it to an assertion"
        MessageKind.strataBug
      emitDiagnostic d
      emitCoreDiagnostic d
    let c : Core.Procedure.Check := { expr := checkExpr, attr := .Free, md }
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
  let inouts ← liftM (m := Except String) (procInoutNames proc)
  modify fun s => { s with currentProcInouts := inouts }
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

  -- Translate postconditions for Opaque and Abstract bodies. After the contract
  -- pass, the only postconditions still attached to a procedure are the free
  -- (assume-only) ones added by the transparency pass; `translateChecks` rejects
  -- any non-free condition and always emits `.Free`.
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check ←
    match proc.body with
    | .Opaque postconds _ _ | .Abstract postconds =>
        translateChecks postconds s!"postcondition"
          (defaultSummary := "postcondition")
    | _ => pure []
  let body : List Core.Statement :=
    match bodyStmts with
    | some ss => ss
    | none =>
      -- A bodiless procedure (e.g. a generated `$hole`, or any opaque/abstract
      -- declaration) would otherwise produce an empty structured body, which the
      -- Core interpreter rejects when called ("has no body"). Emit a single
      -- `assume true` so the body is non-empty. This is a no-op for both
      -- verification (such a procedure's postconditions are already marked
      -- `free`, so there is nothing to check against the body) and concrete
      -- execution (the outputs stay havoc'd), but it lets the interpreter step
      -- through the call instead of erroring.
      [Core.Statement.assume "assume_true" (.true ()) Imperative.MetaData.empty]
  let spec : Core.Procedure.Spec := { preconditions, postconditions }
  return { header, spec, body := .structured body }

structure LaurelVerifyOptions where
  translateOptions : LaurelTranslateOptions := {}
  verifyOptions : Core.VerifyOptions := .default

instance : Inhabited LaurelVerifyOptions where
  default := {}

/-- Unwrap the pattern produced by EliminateValuesInReturns + EliminateReturnStatements:
    `{ result := <expr>; exit "$return" } $return` → `<expr>`
    Also handles an extra wrapping layer from the contract pass:
    `{ { result := <expr>; exit "$return" } $return } none` → `<expr>`
    Support for transparent multi-out procedures is not yet available.
-/
private def unwrapReturnBlock (b : StmtExprMd) : StmtExprMd :=
  match b.val with
  | .Block [⟨.Assign [⟨.Local _, _⟩] value, _⟩, ⟨.Exit returnLabel, _⟩] (some returnLabel) => value
  | .Block [⟨.Block [⟨.Assign [⟨.Local _, _⟩] value, _⟩, ⟨.Exit returnLabel, _⟩] (some returnLabel), _⟩] _ => value
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
  -- Bring the datatype's type parameters into scope so their occurrences in
  -- constructor argument types lower to Core free type variables (`.ftvar`).
  let savedTypeParams := (← get).typeParams
  modify fun s => { s with typeParams := dt.typeArgs.map (·.text) }
  let constrs ← dt.constructors.mapM fun c => do
    let args ← c.args.mapM fun ⟨ n, ty ⟩ => do
      return (⟨n.text, ()⟩, ← translateType ty)
    return { name := ⟨c.name.text, ()⟩
             args := args
             testerName := s!"{dt.name}..is{c.name}" : Lambda.LConstr Unit }
  modify fun s => { s with typeParams := savedTypeParams }
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

abbrev TranslateResult := (Option Core.Program) × (List Message)

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
      -- Carry the producer's interpret-entry marker into Core metadata so the
      -- interpreter can find the entry without name mangling.
      let procMd := identifierToCoreMd proc.name
      let procMd := if proc.isInterpretEntry
        then procMd.pushElem Imperative.MetaData.interpretEntry (.switch true)
        else procMd
      return [Core.Decl.proc procDecl procMd] ++ axiomDecls
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
  name := "LaurelToCoreSchema"
  comesBefore := []
  documentation := "Produce a `Core` program from a `CoreWithLaurelTypes` program. Intended to be dumb 1-to-1 translation. However, there are several smart translations still happening:
  - The @[cases] parameter is inferred for recursive functions.
  - Laurel parameter definitions are translated to Core ones.
  - Laurel calling conventions are translated to Core ones."
  run := fun options p fnModel =>
    let procedureNames : Std.HashSet String := p.decls.foldl (fun r d => match d with
      | .procedure proc => r.insert proc.name.text
      | _ => r) {}
    let initState : TranslateState :=
      { model := fnModel, overflowChecks := options.overflowChecks, procedureNames, gradualTypes := options.gradualTypes }
    let (coreProgramResult, translateState) :=
      runTranslateM initState (translateLaurelToCore options p)
    let diagnostics : List Message :=
      -- Because of the duplication between functions and procedures, this translation is liable to create duplicate diagnostics
      let d := translateState.diagnostics.eraseDups
      if d.isEmpty then translateState.coreDiagnostics else d
    match coreProgramResult with
    | .ok coreProgram => (coreProgram, diagnostics, {})
    | .error e =>
      let diag := Message.fromString s!"Internal error in LaurelToCoreSchema: {e}" .strataBug
      (default, diagnostics ++ [diag], {})

end -- public section
end Laurel
