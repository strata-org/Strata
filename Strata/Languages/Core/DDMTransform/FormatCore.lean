/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DDMTransform.Grammar
public import Strata.Languages.Core.DDMTransform.FracLit
public import Strata.Languages.Core.Procedure
public import StrataDDM.Util.DecimalRat
public import StrataDDM.Format
import Strata.Languages.Core.Factory
open StrataDDM

public section

/-!
# Core AST → CST Conversion (Core Module)

This module contains the core AST-to-CST conversion functions that do NOT
depend on `Program.lean`. It imports `Procedure.lean` (not `Program.lean`)
so it can be imported by `Program.lean` without creating a circular
dependency.

Functions that depend on `Program.lean` (such as `programToCST`,
`formatProgram`, and the declaration-level converters) live in
`ASTtoCST.lean`.

Metadata is emitted as `@[key, key = value]` annotations, controlled by
`MetadataAnnFilter` (default: `.none` — emit nothing).

Known issues:

- Unsupported constructs (coming soon):
  -- Sub-functions (functions defined inside procedures)

- Misc. formatting issues
  -- Remove extra indentation from the last brace of a block or the `end`
  keyword of a mutual block.
-/

namespace Strata

open Core
open Strata.CoreDDM

---------------------------------------------------------------------
-- Conversion Errors
---------------------------------------------------------------------

/-- Errors that can occur during AST→CST conversion -/
inductive ASTToCSTError (M : Type) where
  | unsupportedConstruct (fn : String) (description : String)
                         (context : String) (metadata : M) :
      ASTToCSTError M
  deriving Repr, Inhabited

namespace ASTToCSTError

def toString {M} [ToString M] : ASTToCSTError M → String
  | unsupportedConstruct fn desc ctx _m =>
    s!"Unsupported construct in {fn}: {desc}\nContext: {ctx}"

instance {M} [ToString M] : ToString (ASTToCSTError M) where
  toString := ASTToCSTError.toString

instance : ToString SourceRange where
  toString sr := (Std.format sr).pretty

end ASTToCSTError

---------------------------------------------------------------------
-- Core AST → CST Conversion
---------------------------------------------------------------------

section ToCST

/-- Constants for consistent naming -/
def unknownTypeVar : String := "$__unknown_type"

/-- Generate quantifier variable names with a `__` prefix to indicate that they
    are generated names. In the future, we will store existing variable names in an extra field of quantifier expressions. -/
def mkQuantVarName (level : Nat) : String := "__q" ++ toString level

---------------------------------------------------------------------
-- MetadataAnn Filter
---------------------------------------------------------------------

/-- Controls which metadata keys are emitted as annotations in formatted output. -/
inductive MetadataAnnFilter where
  | none
  | all
  | only (keys : Std.HashSet String)
  | allExcept (keys : Std.HashSet String)
  deriving Inhabited

namespace MetadataAnnFilter

def checks : MetadataAnnFilter :=
  .only Imperative.MetaData.checkKeys

def properties : MetadataAnnFilter :=
  .only Imperative.MetaData.propertyKeys

def shouldEmit (filter : MetadataAnnFilter) (key : String) : Bool :=
  match filter with
  | .none => false
  | .all => true
  | .only keys => keys.contains key
  | .allExcept keys => !keys.contains key

end MetadataAnnFilter

---------------------------------------------------------------------

structure Scope where
  /-- Track bound variables in this scope -/
  boundVars : Array String := #[]
  /-- Track free variables in this scope -/
  freeVars : Array String := #[]
  deriving Inhabited, Repr

structure ToCSTContext (M : Type) where
  /-- Stack of scopes, with global scope at index 0 -/
  scopes : Array Scope := #[{}]
  /-- Collected errors during conversion -/
  errors : Array (ASTToCSTError M) := #[]
  /-- Filter controlling which metadata keys are emitted as annotations -/
  annFilter : MetadataAnnFilter := .none
  deriving Inhabited

namespace ToCSTContext

def empty {M} : ToCSTContext M := { scopes := #[{}] }

-- Format context for error messages
private def toErrorString {M} (ctx : ToCSTContext M) : String :=
  let lines := ctx.scopes.toList.mapIdx fun i scope =>
    let header := if i = 0 then "Global scope:" else "Scope " ++ toString i ++ ":"
    let bv := if scope.boundVars.isEmpty then ""
              else "\n  boundVars: " ++ toString scope.boundVars.toList
    let fv := if scope.freeVars.isEmpty then ""
              else "\n  freeVars: " ++ toString scope.freeVars.toList
    header ++ bv ++ fv
  String.intercalate "\n" lines

/-- Log an error without throwing -/
def logError {M} [Inhabited M] (ctx : ToCSTContext M)
    (fn : String) (desc : String) (detail : String) : ToCSTContext M :=
  let msg := desc ++ ": " ++ detail
  let err := ASTToCSTError.unsupportedConstruct fn msg
                ctx.toErrorString default
  { ctx with errors := ctx.errors.push err }

/-- Get all bound variables across all scopes -/
def allBoundVars {M} (ctx : ToCSTContext M) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.boundVars) #[]

/-- Find index of bound variable in context -/
def findBoundVarIndex? {M} (ctx : ToCSTContext M) (name : String)
    : Option Nat :=
  ctx.allBoundVars.findIdx? (· == name)

/-- Get all free variables across all scopes -/
def allFreeVars {M} (ctx : ToCSTContext M) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.freeVars) #[]

/-- Find index of free variable across all scopes -/
def freeVarIndex? {M} (ctx : ToCSTContext M) (name : String) : Option Nat :=
  ctx.allFreeVars.findIdx? (· == name)

/-- Add bound variables to the current scope -/
def addScopedBoundVars {M} (ctx : ToCSTContext M) (names : Array String)
    (reverse? : Bool := true) : ToCSTContext M :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let names := if reverse? then names.reverse else names
  let newScope := { scope with boundVars := names ++ scope.boundVars }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Add free variables to the global scope (scope 0) -/
def addGlobalFreeVars {M} (ctx : ToCSTContext M) (names : Array String)
    : ToCSTContext M :=
  let globalScope := ctx.scopes[0]!
  let newGlobalScope := { globalScope with freeVars :=
                            globalScope.freeVars ++ names }
  { ctx with scopes := ctx.scopes.set! 0 newGlobalScope }

/-- Push bound variables to the current scope.
  Unlike `addScopedBoundVars`, the variable is added to the end of the bound
  variables.
-/
def pushBoundVar {M} (ctx : ToCSTContext M) (name : String)
    : ToCSTContext M :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundVars := scope.boundVars.push name }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Push a new scope onto the stack -/
def pushScope {M} (ctx : ToCSTContext M) : ToCSTContext M :=
  { ctx with scopes := ctx.scopes.push {} }

/-- Pop the current scope from the stack (never pops scope 0) -/
def popScope {M} (ctx : ToCSTContext M) : ToCSTContext M :=
  if ctx.scopes.size > 1 then
    { ctx with scopes := ctx.scopes.pop }
  else
    ctx

end ToCSTContext

---------------------------------------------------------------------

/-- Monad for AST->CST conversion with context and error collection -/
@[expose] abbrev ToCSTM (M : Type) := StateM (ToCSTContext M)

/-- Log an error in `ToCSTM` without throwing -/
def ToCSTM.logError {M} [Inhabited M] (fn : String) (desc : String) (detail : String) : ToCSTM M Unit := do
  modify (·.logError fn desc detail)

/-- Does `name` carry a Core internal-operator prefix (`Bv<N>.`, `Int.`,
    `Real.`)? Such names come from the operator tables, so reaching the
    generic-call fallback with one means a missing arm in the CST mapping
    (the rendered call will not re-parse). -/
private def isInternalOpName (name : String) : Bool :=
  name.startsWith "Int." || name.startsWith "Real." ||
    (name.startsWith "Bv" &&
      let rest := name.drop 2 |>.dropWhile Char.isDigit
      rest.startsWith "." && rest.toString.length < name.length - 2)

#guard isInternalOpName "Int.Add"
#guard isInternalOpName "Real.Div"
#guard isInternalOpName "Bv32.Add"
#guard isInternalOpName "Bv128.Neg"
#guard isInternalOpName "Bv1.UAddOverflow"
#guard !isInternalOpName "Bv.Add"      -- no width digits
#guard !isInternalOpName "BvFoo.Add"   -- non-digit after Bv
#guard !isInternalOpName "Bv32Add"     -- no dot after the width
#guard !isInternalOpName "myFunc"
#guard !isInternalOpName "Integer.Add" -- prefix must be exactly `Int.`

/-- Render an unknown operation as a generic function call `name(args...)`.
    Registers the name as a free variable if not already registered. -/
def mkGenericCall {M} [Inhabited M] (caller : String) (name : String)
    (args : List (CoreDDM.Expr M)) : ToCSTM M (CoreDDM.Expr M) := do
  if isInternalOpName name then
    ToCSTM.logError caller
      "internal Core operator missing from the CST mapping tables; the rendered call will not re-parse" name
  else
    ToCSTM.logError caller "unknown operation, rendering as generic call" name
  let ctx ← get
  let idx ← match ctx.freeVarIndex? name with
    | some idx => pure idx
    | none =>
      let idx := ctx.allFreeVars.size
      modify (·.addGlobalFreeVars #[name])
      pure idx
  let fnExpr := CoreDDM.Expr.fvar default idx
  pure <| args.foldl (fun acc arg => .app default acc arg) fnExpr

/-- Convert `LMonoTy` to `CoreType` -/
def lmonoTyToCoreType {M} [Inhabited M] (ty : Lambda.LMonoTy) :
    ToCSTM M (CoreType M) := do
  match ty with
  | .ftvar name => pure (.tvar default name)
  | .bitvec 1 => pure (.bv default (.W1 default))
  | .bitvec 8 => pure (.bv default (.W8 default))
  | .bitvec 16 => pure (.bv default (.W16 default))
  | .bitvec 32 => pure (.bv default (.W32 default))
  | .bitvec 64 => pure (.bv default (.W64 default))
  | .bitvec 128 => pure (.bv default (.W128 default))
  | .bool => pure (.bool default)
  | .int => pure (.int default)
  | .string => pure (.string default)
  | .real => pure (.real default)
  | .tcons "regex" [] => pure (.regex default)
  | .tcons "Map" [k, v] => do
    let kty ← lmonoTyToCoreType k
    let vty ← lmonoTyToCoreType v
    pure (.Map default kty vty)
  | .tcons "Sequence" [e] => do
    let ety ← lmonoTyToCoreType e
    pure (.Sequence default ety)
  | .tcons "arrow" [a, b] => do
    let aty ← lmonoTyToCoreType a
    let bty ← lmonoTyToCoreType b
    pure (.arrow default aty bty)
  | .tcons name args =>
    let ctx ← get
    match ctx.freeVarIndex? name with
    | some idx => do
      let argTys ← args.mapM lmonoTyToCoreType
      pure (.fvar default idx argTys.toArray)
    | _ => do
      ToCSTM.logError "lmonoTyToCoreType" "unknown type" (toString ty)
      pure (.tvar default unknownTypeVar)
  | _ => do
    ToCSTM.logError "lmonoTyToCoreType" "unknown type" (toString ty)
    pure (.tvar default unknownTypeVar)

/-- Convert `LTy` to `CoreType` -/
def lTyToCoreType {M} [Inhabited M] (ty : Lambda.LTy) : ToCSTM M (CoreType M) :=
  match ty with
  | .forAll _typeVars monoTy => lmonoTyToCoreType monoTy

/-- Convert a type constructor declaration to CST -/
def typeConArgsToCST {M} [Inhabited M] (tcons : TypeConstructor)
    : Ann (Option (Bindings M)) M :=
  if tcons.params.isEmpty then
    ⟨default, none⟩
  else
    let bindings := tcons.params.map fun paramName =>
      let paramNameAnn : Ann String M := ⟨default, paramName⟩
      let paramType := TypeP.type default
      Binding.mkBinding default paramNameAnn paramType
    ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩

def lconstToExpr {M} [Inhabited M] (c : Lambda.LConst) :
    ToCSTM M (CoreDDM.Expr M) :=
  match c with
  | .boolConst true => pure (.btrue default)
  | .boolConst false => pure (.bfalse default)
  | .intConst n =>
    if n >= 0 then
      pure (.natToInt default ⟨default, n.toNat⟩)
    else
      pure (.unaryArithInt default (CoreDDM.UnaryArithInt.int_neg default)
        (.natToInt default ⟨default, n.natAbs⟩))
  | .realConst r =>
    match StrataDDM.Decimal.fromRat r with
    | some d => pure (.realLit default ⟨default, d⟩)
    | none =>
      -- Exact rational literals that are not parsed by `Decimal.fromRat`.
      let (neg, num, den) := FracLit.fracEncode r
      let fracExpr :=
        CoreDDM.Expr.fracLit default ⟨default, num⟩ ⟨default, den⟩
      if neg then
        pure (.unaryArithReal default (CoreDDM.UnaryArithReal.real_neg default) fracExpr)
      else
        pure fracExpr
  | .strConst s => pure (.strLit default ⟨default, s⟩)
  | .bitvecConst 1 n => pure (.bv1Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 8 n => pure (.bv8Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 16 n => pure (.bv16Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 32 n => pure (.bv32Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 64 n => pure (.bv64Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 128 n => pure (.bv128Lit default ⟨default, n.toNat⟩)
  | .bitvecConst w _ => do
    ToCSTM.logError "lconstToExpr" "unsupported bitvec width" (toString w)
    pure (.bv64Lit default ⟨default, w⟩)


/-- Handle 0-ary operations -/
def handleZeroaryOps {M} [Inhabited M] (name : String)
    : ToCSTM M (CoreDDM.Expr M) :=
  open Core in
  match CoreOp.ofString name with
  | .re .All => pure (.re_all default)
  | .re .AllChar => pure (.re_allchar default)
  | .re .None => pure (.re_none default)
  | _ => do
    ToCSTM.logError "lopToExpr" "0-ary op not found" name
    pure (.re_none default)

/-- Grouped type-specific unary operators to CST. Returns `none` for ops that are
    not part of a grouped family (handled structurally by the caller). The op
    name (e.g. "Int.Neg", "Bv8.ToUInt") selects the wrapper + category member. -/
private def groupedUnaryCST? {M} [Inhabited M] (name : String) (arg : CoreDDM.Expr M)
    : Option (CoreDDM.Expr M) :=
  match name with
  | "Int.Neg" => some (.unaryArithInt default (CoreDDM.UnaryArithInt.int_neg default) arg)
  | "Real.Neg" => some (.unaryArithReal default (CoreDDM.UnaryArithReal.real_neg default) arg)
  | "Bv1.Neg" => some (.unaryArithBv default (.W1 default) (CoreDDM.UnaryArithBv.bv1_neg default) arg)
  | "Bv1.Not" => some (.unaryArithBv default (.W1 default) (CoreDDM.UnaryArithBv.bv1_not default) arg)
  | "Bv1.SafeNeg" => some (.unarySafeBv default (.W1 default) (CoreDDM.UnarySafeBv.bv1_safeNeg default) arg)
  | "Bv1.SafeUNeg" => some (.unarySafeBv default (.W1 default) (CoreDDM.UnarySafeBv.bv1_safeUNeg default) arg)
  | "Bv1.SNegOverflow" => some (.unaryOverflowBv default (.W1 default) (CoreDDM.UnaryOverflowBv.bv1_sNegOverflow default) arg)
  | "Bv1.UNegOverflow" => some (.unaryOverflowBv default (.W1 default) (CoreDDM.UnaryOverflowBv.bv1_uNegOverflow default) arg)
  | "Bv8.Neg" => some (.unaryArithBv default (.W8 default) (CoreDDM.UnaryArithBv.bv8_neg default) arg)
  | "Bv8.Not" => some (.unaryArithBv default (.W8 default) (CoreDDM.UnaryArithBv.bv8_not default) arg)
  | "Bv8.SafeNeg" => some (.unarySafeBv default (.W8 default) (CoreDDM.UnarySafeBv.bv8_safeNeg default) arg)
  | "Bv8.SafeUNeg" => some (.unarySafeBv default (.W8 default) (CoreDDM.UnarySafeBv.bv8_safeUNeg default) arg)
  | "Bv8.SNegOverflow" => some (.unaryOverflowBv default (.W8 default) (CoreDDM.UnaryOverflowBv.bv8_sNegOverflow default) arg)
  | "Bv8.UNegOverflow" => some (.unaryOverflowBv default (.W8 default) (CoreDDM.UnaryOverflowBv.bv8_uNegOverflow default) arg)
  | "Bv16.Neg" => some (.unaryArithBv default (.W16 default) (CoreDDM.UnaryArithBv.bv16_neg default) arg)
  | "Bv16.Not" => some (.unaryArithBv default (.W16 default) (CoreDDM.UnaryArithBv.bv16_not default) arg)
  | "Bv16.SafeNeg" => some (.unarySafeBv default (.W16 default) (CoreDDM.UnarySafeBv.bv16_safeNeg default) arg)
  | "Bv16.SafeUNeg" => some (.unarySafeBv default (.W16 default) (CoreDDM.UnarySafeBv.bv16_safeUNeg default) arg)
  | "Bv16.SNegOverflow" => some (.unaryOverflowBv default (.W16 default) (CoreDDM.UnaryOverflowBv.bv16_sNegOverflow default) arg)
  | "Bv16.UNegOverflow" => some (.unaryOverflowBv default (.W16 default) (CoreDDM.UnaryOverflowBv.bv16_uNegOverflow default) arg)
  | "Bv32.Neg" => some (.unaryArithBv default (.W32 default) (CoreDDM.UnaryArithBv.bv32_neg default) arg)
  | "Bv32.Not" => some (.unaryArithBv default (.W32 default) (CoreDDM.UnaryArithBv.bv32_not default) arg)
  | "Bv32.SafeNeg" => some (.unarySafeBv default (.W32 default) (CoreDDM.UnarySafeBv.bv32_safeNeg default) arg)
  | "Bv32.SafeUNeg" => some (.unarySafeBv default (.W32 default) (CoreDDM.UnarySafeBv.bv32_safeUNeg default) arg)
  | "Bv32.SNegOverflow" => some (.unaryOverflowBv default (.W32 default) (CoreDDM.UnaryOverflowBv.bv32_sNegOverflow default) arg)
  | "Bv32.UNegOverflow" => some (.unaryOverflowBv default (.W32 default) (CoreDDM.UnaryOverflowBv.bv32_uNegOverflow default) arg)
  | "Bv64.Neg" => some (.unaryArithBv default (.W64 default) (CoreDDM.UnaryArithBv.bv64_neg default) arg)
  | "Bv128.Neg" => some (.unaryArithBv default (.W128 default) (CoreDDM.UnaryArithBv.bv128_neg default) arg)
  | "Bv64.Not" => some (.unaryArithBv default (.W64 default) (CoreDDM.UnaryArithBv.bv64_not default) arg)
  | "Bv128.Not" => some (.unaryArithBv default (.W128 default) (CoreDDM.UnaryArithBv.bv128_not default) arg)
  | "Bv64.SafeNeg" => some (.unarySafeBv default (.W64 default) (CoreDDM.UnarySafeBv.bv64_safeNeg default) arg)
  | "Bv128.SafeNeg" => some (.unarySafeBv default (.W128 default) (CoreDDM.UnarySafeBv.bv128_safeNeg default) arg)
  | "Bv64.SafeUNeg" => some (.unarySafeBv default (.W64 default) (CoreDDM.UnarySafeBv.bv64_safeUNeg default) arg)
  | "Bv128.SafeUNeg" => some (.unarySafeBv default (.W128 default) (CoreDDM.UnarySafeBv.bv128_safeUNeg default) arg)
  | "Bv64.SNegOverflow" => some (.unaryOverflowBv default (.W64 default) (CoreDDM.UnaryOverflowBv.bv64_sNegOverflow default) arg)
  | "Bv128.SNegOverflow" => some (.unaryOverflowBv default (.W128 default) (CoreDDM.UnaryOverflowBv.bv128_sNegOverflow default) arg)
  | "Bv64.UNegOverflow" => some (.unaryOverflowBv default (.W64 default) (CoreDDM.UnaryOverflowBv.bv64_uNegOverflow default) arg)
  | "Bv128.UNegOverflow" => some (.unaryOverflowBv default (.W128 default) (CoreDDM.UnaryOverflowBv.bv128_uNegOverflow default) arg)
  | "Bv1.ToUInt" => some (.castBv default (.W1 default) (CoreDDM.CastBv.bv1_toUInt default) arg)
  | "Bv1.ToInt" => some (.castBv default (.W1 default) (CoreDDM.CastBv.bv1_toInt default) arg)
  | "Bv8.ToUInt" => some (.castBv default (.W8 default) (CoreDDM.CastBv.bv8_toUInt default) arg)
  | "Bv8.ToInt" => some (.castBv default (.W8 default) (CoreDDM.CastBv.bv8_toInt default) arg)
  | "Bv16.ToUInt" => some (.castBv default (.W16 default) (CoreDDM.CastBv.bv16_toUInt default) arg)
  | "Bv16.ToInt" => some (.castBv default (.W16 default) (CoreDDM.CastBv.bv16_toInt default) arg)
  | "Bv32.ToUInt" => some (.castBv default (.W32 default) (CoreDDM.CastBv.bv32_toUInt default) arg)
  | "Bv32.ToInt" => some (.castBv default (.W32 default) (CoreDDM.CastBv.bv32_toInt default) arg)
  | "Bv64.ToUInt" => some (.castBv default (.W64 default) (CoreDDM.CastBv.bv64_toUInt default) arg)
  | "Bv64.ToInt" => some (.castBv default (.W64 default) (CoreDDM.CastBv.bv64_toInt default) arg)
  | "Bv128.ToUInt" => some (.castBv default (.W128 default) (CoreDDM.CastBv.bv128_toUInt default) arg)
  | "Bv128.ToInt" => some (.castBv default (.W128 default) (CoreDDM.CastBv.bv128_toInt default) arg)
  -- int -> bitvector casts (`as_bvN`): standalone grammar fns, not grouped wrappers.
  | "Int.ToBv1" => some (.as_bv1 default arg)
  | "Int.ToBv8" => some (.as_bv8 default arg)
  | "Int.ToBv16" => some (.as_bv16 default arg)
  | "Int.ToBv32" => some (.as_bv32 default arg)
  | "Int.ToBv64" => some (.as_bv64 default arg)
  | "Int.ToBv128" => some (.as_bv128 default arg)
  | _ => none

/-- Grouped type-specific binary operators → CST. Returns `none` for non-grouped ops. -/
private def groupedBinaryCST? {M} [Inhabited M] (name : String) (arg1 arg2 : CoreDDM.Expr M)
    : Option (CoreDDM.Expr M) :=
  match name with
  | "Int.Add" => some (.binaryArithBasicInt default (CoreDDM.BinaryArithBasicInt.int_add default) arg1 arg2)
  | "Int.Sub" => some (.binaryArithBasicInt default (CoreDDM.BinaryArithBasicInt.int_sub default) arg1 arg2)
  | "Int.Mul" => some (.binaryArithBasicInt default (CoreDDM.BinaryArithBasicInt.int_mul default) arg1 arg2)
  | "Int.Div" => some (.binaryArithDivModInt default (CoreDDM.BinaryArithDivModInt.int_div default) arg1 arg2)
  | "Int.Mod" => some (.binaryArithDivModInt default (CoreDDM.BinaryArithDivModInt.int_mod default) arg1 arg2)
  | "Int.SafeDiv" => some (.binarySafeInt default (CoreDDM.BinarySafeInt.int_safeDiv default) arg1 arg2)
  | "Int.SafeMod" => some (.binarySafeInt default (CoreDDM.BinarySafeInt.int_safeMod default) arg1 arg2)
  | "Int.DivT" => some (.binaryTruncInt default (CoreDDM.BinaryTruncInt.int_divT default) arg1 arg2)
  | "Int.ModT" => some (.binaryTruncInt default (CoreDDM.BinaryTruncInt.int_modT default) arg1 arg2)
  | "Int.SafeDivT" => some (.binaryTruncInt default (CoreDDM.BinaryTruncInt.int_safeDivT default) arg1 arg2)
  | "Int.SafeModT" => some (.binaryTruncInt default (CoreDDM.BinaryTruncInt.int_safeModT default) arg1 arg2)
  | "Int.Le" => some (.binaryCmpBaseInt default (CoreDDM.BinaryCmpBaseInt.int_le default) arg1 arg2)
  | "Int.Lt" => some (.binaryCmpBaseInt default (CoreDDM.BinaryCmpBaseInt.int_lt default) arg1 arg2)
  | "Int.Ge" => some (.binaryCmpBaseInt default (CoreDDM.BinaryCmpBaseInt.int_ge default) arg1 arg2)
  | "Int.Gt" => some (.binaryCmpBaseInt default (CoreDDM.BinaryCmpBaseInt.int_gt default) arg1 arg2)
  | "Real.Le" => some (.binaryCmpBaseReal default (CoreDDM.BinaryCmpBaseReal.real_le default) arg1 arg2)
  | "Real.Lt" => some (.binaryCmpBaseReal default (CoreDDM.BinaryCmpBaseReal.real_lt default) arg1 arg2)
  | "Real.Ge" => some (.binaryCmpBaseReal default (CoreDDM.BinaryCmpBaseReal.real_ge default) arg1 arg2)
  | "Real.Gt" => some (.binaryCmpBaseReal default (CoreDDM.BinaryCmpBaseReal.real_gt default) arg1 arg2)
  | "Bv1.ULe" => some (.binaryCmpBaseBv default (.W1 default) (CoreDDM.BinaryCmpBaseBv.bv1_uLe default) arg1 arg2)
  | "Bv1.ULt" => some (.binaryCmpBaseBv default (.W1 default) (CoreDDM.BinaryCmpBaseBv.bv1_uLt default) arg1 arg2)
  | "Bv1.UGe" => some (.binaryCmpBaseBv default (.W1 default) (CoreDDM.BinaryCmpBaseBv.bv1_uGe default) arg1 arg2)
  | "Bv1.UGt" => some (.binaryCmpBaseBv default (.W1 default) (CoreDDM.BinaryCmpBaseBv.bv1_uGt default) arg1 arg2)
  | "Bv1.SLe" => some (.binaryCmpSignedBv default (.W1 default) (CoreDDM.BinaryCmpSignedBv.bv1_sLe default) arg1 arg2)
  | "Bv1.SLt" => some (.binaryCmpSignedBv default (.W1 default) (CoreDDM.BinaryCmpSignedBv.bv1_sLt default) arg1 arg2)
  | "Bv1.SGe" => some (.binaryCmpSignedBv default (.W1 default) (CoreDDM.BinaryCmpSignedBv.bv1_sGe default) arg1 arg2)
  | "Bv1.SGt" => some (.binaryCmpSignedBv default (.W1 default) (CoreDDM.BinaryCmpSignedBv.bv1_sGt default) arg1 arg2)
  | "Bv8.ULe" => some (.binaryCmpBaseBv default (.W8 default) (CoreDDM.BinaryCmpBaseBv.bv8_uLe default) arg1 arg2)
  | "Bv8.ULt" => some (.binaryCmpBaseBv default (.W8 default) (CoreDDM.BinaryCmpBaseBv.bv8_uLt default) arg1 arg2)
  | "Bv8.UGe" => some (.binaryCmpBaseBv default (.W8 default) (CoreDDM.BinaryCmpBaseBv.bv8_uGe default) arg1 arg2)
  | "Bv8.UGt" => some (.binaryCmpBaseBv default (.W8 default) (CoreDDM.BinaryCmpBaseBv.bv8_uGt default) arg1 arg2)
  | "Bv8.SLe" => some (.binaryCmpSignedBv default (.W8 default) (CoreDDM.BinaryCmpSignedBv.bv8_sLe default) arg1 arg2)
  | "Bv8.SLt" => some (.binaryCmpSignedBv default (.W8 default) (CoreDDM.BinaryCmpSignedBv.bv8_sLt default) arg1 arg2)
  | "Bv8.SGe" => some (.binaryCmpSignedBv default (.W8 default) (CoreDDM.BinaryCmpSignedBv.bv8_sGe default) arg1 arg2)
  | "Bv8.SGt" => some (.binaryCmpSignedBv default (.W8 default) (CoreDDM.BinaryCmpSignedBv.bv8_sGt default) arg1 arg2)
  | "Bv16.ULe" => some (.binaryCmpBaseBv default (.W16 default) (CoreDDM.BinaryCmpBaseBv.bv16_uLe default) arg1 arg2)
  | "Bv16.ULt" => some (.binaryCmpBaseBv default (.W16 default) (CoreDDM.BinaryCmpBaseBv.bv16_uLt default) arg1 arg2)
  | "Bv16.UGe" => some (.binaryCmpBaseBv default (.W16 default) (CoreDDM.BinaryCmpBaseBv.bv16_uGe default) arg1 arg2)
  | "Bv16.UGt" => some (.binaryCmpBaseBv default (.W16 default) (CoreDDM.BinaryCmpBaseBv.bv16_uGt default) arg1 arg2)
  | "Bv16.SLe" => some (.binaryCmpSignedBv default (.W16 default) (CoreDDM.BinaryCmpSignedBv.bv16_sLe default) arg1 arg2)
  | "Bv16.SLt" => some (.binaryCmpSignedBv default (.W16 default) (CoreDDM.BinaryCmpSignedBv.bv16_sLt default) arg1 arg2)
  | "Bv16.SGe" => some (.binaryCmpSignedBv default (.W16 default) (CoreDDM.BinaryCmpSignedBv.bv16_sGe default) arg1 arg2)
  | "Bv16.SGt" => some (.binaryCmpSignedBv default (.W16 default) (CoreDDM.BinaryCmpSignedBv.bv16_sGt default) arg1 arg2)
  | "Bv32.ULe" => some (.binaryCmpBaseBv default (.W32 default) (CoreDDM.BinaryCmpBaseBv.bv32_uLe default) arg1 arg2)
  | "Bv32.ULt" => some (.binaryCmpBaseBv default (.W32 default) (CoreDDM.BinaryCmpBaseBv.bv32_uLt default) arg1 arg2)
  | "Bv32.UGe" => some (.binaryCmpBaseBv default (.W32 default) (CoreDDM.BinaryCmpBaseBv.bv32_uGe default) arg1 arg2)
  | "Bv32.UGt" => some (.binaryCmpBaseBv default (.W32 default) (CoreDDM.BinaryCmpBaseBv.bv32_uGt default) arg1 arg2)
  | "Bv32.SLe" => some (.binaryCmpSignedBv default (.W32 default) (CoreDDM.BinaryCmpSignedBv.bv32_sLe default) arg1 arg2)
  | "Bv32.SLt" => some (.binaryCmpSignedBv default (.W32 default) (CoreDDM.BinaryCmpSignedBv.bv32_sLt default) arg1 arg2)
  | "Bv32.SGe" => some (.binaryCmpSignedBv default (.W32 default) (CoreDDM.BinaryCmpSignedBv.bv32_sGe default) arg1 arg2)
  | "Bv32.SGt" => some (.binaryCmpSignedBv default (.W32 default) (CoreDDM.BinaryCmpSignedBv.bv32_sGt default) arg1 arg2)
  | "Bv64.ULe" => some (.binaryCmpBaseBv default (.W64 default) (CoreDDM.BinaryCmpBaseBv.bv64_uLe default) arg1 arg2)
  | "Bv128.ULe" => some (.binaryCmpBaseBv default (.W128 default) (CoreDDM.BinaryCmpBaseBv.bv128_uLe default) arg1 arg2)
  | "Bv64.ULt" => some (.binaryCmpBaseBv default (.W64 default) (CoreDDM.BinaryCmpBaseBv.bv64_uLt default) arg1 arg2)
  | "Bv128.ULt" => some (.binaryCmpBaseBv default (.W128 default) (CoreDDM.BinaryCmpBaseBv.bv128_uLt default) arg1 arg2)
  | "Bv64.UGe" => some (.binaryCmpBaseBv default (.W64 default) (CoreDDM.BinaryCmpBaseBv.bv64_uGe default) arg1 arg2)
  | "Bv128.UGe" => some (.binaryCmpBaseBv default (.W128 default) (CoreDDM.BinaryCmpBaseBv.bv128_uGe default) arg1 arg2)
  | "Bv64.UGt" => some (.binaryCmpBaseBv default (.W64 default) (CoreDDM.BinaryCmpBaseBv.bv64_uGt default) arg1 arg2)
  | "Bv128.UGt" => some (.binaryCmpBaseBv default (.W128 default) (CoreDDM.BinaryCmpBaseBv.bv128_uGt default) arg1 arg2)
  | "Bv64.SLe" => some (.binaryCmpSignedBv default (.W64 default) (CoreDDM.BinaryCmpSignedBv.bv64_sLe default) arg1 arg2)
  | "Bv128.SLe" => some (.binaryCmpSignedBv default (.W128 default) (CoreDDM.BinaryCmpSignedBv.bv128_sLe default) arg1 arg2)
  | "Bv64.SLt" => some (.binaryCmpSignedBv default (.W64 default) (CoreDDM.BinaryCmpSignedBv.bv64_sLt default) arg1 arg2)
  | "Bv128.SLt" => some (.binaryCmpSignedBv default (.W128 default) (CoreDDM.BinaryCmpSignedBv.bv128_sLt default) arg1 arg2)
  | "Bv64.SGe" => some (.binaryCmpSignedBv default (.W64 default) (CoreDDM.BinaryCmpSignedBv.bv64_sGe default) arg1 arg2)
  | "Bv128.SGe" => some (.binaryCmpSignedBv default (.W128 default) (CoreDDM.BinaryCmpSignedBv.bv128_sGe default) arg1 arg2)
  | "Bv64.SGt" => some (.binaryCmpSignedBv default (.W64 default) (CoreDDM.BinaryCmpSignedBv.bv64_sGt default) arg1 arg2)
  | "Bv128.SGt" => some (.binaryCmpSignedBv default (.W128 default) (CoreDDM.BinaryCmpSignedBv.bv128_sGt default) arg1 arg2)
  | "Real.Add" => some (.binaryArithBasicReal default (CoreDDM.BinaryArithBasicReal.real_add default) arg1 arg2)
  | "Real.Sub" => some (.binaryArithBasicReal default (CoreDDM.BinaryArithBasicReal.real_sub default) arg1 arg2)
  | "Real.Mul" => some (.binaryArithBasicReal default (CoreDDM.BinaryArithBasicReal.real_mul default) arg1 arg2)
  | "Real.Div" => some (.binaryArithDivModReal default (CoreDDM.BinaryArithDivModReal.real_div default) arg1 arg2)
  | "Bv1.Add" => some (.binaryArithBasicBv default (.W1 default) (CoreDDM.BinaryArithBasicBv.bv1_add default) arg1 arg2)
  | "Bv1.Sub" => some (.binaryArithBasicBv default (.W1 default) (CoreDDM.BinaryArithBasicBv.bv1_sub default) arg1 arg2)
  | "Bv1.Mul" => some (.binaryArithBasicBv default (.W1 default) (CoreDDM.BinaryArithBasicBv.bv1_mul default) arg1 arg2)
  | "Bv1.UDiv" => some (.binaryArithDivModBv default (.W1 default) (CoreDDM.BinaryArithDivModBv.bv1_uDiv default) arg1 arg2)
  | "Bv1.UMod" => some (.binaryArithDivModBv default (.W1 default) (CoreDDM.BinaryArithDivModBv.bv1_uMod default) arg1 arg2)
  | "Bv1.SDiv" => some (.binaryArithDivModBv default (.W1 default) (CoreDDM.BinaryArithDivModBv.bv1_sDiv default) arg1 arg2)
  | "Bv1.SMod" => some (.binaryArithDivModBv default (.W1 default) (CoreDDM.BinaryArithDivModBv.bv1_sMod default) arg1 arg2)
  | "Bv1.And" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_and default) arg1 arg2)
  | "Bv1.Or" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_or default) arg1 arg2)
  | "Bv1.Xor" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_xor default) arg1 arg2)
  | "Bv1.Shl" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_shl default) arg1 arg2)
  | "Bv1.UShr" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_uShr default) arg1 arg2)
  | "Bv1.SShr" => some (.binaryBitwiseBv default (.W1 default) (CoreDDM.BinaryBitwiseBv.bv1_sShr default) arg1 arg2)
  | "Bv1.SafeAdd" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeAdd default) arg1 arg2)
  | "Bv1.SafeSub" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeSub default) arg1 arg2)
  | "Bv1.SafeMul" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeMul default) arg1 arg2)
  | "Bv1.SafeUAdd" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeUAdd default) arg1 arg2)
  | "Bv1.SafeUSub" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeUSub default) arg1 arg2)
  | "Bv1.SafeUMul" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeUMul default) arg1 arg2)
  | "Bv1.SafeSDiv" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeSDiv default) arg1 arg2)
  | "Bv1.SafeSMod" => some (.binarySafeBv default (.W1 default) (CoreDDM.BinarySafeBv.bv1_safeSMod default) arg1 arg2)
  | "Bv1.SAddOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_sAddOverflow default) arg1 arg2)
  | "Bv1.SSubOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_sSubOverflow default) arg1 arg2)
  | "Bv1.SMulOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_sMulOverflow default) arg1 arg2)
  | "Bv1.SDivOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_sDivOverflow default) arg1 arg2)
  | "Bv1.UAddOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_uAddOverflow default) arg1 arg2)
  | "Bv1.USubOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_uSubOverflow default) arg1 arg2)
  | "Bv1.UMulOverflow" => some (.binaryOverflowBv default (.W1 default) (CoreDDM.BinaryOverflowBv.bv1_uMulOverflow default) arg1 arg2)
  | "Bv8.Add" => some (.binaryArithBasicBv default (.W8 default) (CoreDDM.BinaryArithBasicBv.bv8_add default) arg1 arg2)
  | "Bv8.Sub" => some (.binaryArithBasicBv default (.W8 default) (CoreDDM.BinaryArithBasicBv.bv8_sub default) arg1 arg2)
  | "Bv8.Mul" => some (.binaryArithBasicBv default (.W8 default) (CoreDDM.BinaryArithBasicBv.bv8_mul default) arg1 arg2)
  | "Bv8.UDiv" => some (.binaryArithDivModBv default (.W8 default) (CoreDDM.BinaryArithDivModBv.bv8_uDiv default) arg1 arg2)
  | "Bv8.UMod" => some (.binaryArithDivModBv default (.W8 default) (CoreDDM.BinaryArithDivModBv.bv8_uMod default) arg1 arg2)
  | "Bv8.SDiv" => some (.binaryArithDivModBv default (.W8 default) (CoreDDM.BinaryArithDivModBv.bv8_sDiv default) arg1 arg2)
  | "Bv8.SMod" => some (.binaryArithDivModBv default (.W8 default) (CoreDDM.BinaryArithDivModBv.bv8_sMod default) arg1 arg2)
  | "Bv8.And" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_and default) arg1 arg2)
  | "Bv8.Or" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_or default) arg1 arg2)
  | "Bv8.Xor" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_xor default) arg1 arg2)
  | "Bv8.Shl" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_shl default) arg1 arg2)
  | "Bv8.UShr" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_uShr default) arg1 arg2)
  | "Bv8.SShr" => some (.binaryBitwiseBv default (.W8 default) (CoreDDM.BinaryBitwiseBv.bv8_sShr default) arg1 arg2)
  | "Bv8.SafeAdd" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeAdd default) arg1 arg2)
  | "Bv8.SafeSub" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeSub default) arg1 arg2)
  | "Bv8.SafeMul" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeMul default) arg1 arg2)
  | "Bv8.SafeUAdd" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeUAdd default) arg1 arg2)
  | "Bv8.SafeUSub" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeUSub default) arg1 arg2)
  | "Bv8.SafeUMul" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeUMul default) arg1 arg2)
  | "Bv8.SafeSDiv" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeSDiv default) arg1 arg2)
  | "Bv8.SafeSMod" => some (.binarySafeBv default (.W8 default) (CoreDDM.BinarySafeBv.bv8_safeSMod default) arg1 arg2)
  | "Bv8.SAddOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_sAddOverflow default) arg1 arg2)
  | "Bv8.SSubOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_sSubOverflow default) arg1 arg2)
  | "Bv8.SMulOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_sMulOverflow default) arg1 arg2)
  | "Bv8.SDivOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_sDivOverflow default) arg1 arg2)
  | "Bv8.UAddOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_uAddOverflow default) arg1 arg2)
  | "Bv8.USubOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_uSubOverflow default) arg1 arg2)
  | "Bv8.UMulOverflow" => some (.binaryOverflowBv default (.W8 default) (CoreDDM.BinaryOverflowBv.bv8_uMulOverflow default) arg1 arg2)
  | "Bv16.Add" => some (.binaryArithBasicBv default (.W16 default) (CoreDDM.BinaryArithBasicBv.bv16_add default) arg1 arg2)
  | "Bv16.Sub" => some (.binaryArithBasicBv default (.W16 default) (CoreDDM.BinaryArithBasicBv.bv16_sub default) arg1 arg2)
  | "Bv16.Mul" => some (.binaryArithBasicBv default (.W16 default) (CoreDDM.BinaryArithBasicBv.bv16_mul default) arg1 arg2)
  | "Bv16.UDiv" => some (.binaryArithDivModBv default (.W16 default) (CoreDDM.BinaryArithDivModBv.bv16_uDiv default) arg1 arg2)
  | "Bv16.UMod" => some (.binaryArithDivModBv default (.W16 default) (CoreDDM.BinaryArithDivModBv.bv16_uMod default) arg1 arg2)
  | "Bv16.SDiv" => some (.binaryArithDivModBv default (.W16 default) (CoreDDM.BinaryArithDivModBv.bv16_sDiv default) arg1 arg2)
  | "Bv16.SMod" => some (.binaryArithDivModBv default (.W16 default) (CoreDDM.BinaryArithDivModBv.bv16_sMod default) arg1 arg2)
  | "Bv16.And" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_and default) arg1 arg2)
  | "Bv16.Or" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_or default) arg1 arg2)
  | "Bv16.Xor" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_xor default) arg1 arg2)
  | "Bv16.Shl" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_shl default) arg1 arg2)
  | "Bv16.UShr" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_uShr default) arg1 arg2)
  | "Bv16.SShr" => some (.binaryBitwiseBv default (.W16 default) (CoreDDM.BinaryBitwiseBv.bv16_sShr default) arg1 arg2)
  | "Bv16.SafeAdd" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeAdd default) arg1 arg2)
  | "Bv16.SafeSub" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeSub default) arg1 arg2)
  | "Bv16.SafeMul" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeMul default) arg1 arg2)
  | "Bv16.SafeUAdd" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeUAdd default) arg1 arg2)
  | "Bv16.SafeUSub" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeUSub default) arg1 arg2)
  | "Bv16.SafeUMul" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeUMul default) arg1 arg2)
  | "Bv16.SafeSDiv" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeSDiv default) arg1 arg2)
  | "Bv16.SafeSMod" => some (.binarySafeBv default (.W16 default) (CoreDDM.BinarySafeBv.bv16_safeSMod default) arg1 arg2)
  | "Bv16.SAddOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_sAddOverflow default) arg1 arg2)
  | "Bv16.SSubOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_sSubOverflow default) arg1 arg2)
  | "Bv16.SMulOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_sMulOverflow default) arg1 arg2)
  | "Bv16.SDivOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_sDivOverflow default) arg1 arg2)
  | "Bv16.UAddOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_uAddOverflow default) arg1 arg2)
  | "Bv16.USubOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_uSubOverflow default) arg1 arg2)
  | "Bv16.UMulOverflow" => some (.binaryOverflowBv default (.W16 default) (CoreDDM.BinaryOverflowBv.bv16_uMulOverflow default) arg1 arg2)
  | "Bv32.Add" => some (.binaryArithBasicBv default (.W32 default) (CoreDDM.BinaryArithBasicBv.bv32_add default) arg1 arg2)
  | "Bv32.Sub" => some (.binaryArithBasicBv default (.W32 default) (CoreDDM.BinaryArithBasicBv.bv32_sub default) arg1 arg2)
  | "Bv32.Mul" => some (.binaryArithBasicBv default (.W32 default) (CoreDDM.BinaryArithBasicBv.bv32_mul default) arg1 arg2)
  | "Bv32.UDiv" => some (.binaryArithDivModBv default (.W32 default) (CoreDDM.BinaryArithDivModBv.bv32_uDiv default) arg1 arg2)
  | "Bv32.UMod" => some (.binaryArithDivModBv default (.W32 default) (CoreDDM.BinaryArithDivModBv.bv32_uMod default) arg1 arg2)
  | "Bv32.SDiv" => some (.binaryArithDivModBv default (.W32 default) (CoreDDM.BinaryArithDivModBv.bv32_sDiv default) arg1 arg2)
  | "Bv32.SMod" => some (.binaryArithDivModBv default (.W32 default) (CoreDDM.BinaryArithDivModBv.bv32_sMod default) arg1 arg2)
  | "Bv32.And" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_and default) arg1 arg2)
  | "Bv32.Or" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_or default) arg1 arg2)
  | "Bv32.Xor" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_xor default) arg1 arg2)
  | "Bv32.Shl" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_shl default) arg1 arg2)
  | "Bv32.UShr" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_uShr default) arg1 arg2)
  | "Bv32.SShr" => some (.binaryBitwiseBv default (.W32 default) (CoreDDM.BinaryBitwiseBv.bv32_sShr default) arg1 arg2)
  | "Bv32.SafeAdd" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeAdd default) arg1 arg2)
  | "Bv32.SafeSub" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeSub default) arg1 arg2)
  | "Bv32.SafeMul" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeMul default) arg1 arg2)
  | "Bv32.SafeUAdd" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeUAdd default) arg1 arg2)
  | "Bv32.SafeUSub" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeUSub default) arg1 arg2)
  | "Bv32.SafeUMul" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeUMul default) arg1 arg2)
  | "Bv32.SafeSDiv" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeSDiv default) arg1 arg2)
  | "Bv32.SafeSMod" => some (.binarySafeBv default (.W32 default) (CoreDDM.BinarySafeBv.bv32_safeSMod default) arg1 arg2)
  | "Bv32.SAddOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_sAddOverflow default) arg1 arg2)
  | "Bv32.SSubOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_sSubOverflow default) arg1 arg2)
  | "Bv32.SMulOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_sMulOverflow default) arg1 arg2)
  | "Bv32.SDivOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_sDivOverflow default) arg1 arg2)
  | "Bv32.UAddOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_uAddOverflow default) arg1 arg2)
  | "Bv32.USubOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_uSubOverflow default) arg1 arg2)
  | "Bv32.UMulOverflow" => some (.binaryOverflowBv default (.W32 default) (CoreDDM.BinaryOverflowBv.bv32_uMulOverflow default) arg1 arg2)
  | "Bv64.Add" => some (.binaryArithBasicBv default (.W64 default) (CoreDDM.BinaryArithBasicBv.bv64_add default) arg1 arg2)
  | "Bv128.Add" => some (.binaryArithBasicBv default (.W128 default) (CoreDDM.BinaryArithBasicBv.bv128_add default) arg1 arg2)
  | "Bv64.Sub" => some (.binaryArithBasicBv default (.W64 default) (CoreDDM.BinaryArithBasicBv.bv64_sub default) arg1 arg2)
  | "Bv128.Sub" => some (.binaryArithBasicBv default (.W128 default) (CoreDDM.BinaryArithBasicBv.bv128_sub default) arg1 arg2)
  | "Bv64.Mul" => some (.binaryArithBasicBv default (.W64 default) (CoreDDM.BinaryArithBasicBv.bv64_mul default) arg1 arg2)
  | "Bv128.Mul" => some (.binaryArithBasicBv default (.W128 default) (CoreDDM.BinaryArithBasicBv.bv128_mul default) arg1 arg2)
  | "Bv64.UDiv" => some (.binaryArithDivModBv default (.W64 default) (CoreDDM.BinaryArithDivModBv.bv64_uDiv default) arg1 arg2)
  | "Bv128.UDiv" => some (.binaryArithDivModBv default (.W128 default) (CoreDDM.BinaryArithDivModBv.bv128_uDiv default) arg1 arg2)
  | "Bv64.UMod" => some (.binaryArithDivModBv default (.W64 default) (CoreDDM.BinaryArithDivModBv.bv64_uMod default) arg1 arg2)
  | "Bv128.UMod" => some (.binaryArithDivModBv default (.W128 default) (CoreDDM.BinaryArithDivModBv.bv128_uMod default) arg1 arg2)
  | "Bv64.SDiv" => some (.binaryArithDivModBv default (.W64 default) (CoreDDM.BinaryArithDivModBv.bv64_sDiv default) arg1 arg2)
  | "Bv128.SDiv" => some (.binaryArithDivModBv default (.W128 default) (CoreDDM.BinaryArithDivModBv.bv128_sDiv default) arg1 arg2)
  | "Bv64.SMod" => some (.binaryArithDivModBv default (.W64 default) (CoreDDM.BinaryArithDivModBv.bv64_sMod default) arg1 arg2)
  | "Bv128.SMod" => some (.binaryArithDivModBv default (.W128 default) (CoreDDM.BinaryArithDivModBv.bv128_sMod default) arg1 arg2)
  | "Bv64.And" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_and default) arg1 arg2)
  | "Bv128.And" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_and default) arg1 arg2)
  | "Bv64.Or" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_or default) arg1 arg2)
  | "Bv128.Or" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_or default) arg1 arg2)
  | "Bv64.Xor" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_xor default) arg1 arg2)
  | "Bv128.Xor" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_xor default) arg1 arg2)
  | "Bv64.Shl" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_shl default) arg1 arg2)
  | "Bv128.Shl" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_shl default) arg1 arg2)
  | "Bv64.UShr" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_uShr default) arg1 arg2)
  | "Bv128.UShr" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_uShr default) arg1 arg2)
  | "Bv64.SShr" => some (.binaryBitwiseBv default (.W64 default) (CoreDDM.BinaryBitwiseBv.bv64_sShr default) arg1 arg2)
  | "Bv128.SShr" => some (.binaryBitwiseBv default (.W128 default) (CoreDDM.BinaryBitwiseBv.bv128_sShr default) arg1 arg2)
  | "Bv64.SafeAdd" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeAdd default) arg1 arg2)
  | "Bv128.SafeAdd" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeAdd default) arg1 arg2)
  | "Bv64.SafeSub" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeSub default) arg1 arg2)
  | "Bv128.SafeSub" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeSub default) arg1 arg2)
  | "Bv64.SafeMul" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeMul default) arg1 arg2)
  | "Bv128.SafeMul" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeMul default) arg1 arg2)
  | "Bv64.SafeUAdd" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeUAdd default) arg1 arg2)
  | "Bv128.SafeUAdd" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeUAdd default) arg1 arg2)
  | "Bv64.SafeUSub" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeUSub default) arg1 arg2)
  | "Bv128.SafeUSub" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeUSub default) arg1 arg2)
  | "Bv64.SafeUMul" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeUMul default) arg1 arg2)
  | "Bv128.SafeUMul" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeUMul default) arg1 arg2)
  | "Bv64.SafeSDiv" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeSDiv default) arg1 arg2)
  | "Bv128.SafeSDiv" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeSDiv default) arg1 arg2)
  | "Bv64.SafeSMod" => some (.binarySafeBv default (.W64 default) (CoreDDM.BinarySafeBv.bv64_safeSMod default) arg1 arg2)
  | "Bv128.SafeSMod" => some (.binarySafeBv default (.W128 default) (CoreDDM.BinarySafeBv.bv128_safeSMod default) arg1 arg2)
  | "Bv64.SAddOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_sAddOverflow default) arg1 arg2)
  | "Bv128.SAddOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_sAddOverflow default) arg1 arg2)
  | "Bv64.SSubOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_sSubOverflow default) arg1 arg2)
  | "Bv128.SSubOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_sSubOverflow default) arg1 arg2)
  | "Bv64.SMulOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_sMulOverflow default) arg1 arg2)
  | "Bv128.SMulOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_sMulOverflow default) arg1 arg2)
  | "Bv64.SDivOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_sDivOverflow default) arg1 arg2)
  | "Bv128.SDivOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_sDivOverflow default) arg1 arg2)
  | "Bv64.UAddOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_uAddOverflow default) arg1 arg2)
  | "Bv128.UAddOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_uAddOverflow default) arg1 arg2)
  | "Bv64.USubOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_uSubOverflow default) arg1 arg2)
  | "Bv128.USubOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_uSubOverflow default) arg1 arg2)
  | "Bv64.UMulOverflow" => some (.binaryOverflowBv default (.W64 default) (CoreDDM.BinaryOverflowBv.bv64_uMulOverflow default) arg1 arg2)
  | "Bv128.UMulOverflow" => some (.binaryOverflowBv default (.W128 default) (CoreDDM.BinaryOverflowBv.bv128_uMulOverflow default) arg1 arg2)
  | _ => none

/-- Handle unary operations -/
def handleUnaryOps {M} [Inhabited M] (name : String) (arg : CoreDDM.Expr M)
    : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  open Core in
  -- Type-specific unary operators (neg, not, safeNeg, overflow, casts) are
  -- grouped: each is a nullary member of a wrapper category, dispatched by name.
  match groupedUnaryCST? name arg with
  | some e => pure e
  | none =>
  match CoreOp.ofString name with
  | .other "old" => pure (.old default ty arg)
  -- Booleans
  | .bool .Not => pure (.not default arg)
  -- Strings and regexes
  | .str .Length => pure (.str_len default arg)
  | .str .ToRegEx => pure (.str_toregex default arg)
  | .re .Star => pure (.re_star default arg)
  | .re .Plus => pure (.re_plus default arg)
  | .re .Comp => pure (.re_comp default arg)
  -- Sequences
  | .seq .Length => pure (.seq_length default ty arg)
  -- Bitvector extract ops (not part of the grouped operator families).
  | .bvExtract 8 7 7 => pure (.bvextract_7_7 default arg)
  | .bvExtract 16 15 15 => pure (.bvextract_15_15 default arg)
  | .bvExtract 32 31 31 => pure (.bvextract_31_31 default arg)
  | .bvExtract 16 7 0 => pure (.bvextract_7_0_16 default arg)
  | .bvExtract 32 7 0 => pure (.bvextract_7_0_32 default arg)
  | .bvExtract 32 15 0 => pure (.bvextract_15_0_32 default arg)
  | .bvExtract 64 7 0 => pure (.bvextract_7_0_64 default arg)
  | .bvExtract 64 15 0 => pure (.bvextract_15_0_64 default arg)
  | .bvExtract 64 31 0 => pure (.bvextract_31_0_64 default arg)
  | _ => mkGenericCall "handleUnaryOps" name [arg]

/-- Handle binary operations -/
def handleBinaryOps {M} [Inhabited M] (name : String)
    (arg1 arg2 : CoreDDM.Expr M) : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  open Core in
  -- Type-specific binary operators (arith, bitwise, comparison, safe, overflow)
  -- are grouped: each is a nullary member of a wrapper category, by name.
  match groupedBinaryCST? name arg1 arg2 with
  | some e => pure e
  | none =>
  match CoreOp.ofString name with
  -- Bitvector concat (not part of the grouped operator families).
  | .bv ⟨8, .Concat⟩ => pure (.bvconcat8 default arg1 arg2)
  | .bv ⟨16, .Concat⟩ => pure (.bvconcat16 default arg1 arg2)
  | .bv ⟨32, .Concat⟩ => pure (.bvconcat32 default arg1 arg2)
  -- Boolean operations
  | .bool .And => pure (.and default arg1 arg2)
  | .bool .Or => pure (.or default arg1 arg2)
  | .bool .Implies => pure (.implies default arg1 arg2)
  | .bool .Equiv => pure (.equiv default arg1 arg2)
  -- Map operations
  | .map .Select => pure (.map_get default ty ty arg1 arg2)
  -- Sequence operations
  | .seq .Select => pure (.seq_select default ty arg1 arg2)
  | .seq .Append => pure (.seq_append default ty arg1 arg2)
  | .seq .Build => pure (.seq_build default ty arg1 arg2)
  | .seq .Contains => pure (.seq_contains default ty arg1 arg2)
  | .seq .Take => pure (.seq_take default ty arg1 arg2)
  | .seq .Drop => pure (.seq_drop default ty arg1 arg2)
  -- String and Regex operations
  | .str .Concat => pure (.str_concat default arg1 arg2)
  | .str .InRegEx => pure (.str_inregex default arg1 arg2)
  | .str .PrefixOf => pure (.str_prefixof default arg1 arg2)
  | .str .SuffixOf => pure (.str_suffixof default arg1 arg2)
  | .str .Contains => pure (.str_contains default arg1 arg2)
  | .str .At => pure (.str_at default arg1 arg2)
  | .str .Lt => pure (.str_lt default arg1 arg2)
  | .str .Le => pure (.str_le default arg1 arg2)
  | .re .Range => pure (.re_range default arg1 arg2)
  | .re .Concat => pure (.re_concat default arg1 arg2)
  | .re .Union => pure (.re_union default arg1 arg2)
  | .re .Inter => pure (.re_inter default arg1 arg2)
  | _ => mkGenericCall "handleBinaryOps" name [arg1, arg2]

/-- Handle ternary operations -/
def handleTernaryOps {M} [Inhabited M] (name : String)
    (arg1 arg2 arg3 : CoreDDM.Expr M) : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  open Core in
  match CoreOp.ofString name with
  -- Maps
  | .map .Update => pure (.map_set default ty ty arg1 arg2 arg3)
  -- Sequences
  | .seq .Update => pure (.seq_update default ty arg1 arg2 arg3)
  -- Strings and regexes
  | .str .Substr => pure (.str_substr default arg1 arg2 arg3)
  | .str .IndexOf => pure (.str_indexof default arg1 arg2 arg3)
  | .str .Replace => pure (.str_replace default arg1 arg2 arg3)
  | .re .Loop => pure (.re_loop default arg1 arg2 arg3)
  | _ => mkGenericCall "handleTernaryOps" name [arg1, arg2, arg3]

def lopToExpr {M} [Inhabited M]
    (name : String) (args : List (CoreDDM.Expr M))
    : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  -- User-defined functions: check bound vars first (local funcDecl via
  -- @[declareFn]), then free vars (global declarations).
  match ctx.findBoundVarIndex? name with
  | some idx =>
    let fnExpr := CoreDDM.Expr.bvar default (ctx.allBoundVars.size - (idx + 1))
    pure <| args.foldl (fun acc arg => .app default acc arg) fnExpr
  | none =>
  match ctx.freeVarIndex? name with
  | some idx =>
    let fnExpr := CoreDDM.Expr.fvar default idx
    pure <| args.foldl (fun acc arg => .app default acc arg) fnExpr
  | none =>
    -- Either a built-in or an invalid operation.
    match args with
    | [] => handleZeroaryOps name
    | [arg] => handleUnaryOps name arg
    | [arg1, arg2] => handleBinaryOps name arg1 arg2
    | [arg1, arg2, arg3] => handleTernaryOps name arg1 arg2 arg3
    | args => mkGenericCall "lopToExpr" name args

mutual
/-- Convert `Lambda.LExpr` to Core `Expr` -/
partial def lexprToExpr {M} [Inhabited M]
    (e : Lambda.LExpr CoreLParams.mono) (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  match e with
  | .const _ c => lconstToExpr c
  | .bvar _ idx =>
    if idx < ctx.allBoundVars.size then
      pure (.bvar default idx)
    else
      ToCSTM.logError "lexprToExpr" "bvar index out of bounds" (toString idx)
      pure (.bvar default idx)
  | .fvar _ id _ =>
    -- We first look for Lambda .fvars in the boundVars context, before checking
    -- the freeVars context. Lambda .fvars can come from formals of a function
    -- or procedure (which are .bvars in DDM), but also from global variable
    -- declaration (which are DDM .fvars). Note that Strata Core does not allow
    -- variable shadowing.
    match ctx.findBoundVarIndex? id.name with
    | some idx => pure (.bvar default (ctx.allBoundVars.size - (idx + 1)))
    | none =>
      match ctx.freeVarIndex? id.name with
      | some idx => pure (.fvar default idx)
      | none => do
        -- Likely this .fvar is generated in an evaluated Core program (i.e.,
        -- after analysis). Add to the context.
        modify (·.addGlobalFreeVars #[id.name])
        pure (.fvar default (ctx.allFreeVars.size))
  | .ite _ c t f => liteToExpr c t f qLevel
  | .eq _ e1 e2 => leqToExpr e1 e2 qLevel
  | .op _ name ty => do
    -- seq_empty needs the type annotation to render the explicit type parameter
    if name.name == "Sequence.empty" then
      let tyCST ← match ty with
        | some (.tcons "Sequence" [ety]) => lmonoTyToCoreType ety
        | _ => pure (CoreType.tvar default unknownTypeVar)
      pure (.seq_empty default tyCST)
    else
      lopToExpr name.name []
  | .app _ _ _ => lappToExpr e qLevel
  | .abs _ prettyName ty body => labsToExpr prettyName ty body (qLevel + 1)
  | .quant _ qkind prettyName ty trigger body =>
    lquantToExpr qkind prettyName ty trigger body (qLevel + 1)

/-- Extract trigger patterns from Lambda's trigger expression representation -/
partial def extractTriggerPatterns {M} [Inhabited M]
    (trigger : Lambda.LExpr CoreLParams.mono) (qLevel : Nat)
    : ToCSTM M (Array (CoreDDM.Expr M)) := do
  match trigger with
  | .bvar _ 0 => pure #[]  -- noTrigger
  | .app _ (.app _ (.op _ name _) triggerExpr) rest =>
    if name.name == "TriggerGroup.addTrigger" then
      let expr ← lexprToExpr triggerExpr qLevel
      let restExprs ← extractTriggerPatterns rest qLevel
      pure (#[expr] ++ restExprs)
    else if name.name == "Triggers.addGroup" then
      -- Triggers.addGroup adds a trigger group to a triggers list
      -- triggerExpr is a TriggerGroup, rest is the Triggers list
      let groupExprs ← extractTriggerPatterns triggerExpr qLevel
      let restExprs ← extractTriggerPatterns rest qLevel
      pure (groupExprs ++ restExprs)
    else do
      ToCSTM.logError "extractTriggerPatterns" "unexpected trigger operation" name.name
      pure #[]
  | .op _ name _ =>
    if name.name == "TriggerGroup.empty" ||
       name.name == "Triggers.empty" then
      pure #[]
    else do
      ToCSTM.logError "extractTriggerPatterns" "unexpected trigger operation" name.name
      pure #[]
  | _ =>
    -- Single trigger expression
    let expr ← lexprToExpr trigger qLevel
    pure #[expr]

/-- Convert a lambda abstraction to a CoreDDM `fun` expression, reusing the
    prettyName stored in the `abs` constructor as the bound variable name. -/
partial def labsToExpr {M} [Inhabited M]
    (prettyName : String) (ty : Option Lambda.LMonoTy)
    (body : Lambda.LExpr CoreLParams.mono) (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let varName := if prettyName.isEmpty then mkQuantVarName (qLevel - 1) else prettyName
  let name : Ann String M := ⟨default, varName⟩
  modify ToCSTContext.pushScope
  modify (·.addScopedBoundVars #[name.val])
  let tyExpr ← match ty with
    | some t => lmonoTyToCoreType t
    | none => pure (CoreType.tvar default unknownTypeVar)
  let bind := Bind.bind_mk default name ⟨default, none⟩ tyExpr
  let dl := DeclList.declAtom default bind
  let bodyExpr ← lexprToExpr body qLevel
  modify ToCSTContext.popScope
  pure (.lambda default tyExpr dl bodyExpr)

partial def lquantToExpr {M} [Inhabited M]
    (qkind : Lambda.QuantifierKind) (prettyName : String)
    (ty : Option Lambda.LMonoTy)
    (trigger : Lambda.LExpr CoreLParams.mono) (body : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let varName := if prettyName.isEmpty then mkQuantVarName (qLevel - 1) else prettyName
  let name : Ann String M := ⟨default, varName⟩
  modify ToCSTContext.pushScope
  modify (·.addScopedBoundVars #[name.val])
  let tyExpr ← match ty with
    | some t => lmonoTyToCoreType t
    | none => pure (CoreType.tvar default unknownTypeVar)
  let bind := Bind.bind_mk default name ⟨default, none⟩ tyExpr
  let dl := DeclList.declAtom default bind
  let hasNoTrigger := trigger matches .bvar _ 0
  let result ←
    if hasNoTrigger then
      let bodyExpr ← lexprToExpr body qLevel
      match qkind with
      | .all => pure (.forall default dl bodyExpr)
      | .exist => pure (.exists default dl bodyExpr)
    else
      let triggerExprs ← extractTriggerPatterns trigger qLevel
      let bodyExpr ← lexprToExpr body qLevel
      let trigAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, triggerExprs.reverse⟩
      let tg := TriggerGroup.trigger default trigAnn
      let tl := Triggers.triggersAtom default tg
      match qkind with
      | .all => pure (.forallT default dl tl bodyExpr)
      | .exist => pure (.existsT default dl tl bodyExpr)
  modify ToCSTContext.popScope
  pure result

partial def liteToExpr {M} [Inhabited M]
    (c t f : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let cExpr ← lexprToExpr c qLevel
  let tExpr ← lexprToExpr t qLevel
  let fExpr ← lexprToExpr f qLevel
  let ty := CoreType.bool default
  pure (.if default ty cExpr tExpr fExpr)

partial def leqToExpr {M} [Inhabited M]
    (e1 e2 : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat) :
    ToCSTM M (CoreDDM.Expr M) := do
  let e1Expr ← lexprToExpr e1 qLevel
  let e2Expr ← lexprToExpr e2 qLevel
  let ty := CoreType.bool default
  pure (.equal default ty e1Expr e2Expr)

partial def lappToExpr {M} [Inhabited M]
    (e : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let (head, args) := Lambda.getLFuncCall e
  match head with
  | .op _ fn ty =>
    -- `mapConst` (the constant-map builtin) has no inferable key type, so it is
    -- emitted with an explicit key-type annotation `mapConst<K>(v)`. Recover `K`
    -- from the op's function type `V → Map K V`.
    if fn.name == "mapConst" then
      match args with
      | [valArg] =>
        let valCST ← lexprToExpr valArg qLevel
        let kCST ← match ty with
          | some (.tcons "arrow" [_, .tcons "Map" [k, _]]) => lmonoTyToCoreType k
          | some (.tcons "Map" [k, _]) => lmonoTyToCoreType k
          | _ => pure (CoreType.tvar default unknownTypeVar)
        -- The value type is inferred from `v` on re-parse, so a placeholder is fine.
        pure (.map_const default kCST (CoreType.tvar default unknownTypeVar) valCST)
      | _ =>
        let argExprs ← args.mapM (lexprToExpr · qLevel)
        lopToExpr fn.name argExprs
    else
      let argExprs ← args.mapM (lexprToExpr · qLevel)
      lopToExpr fn.name argExprs
  | .app _ fn arg =>
    -- getLFuncCall couldn't decompose further (fn is not .app or .op)
    let fnCST ← lexprToExpr fn qLevel
    let argCST ← lexprToExpr arg qLevel
    let argExprs ← args.mapM (lexprToExpr · qLevel)
    pure <| (argCST :: argExprs).foldl (fun fnAcc a => .app default fnAcc a) fnCST
  | _ =>
    let fnCST ← lexprToExpr head qLevel
    let argExprs ← args.mapM (lexprToExpr · qLevel)
    pure <| argExprs.foldl (fun fnAcc arg => .app default fnAcc arg) fnCST
end

---------------------------------------------------------------------
-- MetadataAnn CST construction
---------------------------------------------------------------------

/-- Convert a MetaData element to a MetadataAnnEntry CST node.
    Returns `none` if the element is filtered out.

    With `annFilter := .all` the goal is to show every element for debugging, so
    we render each value the best the current grammar allows:
    - `.switch true` → a bare flag `@[key]`.
    - `.msg`/`.provenance` → a string value `@[key = "..."]`.
    - `.expr` → a real expression value `@[key = (e)]`, converted via `lexprToExpr`.
    - `.switch false` and `.var` keys have no grammar syntax of their own, so we
      fall back to a readable string so they are still visible. These do not yet
      round-trip on re-parse; a dedicated syntax (e.g. `!key`, `$var`) and the
      parse-side support are follow-up work. -/
def metadataElemToEntry {M} [Inhabited M] (filter : MetadataAnnFilter)
    (elem : Imperative.MetaDataElem Core.Expression) : ToCSTM M (Option (MetadataAnnEntry M)) := do
  -- Var-typed fields have no key syntax of their own, so we render them as
  -- `$name` for visibility (does not round-trip; see follow-up).
  let key := match elem.fld with
    | .label l => l
    | .var v => s!"${v.toPretty}"
  if !filter.shouldEmit key then return none
  let keyCst : MetadataAnnKey M := .mdAnnKeyBare default ⟨default, key⟩
  let strVal (s : String) : MetadataAnnEntry M :=
    .mdAnnKV default keyCst (.mdAnnValStr default ⟨default, s⟩)
  match elem.value with
  | .switch true => return some (.mdAnnFlag default keyCst)
  | .switch false => return some (strVal "false")
  | .msg s => return some (strVal s)
  | .provenance p => return some (strVal (Std.format p).pretty)
  | .expr e =>
    let eCst ← lexprToExpr e 0
    return some (.mdAnnKV default keyCst (.mdAnnValExpr default eCst))

/-- Convert MetaData to an Option MetadataAnn CST annotation.
    Returns none if no emittable metadata is present (or filter is `.none`). -/
def metadataToAnn {M} [Inhabited M]
    (md : Imperative.MetaData Core.Expression)
    (filter : MetadataAnnFilter := .none) : ToCSTM M (Ann (Option (MetadataAnn M)) M) := do
  let entries ← md.filterMapM (metadataElemToEntry (M := M) filter)
  if entries.isEmpty then
    return ⟨default, none⟩
  else
    let annEntries : Ann (Array (MetadataAnnEntry M)) M := ⟨default, entries⟩
    return ⟨default, some (.mdAnn default annEntries)⟩

/-- Convert preconditions to CST spec elements -/
def precondsToSpecElts {M} [Inhabited M]
    (preconds : List (DL.Util.FuncPrecondition
      (Lambda.LExpr CoreLParams.mono) CoreLParams.Metadata))
    : ToCSTM M (Ann (Array (SpecElt M)) M) := do
  let specElts ← preconds.toArray.mapM fun precond => do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, none⟩
    let freeAnn : Ann (Option (Free M)) M := ⟨default, none⟩
    let exprCST ← lexprToExpr precond.expr 0
    pure (SpecElt.requires_spec default labelAnn freeAnn exprCST)
  pure ⟨default, specElts⟩

/-- Build a `TypeArgs` annotation from a list of type parameter names. -/
def mkTypeArgsAnn {M} [Inhabited M] (typeArgs : List String) : Ann (Option (TypeArgs M)) M :=
  if typeArgs.isEmpty then ⟨default, none⟩
  else
    let tvars := typeArgs.map fun tv =>
      TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
    ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩

/-- Convert a function declaration to a statement -/
def funcDeclToStatement {M} [Inhabited M] (annotsAnn : Ann (Option (MetadataAnn M)) M)
    (decl : Imperative.PureFunc Expression)
    : ToCSTM M (CoreDDM.Statement M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, decl.name.name⟩
  let typeArgs := mkTypeArgsAnn decl.typeArgs
  let processInput (id : CoreLParams.Identifier) (ty : Lambda.LTy) :
          ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let results ← decl.inputs.toArray.mapM (fun (id, ty) => processInput id ty)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2)
  let b : Bindings M := .mkBindings default ⟨default, bindings⟩
  let r ← lTyToCoreType decl.output
  let inline? : Ann (Option (Inline M)) M :=
    if decl.attr.any (· == .inline) then ⟨default, some (.inline default)⟩
    else ⟨default, none⟩
  -- Add formals to the context
  modify (·.addScopedBoundVars (reverse? := false) paramNames)
  -- Convert preconditions
  let preconds ← precondsToSpecElts decl.preconditions
  let bodyExpr ← match decl.body with
  | none =>
    -- Dummy expr for the body.
    let bodyExpr := Expr.fvar default (1 + (←get).allFreeVars.size)
    ToCSTM.logError "funcDeclToStatement" "funcDecl without body not supported in statements" name.val
    pure bodyExpr
  | some body => lexprToExpr body 0
  modify ToCSTContext.popScope
  -- Register function name as a scoped bound variable in the parent scope,
  -- matching DDM's @[declareFn] which makes the name a bvar.
  modify (·.pushBoundVar name.val)
  pure (.funcDecl_statement default annotsAnn name typeArgs b r preconds bodyExpr inline?)

/-- Decompose a single-level `map_update(base, idx, val)` where `base` is (or starts
    with) an fvar matching `varName`. Returns `(indices, innerVal)` with indices
    in left-to-right order, or `none` if the expression is not this pattern. -/
private def decomposeMapUpdate (varName : String)
    (e : Lambda.LExpr CoreLParams.mono)
    : Option (List (Lambda.LExpr CoreLParams.mono) × Lambda.LExpr CoreLParams.mono) :=
  let (head, args) := Lambda.getLFuncCall e
  match head, args with
  | .op _ opName _, [base, idx, val] =>
    if opName.name == "update" then
      match base with
      | .fvar _ ident _ =>
        if ident.name == varName then some ([idx], val)
        else none
      | _ => none
    else none
  | _, _ => none

mutual
/-- Convert `Core.Statement` to `CoreDDM.Statement` -/
partial def stmtToCST {M} [Inhabited M] (s : Core.Statement)
    : ToCSTM M (CoreDDM.Statement M) := do
  match s with
  | .init name ty expr md => do
    let nameAnn : Ann String M := ⟨default, name.toPretty⟩
    let tyCST ← lTyToCoreType ty
    let annotsAnn ← metadataToAnn md (← get).annFilter
    let result ← match expr with
    | Imperative.ExprOrNondet.nondet => do
      let bind := Bind.bind_mk default nameAnn
                  ⟨default, none⟩ tyCST
      let dl := DeclList.declAtom default bind
      pure (.varStatement default annotsAnn dl)
    | Imperative.ExprOrNondet.det e =>
      let exprCST ← lexprToExpr e 0
      pure (.initStatement default annotsAnn tyCST nameAnn exprCST)
    -- Push the newly declared variable to the *end of the bound variables
    -- context* so that the most recently declared variable has the lowest
    -- index.
    modify (·.pushBoundVar name.toPretty)
    pure result
  | .set name expr md => do
    -- Detect map_update(name, idx, val) pattern to produce lhsArray syntax
    let (lhs, exprCST) ← match decomposeMapUpdate name.name expr with
      | some (idxs, val) => do
        let baseLhs := Lhs.lhsIdent default ⟨default, name.name⟩
        let lhs ← idxs.foldlM (init := baseLhs) fun acc idx => do
          let idxCST ← lexprToExpr idx 0
          let tyCST := CoreType.tvar default unknownTypeVar
          pure (Lhs.lhsArray default tyCST acc idxCST)
        let valCST ← lexprToExpr val 0
        pure (lhs, valCST)
      | none => do
        let lhs := Lhs.lhsIdent default ⟨default, name.name⟩
        let exprCST ← lexprToExpr expr 0
        pure (lhs, exprCST)
    let tyCST := CoreType.tvar default unknownTypeVar
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.assign default annotsAnn tyCST lhs exprCST)
  | .havoc name md => do
    let nameAnn : Ann String M := ⟨default, name.name⟩
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.havoc_statement default annotsAnn nameAnn)
  | .assert label expr md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.assert default annotsAnn labelAnn exprCST)
  | .assume label expr md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.assume default annotsAnn labelAnn exprCST)
  | .cover label expr md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.cover default annotsAnn labelAnn exprCST)
  | .call pname coreCallArgs md => do
    let pnameAnn : Ann String M := ⟨default, pname⟩
    let mut callArgs : Array (CoreDDM.CallArg M) := #[]
    for a in coreCallArgs do
      match a with
      | .inArg e =>
        let exprCST ← lexprToExpr e 0
        callArgs := callArgs.push (.callArgExpr default exprCST)
      | .inoutArg id =>
        let nameAnn : Ann String M := ⟨default, id.name⟩
        callArgs := callArgs.push (.callArgInout default nameAnn)
      | .outArg id =>
        let nameAnn : Ann String M := ⟨default, id.name⟩
        callArgs := callArgs.push (.callArgOut default nameAnn)
    let callArgsAnn : Ann (Array (CoreDDM.CallArg M)) M := ⟨default, callArgs⟩
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.call_statement default annotsAnn pnameAnn callArgsAnn)
  | .block label stmts md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    let blockCST ← blockToCST stmts
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.block_statement default annotsAnn labelAnn blockCST)
  | .ite cond thenb elseb md => do
    let thenCST ← blockToCST thenb
    let elseCST ← elseToCST elseb
    let annotsAnn ← metadataToAnn md (← get).annFilter
    match cond with
    | .det e =>
      let condCST ← lexprToExpr e 0
      pure (.if_statement default annotsAnn (.condDet default condCST) thenCST elseCST)
    | .nondet =>
      pure (.if_statement default annotsAnn (.condNondet default) thenCST elseCST)
  | .loop guard measure invariant body md => do
    let measureCST ← measureToCST measure
    let invs ← invariantsToCST invariant
    let bodyCST ← blockToCST body
    let annotsAnn ← metadataToAnn md (← get).annFilter
    match guard with
    | .det e =>
      let guardCST ← lexprToExpr e 0
      pure (.while_statement default annotsAnn (.condDet default guardCST) measureCST invs bodyCST)
    | .nondet =>
      pure (.while_statement default annotsAnn (.condNondet default) measureCST invs bodyCST)
  | .exit label md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.exit_statement default annotsAnn labelAnn)
  | .funcDecl decl md =>
    let annotsAnn ← metadataToAnn md (← get).annFilter
    funcDeclToStatement annotsAnn decl
  | .typeDecl tc md =>
    let nameAnn : Ann String M := ⟨default, tc.name⟩
    let args := typeConArgsToCST (M := M) tc
    let annotsAnn ← metadataToAnn md (← get).annFilter
    pure (.typeDecl_statement default annotsAnn nameAnn args)

partial def blockToCST [Inhabited M] (stmts : List Core.Statement)
    : ToCSTM M (CoreDDM.Block M) := do
  modify ToCSTContext.pushScope
  let stmtsCST ← stmts.toArray.mapM stmtToCST
  modify ToCSTContext.popScope
  pure (.block default ⟨default, stmtsCST⟩)

partial def elseToCST {M} [Inhabited M] (stmts : List Core.Statement)
    : ToCSTM M (Else M) := do
  if stmts.isEmpty then
    pure (.else0 default)
  else
    let blockCST ← blockToCST stmts
    pure (.else1 default blockCST)

partial def invariantsToCST {M} [Inhabited M]
    (inv : List (String × Lambda.LExpr CoreLParams.mono)) : ToCSTM M (Invariants M) :=
  match inv with
  | [] => pure (.nilInvariants default)
  | (label, expr) :: rest => do
    -- An empty source label is emitted as `none`; a non-empty label becomes
    -- `some (.label …)`, matching how `assert` / `assume` labels are formatted.
    let labelAnn : Ann (Option (Label M)) M :=
      if label.isEmpty then ⟨default, none⟩
      else ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let restCST ← invariantsToCST rest
    pure (.consInvariants default labelAnn exprCST restCST)

partial def measureToCST {M} [Inhabited M]
    (measure : Option (Lambda.LExpr CoreLParams.mono)) :
    ToCSTM M (Ann (Option (Measure M)) M) := do
  match measure with
  | none => pure ⟨default, none⟩
  | some e =>
    let exprCST ← lexprToExpr e 0
    pure ⟨default, some (.measure_mk default exprCST)⟩
end

/-- Convert a procedure to CST
N.B.: We don't add the procedure name to the freeVars in the context.
-/
private inductive FormatParamKind where
  | inParam | outParam | inoutParam

def procToCST {M} [Inhabited M] (proc : Core.Procedure)
    (md : Imperative.MetaData Core.Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, proc.header.name.toPretty⟩
  let typeArgs := mkTypeArgsAnn proc.header.typeArgs
  let outputSet := proc.header.outputs.toArray.map (·.1)
  let mkBinding' (id : CoreIdent) (ty : Lambda.LMonoTy) (kind : FormatParamKind) :
      ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.toPretty⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := match kind with
      | .outParam => Binding.outBinding default paramName (TypeP.expr paramType)
      | .inoutParam => Binding.inoutBinding default paramName (TypeP.expr paramType)
      | .inParam => Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.toPretty)
  let mut allBindings : Array (Binding M × String) := #[]
  for (id, ty) in proc.header.inputs.toArray do
    let kind := if outputSet.contains id then FormatParamKind.inoutParam else .inParam
    allBindings := allBindings.push (← mkBinding' id ty kind)
  let inoutSet := proc.header.inputs.toArray.map (·.1)
  for (id, ty) in proc.header.outputs.toArray do
    if !inoutSet.contains id then
      allBindings := allBindings.push (← mkBinding' id ty .outParam)
  let allNames := allBindings.map (·.2)
  modify (ToCSTContext.addScopedBoundVars (reverse? := false) · allNames)
  let arguments : Bindings M := .mkBindings default ⟨default, allBindings.map (·.1)⟩
  -- Build spec elements
  let mut specElts : Array (SpecElt M) := #[]
  -- Add requires
  for (label, check) in proc.spec.preconditions.toList do
    let labelAnn : Ann (Option (Label M)) M :=
      ⟨default, some (.label default ⟨default, label⟩)⟩
    let freeAnn : Ann (Option (Free M)) M :=
      if check.attr == .Free then ⟨default, some (.free default)⟩
      else ⟨default, none⟩
    let exprCST ← lexprToExpr check.expr 0
    let reqSpec := SpecElt.requires_spec default labelAnn freeAnn exprCST
    specElts := specElts.push reqSpec
  -- Add ensures
  for (label, check) in proc.spec.postconditions.toList do
    let labelAnn : Ann (Option (Label M)) M :=
      ⟨default, some (.label default ⟨default, label⟩)⟩
    let freeAnn : Ann (Option (Free M)) M :=
      if check.attr == .Free then ⟨default, some (.free default)⟩
      else ⟨default, none⟩
    let exprCST ← lexprToExpr check.expr 0
    let ensSpec := SpecElt.ensures_spec default labelAnn freeAnn exprCST
    specElts := specElts.push ensSpec
  let specAnn : Ann (Array (SpecElt M)) M := ⟨default, specElts⟩
  let spec : Ann (Option (Spec M)) M :=
    if specElts.isEmpty then
      ⟨default, none⟩
    else
      ⟨default, some (Spec.spec_mk default specAnn)⟩
  let bodyStmts ← match proc.body with
    | .structured ss => pure ss
    | .cfg _ => do
        ToCSTM.logError "procToCST" "CFG bodies not yet supported in CST conversion" proc.header.name.toPretty
        pure []
  let bodyCST ← blockToCST bodyStmts
  let body : Ann (Option (CoreDDM.Block M)) M := ⟨default, some bodyCST⟩
  modify ToCSTContext.popScope
  let annotsAnn ← metadataToAnn md (← get).annFilter
  pure (.command_procedure default annotsAnn name typeArgs arguments spec body)

-- Recreate enough of `GlobalContext` from `ToCSTContext` obtained from
-- `programToCST`, purely for formatting.
private def recreateGlobalContext (ctx : ToCSTContext M)
    : GlobalContext :=
  let allFreeVars := ctx.allFreeVars
  let (nameMap, _) := allFreeVars.foldl
    (init := (Std.HashMap.emptyWithCapacity, 0)) fun (map, i) name =>
    (map.insert name i, i + 1)
  let vars := allFreeVars.map fun name =>
    -- .fvar below is really a dummy value.
    (name, GlobalKind.expr (.fvar default 0 #[]))
  { nameMap, vars }

-- Extract types not in `Core.KnownTypes`.
private def extractFromType (ty : Lambda.LMonoTy) : Array String :=
  match ty with
  | .tcons name args =>
    let nameArr := if name ∈ Core.KnownTypes.keys then #[] else #[name]
    nameArr ++ args.foldl (fun acc arg => acc ++ extractFromType arg) #[]
  | .ftvar name => #[name]
  | .bitvec _ => #[]

-- Extract operation and free variable names from expressions.
-- Ignore built-in operations since they are already tackled by `lexprToExpr`.
private def extractNames (exprs : List Core.Expression.Expr) :
    Array String :=
  let rec extractFromExpr (e : Core.Expression.Expr) :=
    match e with
    | .op _ name ty =>
      let opNames := if name.name ∈ builtinFunctions then #[] else #[name.name]
      let tyNames := match ty with | some ty => extractFromType ty | none => #[]
      opNames ++ tyNames
    | .fvar _ id ty =>
      #[id.name] ++ (match ty with | some ty => extractFromType ty | none => #[])
    | .app _ f arg => extractFromExpr f ++ extractFromExpr arg
    | .abs _ _ _ body => extractFromExpr body
    | .ite _ c t f => extractFromExpr c ++ extractFromExpr t ++ extractFromExpr f
    | .eq _ e1 e2 => extractFromExpr e1 ++ extractFromExpr e2
    | .quant _ _ _ _ trigger body => extractFromExpr trigger ++ extractFromExpr body
    | _ => #[]
  exprs.foldl (fun acc expr => acc ++ extractFromExpr expr) #[]

/-- Run the DDM formatting pipeline on a converted CST, appending any conversion errors.
    The optional `fmtErrors` parameter controls how errors are rendered; the default
    appends them on separate lines. -/
def formatWithDDM (finalCtx : ToCSTContext SourceRange)
    (toFormat : FormatContext → FormatState → Std.Format)
    (fmtErrors : Array (ASTToCSTError SourceRange) → Std.Format :=
      fun errs => "\n\n-- Errors encountered during conversion:\n" ++
        Std.Format.joinSep (errs.toList.map (Std.format ∘ toString)) "\n")
    : Std.Format :=
  let dialects := Core_map
  let ddmCtx := recreateGlobalContext finalCtx
  let ctx := FormatContext.ofDialects dialects ddmCtx {}
  let state : FormatState := {
    openDialects := dialects.toList.foldl (init := {})
      fun a (d : Dialect) => a.insert d.name
  }
  let formatted := toFormat ctx state
  if finalCtx.errors.isEmpty then
    formatted
  else
    formatted ++ fmtErrors finalCtx.errors

/-- Render a list of `Core.Expression.Expr` to a format object.

If the expression references constructs not defined in the Grammar,
use `extraFreeVars` to add their names to the formatting context.
-/
def Core.formatExprs (exprs : List Core.Expression.Expr)
    (extraFreeVars : Array String := #[]) : Std.Format :=
  let extractedNames := extractNames exprs
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := initCtx.addGlobalFreeVars (extraFreeVars ++ extractedNames)
  let (exprsCST, finalCtx) := (exprs.mapM (lexprToExpr · 0)).run initCtx
  formatWithDDM finalCtx
    (toFormat := fun ctx state =>
      Std.Format.joinSep (exprsCST.map fun exprCST =>
        (mformat (ArgF.expr exprCST.toAst) ctx state).format) ", ")
    (fmtErrors := fun errs => "\n" ++ "-- Errors: " ++
      Std.Format.joinSep (errs.toList.map (Std.format ∘ toString)) "; ")

/-- Render a `Core.Statement` to a format object using the DDM pretty-printer. -/
def Core.formatStatement (stmt : Core.Statement)
    (extraFreeVars : Array String := #[])
    (annFilter : MetadataAnnFilter := .none) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := { initCtx with annFilter }
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (cst, finalCtx) := stmtToCST stmt initCtx
  formatWithDDM finalCtx fun ctx state =>
    (mformat (ArgF.op cst.toAst) ctx state).format

/-- Render a `Core.Procedure` to a format object using the DDM pretty-printer.

Note: `annFilter` only affects annotations on statements inside the body. The
procedure's own `@[…]` annotation lives on the enclosing `Decl.proc`, not on
`Core.Procedure`, so it is not reachable from this single-proc view; use
`Core.formatProgram` to see it. -/
def Core.formatProcedure (proc : Core.Procedure)
    (extraFreeVars : Array String := #[])
    (annFilter : MetadataAnnFilter := .none) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := { initCtx with annFilter }
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (cst, finalCtx) := (procToCST proc .empty) initCtx
  formatWithDDM finalCtx fun ctx state =>
    (mformat (ArgF.op cst.toAst) ctx state).format

/-- Render a `Core.Command` (`CmdExt Expression`) to a format object using the DDM pretty-printer. -/
def Core.formatCommand (cmd : Core.Command)
    (extraFreeVars : Array String := #[])
    (annFilter : MetadataAnnFilter := .none) : Std.Format :=
  Core.formatStatement (.cmd cmd) extraFreeVars annFilter

/-- Format a single `Core.Expression.Expr` using the DDM pretty-printer. -/
instance instCoreExprFormat : Std.ToFormat Expression.Expr where
  format e := Core.formatExprs [e]

/-- Format a `Core.Procedure` using the DDM pretty-printer. -/
instance instCoreProcedureFormat : Std.ToFormat Procedure where
  format := Core.formatProcedure

/-- Format a `Core.Command` (`CmdExt Expression`) using the DDM pretty-printer. -/
instance instCoreCommandFormat : Std.ToFormat Command where
  format := Core.formatCommand

end ToCST

---------------------------------------------------------------------

end Strata

end -- public section
