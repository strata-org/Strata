/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DDMTransform.Grammar
public import Strata.Languages.Core.Procedure
public import Strata.DDM.Util.DecimalRat
public import Strata.DDM.Format
public import Strata.Languages.Core.CoreOp

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

Known issues:

- Unsupported constructs (coming soon):
  -- Sub-functions (functions defined inside procedures)

- We do not copy over any metadata in the semantic AST to the CST, including
  source locations. Also, we generate some bound variables' names during
  translation because the semantic AST currently does not preserve them (e.g.,
  bvars in quantifiers). We can log the identifier names during CST -> AST
  translation in the latter's metadata field and recover them in the future.

- Misc. formatting issues
  -- Remove extra parentheses around constructors in datatypes, assignments,
  etc.
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
  deriving Inhabited, Repr

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

/-- Monad for AST->CST conversion with context and error collection -/
@[expose] abbrev ToCSTM (M : Type) := StateM (ToCSTContext M)

/-- Log an error in `ToCSTM` without throwing -/
def ToCSTM.logError {M} [Inhabited M] (fn : String) (desc : String) (detail : String) : ToCSTM M Unit := do
  modify (·.logError fn desc detail)

/-- Render an unknown operation as a generic function call `name(args...)`.
    Registers the name as a free variable if not already registered. -/
def mkGenericCall {M} [Inhabited M] (caller : String) (name : String)
    (args : List (CoreDDM.Expr M)) : ToCSTM M (CoreDDM.Expr M) := do
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
  | .bitvec 1 => pure (.bv1 default)
  | .bitvec 8 => pure (.bv8 default)
  | .bitvec 16 => pure (.bv16 default)
  | .bitvec 32 => pure (.bv32 default)
  | .bitvec 64 => pure (.bv64 default)
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
      let ty := CoreType.tvar default unknownTypeVar
      pure (.neg_expr default ty (.natToInt default ⟨default, n.natAbs⟩))
  | .realConst r =>
    match Strata.Decimal.fromRat r with
    | some d => pure (.realLit default ⟨default, d⟩)
    | none => do
      ToCSTM.logError "lconstToExpr" "unsupported real" (toString r)
      pure (.realLit default ⟨default, default⟩)
  | .strConst s => pure (.strLit default ⟨default, s⟩)
  | .bitvecConst 1 n => pure (.bv1Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 8 n => pure (.bv8Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 16 n => pure (.bv16Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 32 n => pure (.bv32Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 64 n => pure (.bv64Lit default ⟨default, n.toNat⟩)
  | .bitvecConst w _ => do
    ToCSTM.logError "lconstToExpr" "unsupported bitvec width" (toString w)
    pure (.bv64Lit default ⟨default, w⟩)


/-- Handle 0-ary operations -/
def handleZeroaryOps {M} [Inhabited M] (name : String)
    (opTy : Option Lambda.LMonoTy := none)
    : ToCSTM M (CoreDDM.Expr M) :=
  open Core in
  match CoreOp.ofString name with
  | .re .All => pure (.re_all default)
  | .re .AllChar => pure (.re_allchar default)
  | .re .None => pure (.re_none default)
  | .seq .Empty => do
    match opTy with
    | some (.tcons "Sequence" [elemTy]) =>
      let ety ← lmonoTyToCoreType elemTy
      pure (.seq_empty default ety)
    | _ =>
      let ety := CoreType.tvar default unknownTypeVar
      pure (.seq_empty default ety)
  | _ => do
    ToCSTM.logError "lopToExpr" "0-ary op not found" name
    pure (.re_none default)

/-- Handle unary operations -/
def handleUnaryOps {M} [Inhabited M] (name : String) (arg : CoreDDM.Expr M)
    : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  open Core in
  match CoreOp.ofString name with
  | .other "old" => pure (.old default ty arg)
  -- Integers and reals
  | .numeric ⟨_, .Neg⟩ => pure (.neg_expr default ty arg)
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
  -- Bitvector unary ops: enumerated per size because the CST constructors
  -- (.bvnot, .neg_expr) require a concrete type argument. Adding a new BV
  -- width requires adding cases here.
  | .bv ⟨1, .Not⟩ => pure (.bvnot default (.bv1 default) arg)
  | .bv ⟨1, .Neg⟩ => pure (.neg_expr default (.bv1 default) arg)
  | .bv ⟨8, .Not⟩ => pure (.bvnot default (.bv8 default) arg)
  | .bv ⟨8, .Neg⟩ => pure (.neg_expr default (.bv8 default) arg)
  | .bv ⟨16, .Not⟩ => pure (.bvnot default (.bv16 default) arg)
  | .bv ⟨16, .Neg⟩ => pure (.neg_expr default (.bv16 default) arg)
  | .bv ⟨32, .Not⟩ => pure (.bvnot default (.bv32 default) arg)
  | .bv ⟨32, .Neg⟩ => pure (.neg_expr default (.bv32 default) arg)
  | .bv ⟨64, .Not⟩ => pure (.bvnot default (.bv64 default) arg)
  | .bv ⟨64, .Neg⟩ => pure (.neg_expr default (.bv64 default) arg)
  -- Safe negation variants
  | .bv ⟨1, .SafeNeg⟩ | .bv ⟨1, .SafeUNeg⟩ => pure (.safeneg_expr default (.bv1 default) arg)
  | .bv ⟨8, .SafeNeg⟩ | .bv ⟨8, .SafeUNeg⟩ => pure (.safeneg_expr default (.bv8 default) arg)
  | .bv ⟨16, .SafeNeg⟩ | .bv ⟨16, .SafeUNeg⟩ => pure (.safeneg_expr default (.bv16 default) arg)
  | .bv ⟨32, .SafeNeg⟩ | .bv ⟨32, .SafeUNeg⟩ => pure (.safeneg_expr default (.bv32 default) arg)
  | .bv ⟨64, .SafeNeg⟩ | .bv ⟨64, .SafeUNeg⟩ => pure (.safeneg_expr default (.bv64 default) arg)
  -- Overflow predicates: approximated as Bool.Not for CST printing
  | .bv ⟨_, .SNegOverflow⟩ | .bv ⟨_, .UNegOverflow⟩ => pure (.not default arg)
  -- Bitvector extract ops
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

/-- Map from bitvector binary operation kinds to DDM Expr constructors -/
def bvBinaryOpMap {M} [Inhabited M] :
    List (Core.BvOpKind × (CoreType M → CoreDDM.Expr M → CoreDDM.Expr M → CoreDDM.Expr M)) :=
 [
  (.And, fun ty arg1 arg2 => .bvand default ty arg1 arg2),
  (.Or, fun ty arg1 arg2 => .bvor default ty arg1 arg2),
  (.Xor, fun ty arg1 arg2 => .bvxor default ty arg1 arg2),
  (.Add, fun ty arg1 arg2 => .add_expr default ty arg1 arg2),
  (.Sub, fun ty arg1 arg2 => .sub_expr default ty arg1 arg2),
  (.Mul, fun ty arg1 arg2 => .mul_expr default ty arg1 arg2),
  (.UDiv, fun ty arg1 arg2 => .div_expr default ty arg1 arg2),
  (.UMod, fun ty arg1 arg2 => .mod_expr default ty arg1 arg2),
  (.SDiv, fun ty arg1 arg2 => .bvsdiv default ty arg1 arg2),
  (.SMod, fun ty arg1 arg2 => .bvsmod default ty arg1 arg2),
  (.Shl, fun ty arg1 arg2 => .bvshl default ty arg1 arg2),
  (.UShr, fun ty arg1 arg2 => .bvushr default ty arg1 arg2),
  (.SShr, fun ty arg1 arg2 => .bvsshr default ty arg1 arg2),
  (.ULe, fun ty arg1 arg2 => .le default ty arg1 arg2),
  (.ULt, fun ty arg1 arg2 => .lt default ty arg1 arg2),
  (.UGe, fun ty arg1 arg2 => .ge default ty arg1 arg2),
  (.UGt, fun ty arg1 arg2 => .gt default ty arg1 arg2),
  (.SLe, fun ty arg1 arg2 => .bvsle default ty arg1 arg2),
  (.SLt, fun ty arg1 arg2 => .bvslt default ty arg1 arg2),
  (.SGe, fun ty arg1 arg2 => .bvsge default ty arg1 arg2),
  (.SGt, fun ty arg1 arg2 => .bvsgt default ty arg1 arg2),
  -- Safe variants
  (.SafeAdd, fun ty arg1 arg2 => .safeadd_expr default ty arg1 arg2),
  (.SafeSub, fun ty arg1 arg2 => .safesub_expr default ty arg1 arg2),
  (.SafeMul, fun ty arg1 arg2 => .safemul_expr default ty arg1 arg2),
  (.SafeSDiv, fun ty arg1 arg2 => .safesdiv_expr default ty arg1 arg2),
  (.SafeSMod, fun ty arg1 arg2 => .safesmod_expr default ty arg1 arg2),
  (.SafeUAdd, fun ty arg1 arg2 => .safeadd_expr default ty arg1 arg2),
  (.SafeUSub, fun ty arg1 arg2 => .safesub_expr default ty arg1 arg2),
  (.SafeUMul, fun ty arg1 arg2 => .safemul_expr default ty arg1 arg2),
  -- Overflow predicates: approximated as boolean ops for CST printing
  (.SAddOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.SSubOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.SMulOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.SDivOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.UAddOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.USubOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2),
  (.UMulOverflow, fun _ty arg1 arg2 => .le default _ty arg1 arg2)
]

/-- Map from bitvector sizes to their corresponding type constructors -/
def bvTypeMap {M} [Inhabited M] : List (Nat × (CoreType M)) := [
  (1, .bv1 default),
  (8, .bv8 default),
  (16, .bv16 default),
  (32, .bv32 default),
  (64, .bv64 default)
]

/-- Map from bitvector sizes to their corresponding concat operations -/
def bvConcatMap {M} [Inhabited M] :
    List (Nat × (CoreDDM.Expr M → CoreDDM.Expr M → CoreDDM.Expr M)) := [
  (8, fun arg1 arg2 => .bvconcat8 default arg1 arg2),
  (16, fun arg1 arg2 => .bvconcat16 default arg1 arg2),
  (32, fun arg1 arg2 => .bvconcat32 default arg1 arg2)
]

/-- Auto-generated bitvector binary operations handler -/
def handleBitvecBinaryOps {M} [Inhabited M] (name : String) (arg1 arg2 : CoreDDM.Expr M)
    : ToCSTM M (CoreDDM.Expr M) :=
  open Core in
  match CoreOp.ofString name with
  | .bv ⟨size, .Concat⟩ =>
    match (bvConcatMap).find? (·.1 == size) with
    | some (_, concatOp) => pure (concatOp arg1 arg2)
    | none => do
      ToCSTM.logError "handleBitvecBinaryOps" "unsupported concat size" (toString size)
      pure (.bvconcat32 default arg1 arg2)
  | .bv ⟨size, kind⟩ =>
    match (bvTypeMap).find? (·.1 == size) with
    | some (_, ty) =>
      match (bvBinaryOpMap).find? (·.1 == kind) with
      | some (_, op) => pure (op ty arg1 arg2)
      | none => mkGenericCall "handleBitvecBinaryOps" name [arg1, arg2]
    | none => mkGenericCall "handleBitvecBinaryOps" name [arg1, arg2]
  | _ => mkGenericCall "handleBitvecBinaryOps" name [arg1, arg2]

/-- Handle binary operations -/
def handleBinaryOps {M} [Inhabited M] (name : String)
    (arg1 arg2 : CoreDDM.Expr M) : ToCSTM M (CoreDDM.Expr M) :=
  let ty := CoreType.tvar default unknownTypeVar
  open Core in
  match CoreOp.ofString name with
  -- Integer and Real operations
  | .numeric ⟨_, .Add⟩ => pure (.add_expr default ty arg1 arg2)
  | .numeric ⟨_, .Sub⟩ => pure (.sub_expr default ty arg1 arg2)
  | .numeric ⟨_, .Mul⟩ => pure (.mul_expr default ty arg1 arg2)
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.real, .Div⟩ => pure (.div_expr default ty arg1 arg2)
  | .numeric ⟨.int, .SafeDiv⟩ => pure (.safediv_expr default ty arg1 arg2)
  | .numeric ⟨_, .Mod⟩ => pure (.mod_expr default ty arg1 arg2)
  | .numeric ⟨.int, .SafeMod⟩ => pure (.safemod_expr default ty arg1 arg2)
  | .numeric ⟨.int, .DivT⟩ => pure (.divt_expr default ty arg1 arg2)
  | .numeric ⟨.int, .SafeDivT⟩ => pure (.safedivt_expr default ty arg1 arg2)
  | .numeric ⟨.int, .ModT⟩ => pure (.modt_expr default ty arg1 arg2)
  | .numeric ⟨.int, .SafeModT⟩ => pure (.safemodt_expr default ty arg1 arg2)
  | .numeric ⟨_, .Le⟩ => pure (.le default ty arg1 arg2)
  | .numeric ⟨_, .Lt⟩ => pure (.lt default ty arg1 arg2)
  | .numeric ⟨_, .Ge⟩ => pure (.ge default ty arg1 arg2)
  | .numeric ⟨_, .Gt⟩ => pure (.gt default ty arg1 arg2)
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
  | .re .Range => pure (.re_range default arg1 arg2)
  | .re .Concat => pure (.re_concat default arg1 arg2)
  | .re .Union => pure (.re_union default arg1 arg2)
  | .re .Inter => pure (.re_inter default arg1 arg2)
  | _ => handleBitvecBinaryOps name arg1 arg2

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
  | .re .Loop => pure (.re_loop default arg1 arg2 arg3)
  | _ => mkGenericCall "handleTernaryOps" name [arg1, arg2, arg3]

def lopToExpr {M} [Inhabited M]
    (name : String) (args : List (CoreDDM.Expr M))
    (opTy : Option Lambda.LMonoTy := none)
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
    | [] => handleZeroaryOps name opTy
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
  | .op _ name ty => lopToExpr name.name [] ty
  | .app _ _ _ => lappToExpr e qLevel
  | .abs _ prettyName ty body => labsToExpr prettyName ty body (qLevel + 1)
  | .quant _ qkind _ ty trigger body =>
    lquantToExpr qkind ty trigger body (qLevel + 1)

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

/-- Convert a lambda abstraction to a CoreDDM `lambda` expression, reusing the
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
    (qkind : Lambda.QuantifierKind) (ty : Option Lambda.LMonoTy)
    (trigger : Lambda.LExpr CoreLParams.mono) (body : Lambda.LExpr CoreLParams.mono)
    (qLevel : Nat)
    : ToCSTM M (CoreDDM.Expr M) := do
  let name : Ann String M := ⟨default, mkQuantVarName (qLevel - 1)⟩
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
    (qLevel : Nat) (acc : List (CoreDDM.Expr M) := [])
    : ToCSTM M (CoreDDM.Expr M) :=
  match e with
  | .app _ (.app m fn e1) e2 => do
    let e2Expr ← lexprToExpr e2 qLevel
    lappToExpr (.app m fn e1) qLevel (e2Expr :: acc)
  | .app _ (.op _ fn _) e1 => do
    let e1Expr ← lexprToExpr e1 qLevel
    lopToExpr fn.name (e1Expr :: acc)
  | .app _ fn e1 => do
    let fnCST ← lexprToExpr fn qLevel
    let e1Expr ← lexprToExpr e1 qLevel
    pure <| (e1Expr :: acc).foldl (fun fnAcc arg => .app default fnAcc arg) fnCST
  | _ => do
    -- Non-application head (e.g. lambda applied to arguments)
    let eCST ← lexprToExpr e qLevel
    pure <| acc.foldl (fun fnAcc arg => .app default fnAcc arg) eCST
end

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
def funcDeclToStatement {M} [Inhabited M] (decl : Imperative.PureFunc Expression)
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
  let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
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
  pure (.funcDecl_statement default name typeArgs b r preconds bodyExpr inline?)

mutual
/-- Convert `Core.Statement` to `CoreDDM.Statement` -/
partial def stmtToCST {M} [Inhabited M] (s : Core.Statement)
    : ToCSTM M (CoreDDM.Statement M) := do
  match s with
  | .init name ty expr _md => do
    let nameAnn : Ann String M := ⟨default, name.toPretty⟩
    let tyCST ← lTyToCoreType ty
    let result ← match expr with
    | Imperative.ExprOrNondet.nondet => do
      let bind := Bind.bind_mk default nameAnn
                  ⟨default, none⟩ tyCST
      let dl := DeclList.declAtom default bind
      pure (.varStatement default dl)
    | Imperative.ExprOrNondet.det e =>
      let exprCST ← lexprToExpr e 0
      pure (.initStatement default tyCST nameAnn exprCST)
    -- Push the newly declared variable to the *end of the bound variables
    -- context* so that the most recently declared variable has the lowest
    -- index.
    modify (·.pushBoundVar name.toPretty)
    pure result
  | .set name expr _md => do
    let lhs := Lhs.lhsIdent default ⟨default, name.name⟩
    let exprCST ← lexprToExpr expr 0
    -- Type annotation required by CST but not semantically used.
    let tyCST := CoreType.tvar default unknownTypeVar
    pure (.assign default tyCST lhs exprCST)
  | .havoc name _md => do
    let nameAnn : Ann String M := ⟨default, name.name⟩
    pure (.havoc_statement default nameAnn)
  | .assert label expr md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let rcAnn : Ann (Option (ReachCheck M)) M :=
      if Imperative.MetaData.hasReachCheck md then
        ⟨default, some (.reachCheck default)⟩
      else
        ⟨default, none⟩
    pure (.assert default rcAnn labelAnn exprCST)
  | .assume label expr _md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    pure (.assume default labelAnn exprCST)
  | .cover label expr md => do
    let labelAnn := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr 0
    let rcAnn : Ann (Option (ReachCheck M)) M :=
      if Imperative.MetaData.hasReachCheck md then
        ⟨default, some (.reachCheck default)⟩
      else
        ⟨default, none⟩
    pure (.cover default rcAnn labelAnn exprCST)
  | .call pname coreCallArgs _md => do
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
    pure (.call_statement default pnameAnn callArgsAnn)
  | .block label stmts _md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    let blockCST ← blockToCST stmts
    pure (.block_statement default labelAnn blockCST)
  | .ite cond thenb elseb _md => do
    let thenCST ← blockToCST thenb
    let elseCST ← elseToCST elseb
    match cond with
    | .det e =>
      let condCST ← lexprToExpr e 0
      pure (.if_statement default (.condDet default condCST) thenCST elseCST)
    | .nondet =>
      pure (.if_statement default (.condNondet default) thenCST elseCST)
  | .loop guard measure invariant body _md => do
    let measureCST ← measureToCST measure
    let invs ← invariantsToCST invariant
    let bodyCST ← blockToCST body
    match guard with
    | .det e =>
      let guardCST ← lexprToExpr e 0
      pure (.while_statement default (.condDet default guardCST) measureCST invs bodyCST)
    | .nondet =>
      pure (.while_statement default (.condNondet default) measureCST invs bodyCST)
  | .exit label _md => do
    match label with
    | some l =>
      let labelAnn : Ann String M := ⟨default, l⟩
      pure (.exit_statement default labelAnn)
    | none =>
      pure (.exit_unlabeled_statement default)
  | .funcDecl decl _md => funcDeclToStatement decl
  | .typeDecl tc _md =>
    let nameAnn : Ann String M := ⟨default, tc.name⟩
    let args := typeConArgsToCST (M := M) tc
    pure (.typeDecl_statement default nameAnn args)

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
    (inv : List (Lambda.LExpr CoreLParams.mono)) : ToCSTM M (Invariants M) :=
  match inv with
  | [] => pure (.nilInvariants default)
  | expr :: rest => do
    let exprCST ← lexprToExpr expr 0
    let restCST ← invariantsToCST rest
    pure (.consInvariants default exprCST restCST)

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

def procToCST {M} [Inhabited M] (proc : Core.Procedure) : ToCSTM M (Command M) := do
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
  let bodyCST ← blockToCST proc.body
  let body : Ann (Option (CoreDDM.Block M)) M := ⟨default, some bodyCST⟩
  modify ToCSTContext.popScope
  pure (.command_procedure default name typeArgs arguments spec body)

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
    (extraFreeVars : Array String := #[]) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (cst, finalCtx) := stmtToCST stmt initCtx
  formatWithDDM finalCtx fun ctx state =>
    (mformat (ArgF.op cst.toAst) ctx state).format

/-- Render a `Core.Procedure` to a format object using the DDM pretty-printer. -/
def Core.formatProcedure (proc : Core.Procedure)
    (extraFreeVars : Array String := #[]) : Std.Format :=
  let initCtx := ToCSTContext.empty (M := SourceRange)
  let initCtx := initCtx.addGlobalFreeVars extraFreeVars
  let (cst, finalCtx) := procToCST proc initCtx
  formatWithDDM finalCtx fun ctx state =>
    (mformat (ArgF.op cst.toAst) ctx state).format

/-- Render a `Core.Command` (`CmdExt Expression`) to a format object using the DDM pretty-printer. -/
def Core.formatCommand (cmd : Core.Command)
    (extraFreeVars : Array String := #[]) : Std.Format :=
  Core.formatStatement (.cmd cmd) extraFreeVars

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
