/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Lambda
public import Strata.Backends.CBMC.GOTO.Expr
import Strata.Languages.Core.CoreOp

public section
namespace Lambda

/-! # Lambda-to-GOTO expression and type translation

## Known limitations

### Type mapping (`LMonoTy.toGotoType`)
The following types are not yet handled (will return an error):
- `.arrow` — function types
- `.tvar` — type variables
- `.forAll` — polymorphic types

### Expression mapping (`LExprT.toGotoExpr`, `LExpr.toGotoExprCtx`)
The following `LExpr` constructors are not yet handled:
- **`.abs`** — lambda abstractions

The following expression forms are only handled in `toGotoExprCtx` (used for
Core mono-typed expressions) but not in `toGotoExpr` (used for type-inferred
expressions):
- **`.bvar`** — bound variables (de Bruijn indices)
- **`.quant`** — quantified expressions
- **`.ite`** — conditional expressions

### Operator mapping (`fnToGotoID`)
The following Core operators fall through to the `functionApplication` catch-all,
producing uninterpreted function calls in the GOTO output. CBMC may or may not
handle these correctly.

**Integer**: (none — all integer operators are now handled)
**Real**: (none — all real operators are now handled)
**String**: `Str.Concat`, `Str.Length`, `Str.Substr`, `Str.InRegEx`, `Str.ToRegEx`
  (intentionally left as function applications for the CBMC string solver patch)
**Bitvector**: `Bv{8,16,32,64}.Extract_{hi}_{lo}` maps to GOTO `extractbits`; the
  lower bit index is parsed from the operator name and emitted as a constant operand.
**Map**: `Map.const`
**Regex**: `Re.All`, `Re.AllChar`, `Re.Comp`, `Re.Concat`, `Re.Inter`,
  `Re.Loop`, `Re.None`, `Re.Plus`, `Re.Range`, `Re.Star`, `Re.Union`
-/
open Std (ToFormat Format format)
-------------------------------------------------------------------------------
def LMonoTy.toGotoType (ty : LMonoTy) : Except Format CProverGOTO.Ty :=
  match ty with
  | .bitvec n => .ok (CProverGOTO.Ty.UnsignedBV n)
  | .int => .ok .Integer
  | .bool => .ok .Boolean
  | .string => .ok .String
  | .real => .ok .Real
  | .tcons "regex" [] => .ok .Regex
  | .tcons "Map" [_, vty] => do
    let elemTy ← toGotoType vty
    .ok (CProverGOTO.Ty.Array elemTy)
  | .tcons "arrow" _ => .error f!"[toGotoType] Function types not supported in GOTO translation"
  | .tcons name _ => .ok (CProverGOTO.Ty.StructTag name)
  | _ => .error f!"[toGotoType] Not yet implemented: {ty}"

def LExprT.getGotoType {T : LExprParamsT} (e : LExprT T) :
    Except Format CProverGOTO.Ty := do
  let ty := LExpr.toLMonoTy e
  ty.toGotoType


def fnToGotoID (fn : String) : Except Format CProverGOTO.Expr.Identifier :=
  open Core in
  match CoreOp.ofString fn with
  -- Bitvector operations
  | .bv ⟨_, .Add⟩ | .bv ⟨_, .SafeAdd⟩ | .bv ⟨_, .SafeUAdd⟩ => .ok (.multiary .Plus)
  | .bv ⟨_, .Sub⟩ | .bv ⟨_, .SafeSub⟩ | .bv ⟨_, .SafeUSub⟩ => .ok (.binary .Minus)
  | .bv ⟨_, .Mul⟩ | .bv ⟨_, .SafeMul⟩ | .bv ⟨_, .SafeUMul⟩ => .ok (.multiary .Mult)
  | .bv ⟨_, .Neg⟩ | .bv ⟨_, .SafeNeg⟩ | .bv ⟨_, .SafeUNeg⟩ => .ok (.unary .UnaryMinus)
  | .bv ⟨_, .UDiv⟩ | .bv ⟨_, .SDiv⟩ | .bv ⟨_, .SafeSDiv⟩ => .ok (.binary .Div)
  | .bv ⟨_, .UMod⟩ | .bv ⟨_, .SMod⟩ | .bv ⟨_, .SafeSMod⟩ => .ok (.binary .Mod)
  | .bv ⟨_, .Not⟩ => .ok (.unary .Bitnot)
  | .bv ⟨_, .And⟩ => .ok (.binary .Bitand)
  | .bv ⟨_, .Or⟩ => .ok (.binary .Bitor)
  | .bv ⟨_, .Xor⟩ => .ok (.binary .Bitxor)
  | .bv ⟨_, .Shl⟩ => .ok (.binary .Shl)
  | .bv ⟨_, .UShr⟩ => .ok (.binary .Lshr)
  | .bv ⟨_, .SShr⟩ => .ok (.binary .Ashr)
  | .bv ⟨_, .Concat⟩ => .ok (.binary .Concatenation)
  | .bv ⟨_, .ULt⟩ | .bv ⟨_, .SLt⟩ => .ok (.binary .Lt)
  | .bv ⟨_, .ULe⟩ | .bv ⟨_, .SLe⟩ => .ok (.binary .Le)
  | .bv ⟨_, .UGt⟩ | .bv ⟨_, .SGt⟩ => .ok (.binary .Gt)
  | .bv ⟨_, .UGe⟩ | .bv ⟨_, .SGe⟩ => .ok (.binary .Ge)
  | .bvExtract .. => .ok (.binary .Extractbits)
  -- Overflow predicates
  | .bv ⟨_, .SAddOverflow⟩ | .bv ⟨_, .UAddOverflow⟩ => .ok (.binary .PlusOverflow)
  | .bv ⟨_, .SSubOverflow⟩ | .bv ⟨_, .USubOverflow⟩ => .ok (.binary .MinusOverflow)
  | .bv ⟨_, .SMulOverflow⟩ | .bv ⟨_, .UMulOverflow⟩ => .ok (.binary .MultOverflow)
  | .bv ⟨_, .SNegOverflow⟩ | .bv ⟨_, .UNegOverflow⟩ => .ok (.unary .UnaryMinusOverflow)
  | .bv ⟨_, .SDivOverflow⟩ => .ok (.functionApplication "SDivOverflow")
  -- Integer arithmetic
  | .numeric ⟨.int, .Add⟩ => .ok (.multiary .Plus)
  | .numeric ⟨.int, .Sub⟩ => .ok (.binary .Minus)
  | .numeric ⟨.int, .Mul⟩ => .ok (.multiary .Mult)
  | .numeric ⟨.int, .DivT⟩ | .numeric ⟨.int, .SafeDivT⟩ => .ok (.binary .Div)
  | .numeric ⟨.int, .ModT⟩ | .numeric ⟨.int, .SafeModT⟩ => .ok (.binary .Mod)
  | .numeric ⟨.int, .Div⟩ | .numeric ⟨.int, .SafeDiv⟩ =>
    .ok (.functionApplication "Int.EuclideanDiv")
  | .numeric ⟨.int, .Mod⟩ | .numeric ⟨.int, .SafeMod⟩ =>
    .ok (.functionApplication "Int.EuclideanMod")
  | .numeric ⟨.int, .Neg⟩ => .ok (.unary .UnaryMinus)
  | .numeric ⟨.int, .Lt⟩ => .ok (.binary .Lt)
  | .numeric ⟨.int, .Le⟩ => .ok (.binary .Le)
  | .numeric ⟨.int, .Gt⟩ => .ok (.binary .Gt)
  | .numeric ⟨.int, .Ge⟩ => .ok (.binary .Ge)
  -- Boolean operations
  | .bool .And => .ok (.multiary .And)
  | .bool .Or => .ok (.multiary .Or)
  | .bool .Not => .ok (.unary .Not)
  | .bool .Implies => .ok (.binary .Implies)
  | .bool .Equiv => .ok (.binary .Equal)
  -- Real arithmetic
  | .numeric ⟨.real, .Add⟩ => .ok (.multiary .Plus)
  | .numeric ⟨.real, .Sub⟩ => .ok (.binary .Minus)
  | .numeric ⟨.real, .Mul⟩ => .ok (.multiary .Mult)
  | .numeric ⟨.real, .Div⟩ => .ok (.binary .Div)
  | .numeric ⟨.real, .Neg⟩ => .ok (.unary .UnaryMinus)
  | .numeric ⟨.real, .Lt⟩ => .ok (.binary .Lt)
  | .numeric ⟨.real, .Le⟩ => .ok (.binary .Le)
  | .numeric ⟨.real, .Gt⟩ => .ok (.binary .Gt)
  | .numeric ⟨.real, .Ge⟩ => .ok (.binary .Ge)
  -- Map/array operations
  | .map .Select => .ok (.binary .Index)
  | .map .Update => .ok (.ternary .«with»)
  | .map .Const => .ok (.unary .ArrayOf)
  -- Everything else (strings, regex, sequences, user-defined, etc.)
  | _ => .ok (.functionApplication fn)

/-- Parse the lower bit index from a BV Extract operator. -/
def parseBvExtractLo (fn : String) : Option Nat :=
  open Core in
  match CoreOp.ofString fn with
  | .bvExtract _ _ lo => some lo
  | _ => none

/-- Check if a function name is a signed bitvector operation.
    Signed ops need operands cast to signedbv so CBMC interprets them correctly. -/
private def isSignedBvOp (fn : String) : Bool :=
  open Core in
  match CoreOp.ofString fn with
  | .bv ⟨_, kind⟩ => kind.isSigned
  | _ => false

/-- Build SDivOverflow(x, y) = (x == INT_MIN) && (y == -1) for signed bitvectors. -/
private def mkSDivOverflow (x y : CProverGOTO.Expr) : CProverGOTO.Expr :=
  open CProverGOTO in
  open CProverGOTO.Ty in
  let bvTy := x.type
  let width := match bvTy.id with
    | .bitVector (.signedbv n) | .bitVector (.unsignedbv n) => n | _ => 32
  let intMinVal := (2 ^ (width - 1)).repr
  let intMin := Expr.constant intMinVal bvTy
  let negOneVal := (2 ^ width - 1).repr
  let negOne := Expr.constant negOneVal bvTy
  let xIsMin : Expr := { id := .binary .Equal, type := .Boolean, operands := [x, intMin] }
  let yIsNegOne : Expr := { id := .binary .Equal, type := .Boolean, operands := [y, negOne] }
  { id := .multiary .And, type := .Boolean, operands := [xIsMin, yIsNegOne] }

/-- Build Euclidean division from truncating division:
    ediv(a, b) = tdiv(a, b) + ite(tmod(a, b) < 0, ite(b > 0, -1, 1), 0) -/
private def mkEuclideanDiv (a b : CProverGOTO.Expr) : CProverGOTO.Expr :=
  open CProverGOTO in
  let zero := Expr.constant "0" .Integer
  let one := Expr.constant "1" .Integer
  let neg1 := Expr.neg one
  let tdiv := Expr.div a b
  let tmod := Expr.mod a b
  let modNeg : Expr := { id := .binary .Lt, type := .Boolean, operands := [tmod, zero] }
  let bPos : Expr := { id := .binary .Gt, type := .Boolean, operands := [b, zero] }
  let adjust : Expr := { id := .ternary .ite, type := .Integer, operands := [bPos, neg1, one] }
  let correction : Expr := { id := .ternary .ite, type := .Integer, operands := [modNeg, adjust, zero] }
  { id := .multiary .Plus, type := .Integer, operands := [tdiv, correction] }

/-- Build Euclidean modulo from truncating modulo:
    emod(a, b) = tmod(a, b) + ite(tmod(a, b) < 0, ite(b > 0, b, -b), 0) -/
private def mkEuclideanMod (a b : CProverGOTO.Expr) : CProverGOTO.Expr :=
  open CProverGOTO in
  let zero := Expr.constant "0" .Integer
  let tmod := Expr.mod a b
  let modNeg : Expr := { id := .binary .Lt, type := .Boolean, operands := [tmod, zero] }
  let bPos : Expr := { id := .binary .Gt, type := .Boolean, operands := [b, zero] }
  let absB : Expr := { id := .ternary .ite, type := .Integer, operands := [bPos, b, Expr.neg b] }
  let correction : Expr := { id := .ternary .ite, type := .Integer, operands := [modNeg, absB, zero] }
  { id := .multiary .Plus, type := .Integer, operands := [tmod, correction] }

def LExprT.toGotoExpr {TBase: LExprParamsT} [ToString TBase.base.IDMeta] (e : LExprT TBase) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const m c =>
    let gty ← m.type.toGotoType
    return (Expr.constant (toString c) gty)
  -- Variables
  | .fvar m v _ =>
    let gty ← m.type.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Ternary Functions
  | .app m (.app _ (.app _ (.op _ fn _) e1) e2) e3 =>
    let op ← fnToGotoID (toString fn)
    let gty ← m.type.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    let e3g ← toGotoExpr e3
    return { id := op, type := gty, operands := [e1g, e2g, e3g] }
  -- Binary Functions
  | .app m (.app _ (.op _ fn _) e1) e2 =>
    let fnStr := toString fn
    let op ← fnToGotoID fnStr
    let gty ← m.type.toGotoType
    let mut e1g ← toGotoExpr e1
    let mut e2g ← toGotoExpr e2
    -- Euclidean div/mod: expand sentinel into compound expression
    if op == .functionApplication "Int.EuclideanDiv" then return mkEuclideanDiv e1g e2g
    if op == .functionApplication "Int.EuclideanMod" then return mkEuclideanMod e1g e2g
    if op == .functionApplication "SDivOverflow" then return mkSDivOverflow e1g e2g
    -- Signed BV ops: cast operands to signedbv
    if isSignedBvOp fnStr then
      e1g := e1g.toSigned
      e2g := e2g.toSigned
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app m (.op _ fn _) e1 =>
    let fnStr := toString fn
    -- BV Extract: unary in Core, binary (src, index) in GOTO
    if let some lo := parseBvExtractLo fnStr then
      let gty ← m.type.toGotoType
      let e1g ← toGotoExpr e1
      let idxExpr := Expr.constant (toString lo) (.Integer)
      return { id := .binary .Extractbits, type := gty, operands := [e1g, idxExpr] }
    else
      let op ← fnToGotoID fnStr
      let gty ← m.type.toGotoType
      let e1g ← toGotoExpr e1
      return { id := op, type := gty, operands := [e1g] }
  -- Nullary Functions (e.g., datatype constructors with no arguments)
  | .op m fn _ =>
    let op ← fnToGotoID (toString fn)
    let gty ← m.type.toGotoType
    return { id := op, type := gty, operands := [] }
  -- Equality
  | .eq _ e1 e2 =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {e}"

/--
Mapping `LExpr` to GOTO expressions (for LMonoTy-typed expressions).
Accepts a bound variable context for de Bruijn indices (innermost binding first).
-/
def LExpr.toGotoExprCtx {TBase: LExprParams} [ToString $ LExpr TBase.mono]
    (bvars : List (String × CProverGOTO.Ty)) (e : LExpr TBase.mono) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const _ c  =>
    let gty ← c.ty.toGotoType
    return (Expr.constant (toString c) gty)
  -- Variables
  | .fvar _ v (some ty) =>
    let gty ← ty.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Bound variables (de Bruijn index)
  | .bvar _ n =>
    match bvars[n]? with
    | some (name, ty) => return (Expr.symbol name ty)
    | none => .error f!"[toGotoExprCtx] Unbound variable index {n}"
  -- Ternary Functions (must come before Binary to match longest pattern first)
  | .app _ (.app _ (.app _ (.op _ fn (some ty)) e1) e2) e3 =>
    let op ← fnToGotoID (toString fn)
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let e1g ← toGotoExprCtx bvars e1
    let e2g ← toGotoExprCtx bvars e2
    let e3g ← toGotoExprCtx bvars e3
    return { id := op, type := gty, operands := [e1g, e2g, e3g] }
  -- Binary Functions
  | .app _ (.app _ (.op _ fn (some ty)) e1) e2 =>
    let fnStr := toString fn
    -- old(expr): polymorphic, first arg is type, second is the actual expression
    if fnStr == "old" then
      let retty := ty.destructArrow.getLast!
      let gty ← retty.toGotoType
      let e2g ← toGotoExprCtx bvars e2
      return { id := .unary .Old, type := gty, operands := [e2g] }
    else
    let op ← fnToGotoID fnStr
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let mut e1g ← toGotoExprCtx bvars e1
    let mut e2g ← toGotoExprCtx bvars e2
    -- Euclidean div/mod: expand sentinel into compound expression
    if op == .functionApplication "Int.EuclideanDiv" then return mkEuclideanDiv e1g e2g
    if op == .functionApplication "Int.EuclideanMod" then return mkEuclideanMod e1g e2g
    if op == .functionApplication "SDivOverflow" then return mkSDivOverflow e1g e2g
    -- Signed BV ops: cast operands to signedbv
    if isSignedBvOp fnStr then
      e1g := e1g.toSigned
      e2g := e2g.toSigned
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app _ (.op _ fn (some ty)) e1 =>
    let fnStr := toString fn
    -- BV Extract: unary in Core, binary (src, index) in GOTO
    if let some lo := parseBvExtractLo fnStr then
      let retty := ty.destructArrow.getLast!
      let gty ← retty.toGotoType
      let e1g ← toGotoExprCtx bvars e1
      let idxExpr := Expr.constant (toString lo) (.Integer)
      return { id := .binary .Extractbits, type := gty, operands := [e1g, idxExpr] }
    else
      let op ← fnToGotoID fnStr
      let retty := ty.destructArrow.getLast!
      let gty ← retty.toGotoType
      let e1g ← toGotoExprCtx bvars e1
      return { id := op, type := gty, operands := [e1g] }
  -- Nullary Functions (e.g., datatype constructors with no arguments)
  | .op _ fn (some ty) =>
    let op ← fnToGotoID (toString fn)
    let gty ← ty.toGotoType
    return { id := op, type := gty, operands := [] }
  -- Equality
  | .eq _ e1 e2 =>
    let e1g ← toGotoExprCtx bvars e1
    let e2g ← toGotoExprCtx bvars e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  -- Quantifiers
  | .quant _ kind _name (some ty) _trigger body =>
    let gty ← ty.toGotoType
    let qname := s!"__quant_var_{bvars.length}"
    let boundVar := Expr.symbol qname gty
    let bodyG ← toGotoExprCtx ((qname, gty) :: bvars) body
    let qop := match kind with
      | .all => Expr.Identifier.binary .Forall
      | .exist => Expr.Identifier.binary .Exists
    return { id := qop, type := .Boolean, operands := [boundVar, bodyG] }
  -- Conditionals
  | .ite _ c t e =>
    let cg ← toGotoExprCtx bvars c
    let tg ← toGotoExprCtx bvars t
    let eg ← toGotoExprCtx bvars e
    return (Expr.ite cg tg eg)
  | _ => .error f!"[toGotoExprCtx] Not yet implemented: {toString e}"

/--
Mapping `LExpr` to GOTO expressions (for LMonoTy-typed expressions).
-/
def LExpr.toGotoExpr {TBase: LExprParams} [ToString $ LExpr TBase.mono] (e : LExpr TBase.mono) :
    Except Format CProverGOTO.Expr :=
  toGotoExprCtx [] e

end Lambda
