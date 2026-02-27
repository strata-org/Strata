/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.Backends.CBMC.GOTO.Expr
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
  -- Bitvector operations: Bv{8,16,32,64}.{Op}
  let bvOp := if fn.startsWith "Bv8." then some (fn.drop 4).toString
    else if fn.startsWith "Bv16." then some (fn.drop 5).toString
    else if fn.startsWith "Bv32." then some (fn.drop 5).toString
    else if fn.startsWith "Bv64." then some (fn.drop 5).toString
    else none
  if let some op := bvOp then
    match op with
    | "Add" => return .multiary .Plus
    | "Sub" => return .binary .Minus
    | "Mul" => return .multiary .Mult
    | "Neg" => return .unary .UnaryMinus
    | "UDiv" => return .binary .Div
    | "UMod" => return .binary .Mod
    | "SDiv" => return .binary .Div
    | "SMod" => return .binary .Mod
    | "Not" => return .unary .Bitnot
    | "And" => return .binary .Bitand
    | "Or" => return .binary .Bitor
    | "Xor" => return .binary .Bitxor
    | "Shl" => return .binary .Shl
    | "UShr" => return .binary .Lshr
    | "SShr" => return .binary .Ashr
    | "Concat" => return .binary .Concatenation
    | "ULt" => return .binary .Lt
    | "ULe" => return .binary .Le
    | "UGt" => return .binary .Gt
    | "UGe" => return .binary .Ge
    | "SLt" => return .binary .Lt
    | "SLe" => return .binary .Le
    | "SGt" => return .binary .Gt
    | "SGe" => return .binary .Ge
    | "Lt" => return .binary .Lt
    | _ =>
      -- Handle Extract_{hi}_{lo} patterns
      if op.startsWith "Extract_" then
        return .binary .Extractbits
      else
        return .functionApplication fn
  else
  match fn with
  -- Integer arithmetic
  | "Int.Add" => .ok (.multiary .Plus)
  | "Int.Sub" => .ok (.binary .Minus)
  | "Int.Mul" => .ok (.multiary .Mult)
  | "Int.DivT" => .ok (.binary .Div)
  | "Int.ModT" => .ok (.binary .Mod)
  | "Int.Div" | "Int.SafeDiv" => .ok (.functionApplication "Int.EuclideanDiv")
  | "Int.Mod" | "Int.SafeMod" => .ok (.functionApplication "Int.EuclideanMod")
  | "Int.Neg" => .ok (.unary .UnaryMinus)
  -- Integer comparisons
  | "Int.Lt" => .ok (.binary .Lt)
  | "Int.Le" => .ok (.binary .Le)
  | "Int.Gt" => .ok (.binary .Gt)
  | "Int.Ge" => .ok (.binary .Ge)
  -- Boolean operations
  | "Bool.And" => .ok (.multiary .And)
  | "Bool.Or" => .ok (.multiary .Or)
  | "Bool.Not" => .ok (.unary .Not)
  | "Bool.Implies" => .ok (.binary .Implies)
  | "Bool.Equiv" => .ok (.binary .Equal)
  -- Real arithmetic
  | "Real.Add" => .ok (.multiary .Plus)
  | "Real.Sub" => .ok (.binary .Minus)
  | "Real.Mul" => .ok (.multiary .Mult)
  | "Real.Div" => .ok (.binary .Div)
  | "Real.Neg" => .ok (.unary .UnaryMinus)
  -- Real comparisons
  | "Real.Lt" => .ok (.binary .Lt)
  | "Real.Le" => .ok (.binary .Le)
  | "Real.Gt" => .ok (.binary .Gt)
  | "Real.Ge" => .ok (.binary .Ge)
  -- Map/array operations
  | "select" => .ok (.binary .Index)
  | "update" => .ok (.ternary .«with»)
  | "Map.const" => .ok (.unary .ArrayOf)
  | _ => .ok (.functionApplication fn)

/-- Parse the lower bit index from a BV Extract function name like "Bv32.Extract_7_0" → some 0 -/
def parseBvExtractLo (fn : String) : Option Nat :=
  if fn.startsWith "Bv8.Extract_" || fn.startsWith "Bv16.Extract_" ||
     fn.startsWith "Bv32.Extract_" || fn.startsWith "Bv64.Extract_" then
    let rev := fn.toList.reverse
    let digits := rev.takeWhile Char.isDigit
    if digits.isEmpty then none
    else (String.ofList digits.reverse).toNat?
  else none

/-- Check if a function name is a signed bitvector operation.
    Signed ops need operands cast to signedbv so CBMC interprets them correctly. -/
private def isSignedBvOp (fn : String) : Bool :=
  let bvOp := if fn.startsWith "Bv8." then some (fn.drop 4).toString
    else if fn.startsWith "Bv16." then some (fn.drop 5).toString
    else if fn.startsWith "Bv32." then some (fn.drop 5).toString
    else if fn.startsWith "Bv64." then some (fn.drop 5).toString
    else none
  match bvOp with
  | some op => op ∈ ["SDiv", "SMod", "SLt", "SLe", "SGt", "SGe", "SShr"]
  | none => false

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
  | .quant _ kind (some ty) _trigger body =>
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
