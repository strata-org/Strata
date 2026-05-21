/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.SemanticsTautschnig

public section

/-! # Concrete Expression Evaluator (Tautschnig port)

Phase-0 port of `tautschnig/goto-semantics`'s `SemanticsEval.lean`.
Lives in `CProverGOTO.SemanticsTautschnig`. The evaluator stays
`partial def` for now; Phase 2.c will revisit. -/

namespace CProverGOTO.SemanticsTautschnig

open CProverGOTO

/-! ## Constant Parsing -/

/-- Parse a GOTO constant string into a Value, given its type. -/
def parseConstant (val : String) (ty : Ty) : Option Value :=
  match ty.id with
  | .primitive .bool =>
    if val == "true" then some (.vBool true)
    else if val == "false" then some (.vBool false)
    else none
  | .primitive .integer => val.toInt?.map .vInt
  | .primitive .string => some (.vString val)
  | .primitive .real => val.toInt?.map (fun n => .vReal n 1)
  | .bitVector (.signedbv w) => val.toInt?.map (.vBV w)
  | .bitVector (.unsignedbv w) => val.toInt?.map (.vBV w)
  | _ => none

/-- Type cast between values. -/
def typeCast (v : Value) (targetTy : Ty) : Option Value :=
  match v, targetTy.id with
  | .vBool b, .primitive .integer => some (.vInt (if b then 1 else 0))
  | .vInt n, .primitive .bool => some (.vBool (n != 0))
  | .vBV _ n, .bitVector (.signedbv w) => some (.vBV w n)
  | .vBV _ n, .bitVector (.unsignedbv w) => some (.vBV w n)
  | .vInt n, .bitVector (.signedbv w) => some (.vBV w n)
  | .vInt n, .bitVector (.unsignedbv w) => some (.vBV w n)
  | _, _ => none

/-! ## Concrete Evaluator -/

/-- Concrete expression evaluator for GOTO expressions.

    Stays `partial def` for now (Phase 2.c will revisit). -/
partial def concreteEval : ExprEval := fun σ e =>
  match e.id, e.operands with
  -- Nullary
  | .nullary (.symbol name), [] => σ name
  | .nullary (.constant val), [] => parseConstant val e.type
  | .nullary .nil, [] => some .vEmpty

  -- Unary
  | .unary .Not, [op] => do
    let .vBool b ← concreteEval σ op | none
    some (.vBool !b)
  | .unary .UnaryMinus, [op] => do
    match ← concreteEval σ op with
    | .vInt n => some (.vInt (-n))
    | .vBV w n => some (.vBV w (-n))
    | _ => none
  | .unary .Typecast, [op] => do
    let v ← concreteEval σ op
    typeCast v e.type

  -- Binary arithmetic
  | .binary .Div, [l, r] => intBinOp (· / ·) σ l r
  | .binary .Mod, [l, r] => intBinOp (· % ·) σ l r
  | .binary .Minus, [l, r] => intBinOp (· - ·) σ l r

  -- Binary comparison
  | .binary .Lt, [l, r] => intCmp (· < ·) σ l r
  | .binary .Le, [l, r] => intCmp (· ≤ ·) σ l r
  | .binary .Gt, [l, r] => intCmp (· > ·) σ l r
  | .binary .Ge, [l, r] => intCmp (· ≥ ·) σ l r
  | .binary .Equal, [l, r] => do
    some (.vBool ((← concreteEval σ l) == (← concreteEval σ r)))
  | .binary .NotEqual, [l, r] => do
    some (.vBool ((← concreteEval σ l) != (← concreteEval σ r)))

  -- Binary logical
  | .binary .Implies, [l, r] => do
    let .vBool a ← concreteEval σ l | none
    let .vBool b ← concreteEval σ r | none
    some (.vBool (!a || b))

  -- Map/array operations
  | .binary .Index, [arr, idx] => do
    let .vArray elems ← concreteEval σ arr | none
    let .vInt i ← concreteEval σ idx | none
    if i < 0 then none else elems[i.toNat]?

  -- Ternary
  | .ternary .ite, [c, t, el] => do
    let .vBool b ← concreteEval σ c | none
    if b then concreteEval σ t else concreteEval σ el
  | .ternary .«with», [arr, idx, val] => do
    let .vArray elems ← concreteEval σ arr | none
    let .vInt i ← concreteEval σ idx | none
    let v ← concreteEval σ val
    if i < 0 then none else
    some (.vArray (elems.set i.toNat v))

  -- Multiary
  | .multiary .And, ops => do
    let vals ← ops.mapM (fun op => do
      match ← concreteEval σ op with
      | .vBool b => pure b
      | _ => none)
    some (.vBool (vals.all id))
  | .multiary .Or, ops => do
    let vals ← ops.mapM (fun op => do
      match ← concreteEval σ op with
      | .vBool b => pure b
      | _ => none)
    some (.vBool (vals.any id))
  | .multiary .Plus, ops => do
    let vals ← ops.mapM (fun op => do
      match ← concreteEval σ op with
      | .vInt n => pure n
      | _ => none)
    some (.vInt (vals.foldl (· + ·) 0))
  | .multiary .Mult, ops => do
    let vals ← ops.mapM (fun op => do
      match ← concreteEval σ op with
      | .vInt n => pure n
      | _ => none)
    some (.vInt (vals.foldl (· * ·) 1))

  -- Unsupported
  | _, _ => none
where
  intBinOp (f : Int → Int → Int) (σ : Store) (l r : Expr) : Option Value := do
    match ← concreteEval σ l, ← concreteEval σ r with
    | .vInt a, .vInt b => some (.vInt (f a b))
    | .vBV w a, .vBV _ b => some (.vBV w (f a b))
    | _, _ => none
  intCmp (f : Int → Int → Bool) (σ : Store) (l r : Expr) : Option Value := do
    match ← concreteEval σ l, ← concreteEval σ r with
    | .vInt a, .vInt b => some (.vBool (f a b))
    | .vBV _ a, .vBV _ b => some (.vBool (f a b))
    | _, _ => none

/-- Two-state concrete evaluator that handles `old()` expressions. -/
partial def concreteEval₂ : ExprEval₂ := fun σ_old σ_cur e =>
  match e.id, e.operands with
  | .unary .Old, [inner] => concreteEval σ_old inner
  | _, _ => concreteEval σ_cur e

end CProverGOTO.SemanticsTautschnig
