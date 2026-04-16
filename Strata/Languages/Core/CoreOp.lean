/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! ## Structured Operator Types for Strata Core

Replaces string-based operator identity with structured types, enabling
compiler-enforced exhaustiveness checking and eliminating typo risks.
-/

namespace Core

public section

/-! ### Bitvector Operations -/

inductive BvOpKind where
  | Neg
  | Add | Sub | Mul | UDiv | UMod | SDiv | SMod
  | Not | And | Or | Xor | Shl | UShr | SShr
  | ULt | ULe | UGt | UGe | SLt | SLe | SGt | SGe
  | Concat
  -- Safe arithmetic (with overflow preconditions)
  | SafeAdd | SafeSub | SafeMul | SafeNeg
  | SafeUAdd | SafeUSub | SafeUMul | SafeUNeg
  | SafeSDiv | SafeSMod
  -- Overflow predicates
  | SAddOverflow | SSubOverflow | SMulOverflow | SNegOverflow | SDivOverflow
  | UAddOverflow | USubOverflow | UMulOverflow | UNegOverflow
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

structure BvOp where
  size : Nat
  kind : BvOpKind
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def BvOpKind.isSigned : BvOpKind → Bool
  | .SDiv | .SMod | .SLt | .SLe | .SGt | .SGe | .SShr
  | .SafeSDiv | .SafeSMod
  | .SAddOverflow | .SSubOverflow | .SMulOverflow | .SNegOverflow | .SDivOverflow => true
  | _ => false

def BvOpKind.isPredicate : BvOpKind → Bool
  | .ULt | .ULe | .UGt | .UGe | .SLt | .SLe | .SGt | .SGe => true
  | _ => false

def BvOpKind.isUnary : BvOpKind → Bool
  | .Neg | .Not => true
  | _ => false

/-! ### Numeric (Int/Real) Operations -/

inductive NumericType where
  | int | real
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

inductive NumericOpKind where
  | Add | Sub | Mul | Neg
  | Div | Mod | DivT | ModT
  | SafeDiv | SafeMod | SafeDivT | SafeModT
  | Lt | Le | Gt | Ge
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

structure NumericOp where
  ty : NumericType
  kind : NumericOpKind
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def NumericOpKind.hasPrecondition : NumericOpKind → Bool
  | .SafeDiv | .SafeMod | .SafeDivT | .SafeModT => true
  | _ => false

def NumericOpKind.isPredicate : NumericOpKind → Bool
  | .Lt | .Le | .Gt | .Ge => true
  | _ => false

def NumericOpKind.isUnary : NumericOpKind → Bool
  | .Neg => true
  | _ => false

/-! ### Boolean Operations -/

inductive BoolOpKind where
  | And | Or | Not | Implies | Equiv
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### String Operations -/

inductive StrOpKind where
  | Length | Concat | Substr | ToRegEx | InRegEx
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### Regular Expression Operations -/

inductive ReOpKind where
  | All | AllChar | Range | Concat | Star | Plus | Loop
  | Union | Inter | Comp | None
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### Map Operations -/

inductive MapOpKind where
  | Const | Select | Update
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### Sequence Operations -/

inductive SeqOpKind where
  | Length | Empty | Append | Select | Build | Update | Contains | Take | Drop
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### Trigger Operations -/

inductive TriggerOpKind where
  | EmptyTriggers | AddGroup | EmptyGroup | AddTrigger
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### Top-level Operator Sum -/

inductive CoreOp where
  | bv (op : BvOp)
  | numeric (op : NumericOp)
  | bool (kind : BoolOpKind)
  | str (kind : StrOpKind)
  | re (kind : ReOpKind)
  | map (kind : MapOpKind)
  | seq (kind : SeqOpKind)
  | bvExtract (size hi lo : Nat)
  | trigger (kind : TriggerOpKind)
  | other (name : String)
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

/-! ### String Conversion -/

def BvOpKind.toString : BvOpKind → String
  | .Neg => "Neg" | .Add => "Add" | .Sub => "Sub" | .Mul => "Mul"
  | .UDiv => "UDiv" | .UMod => "UMod" | .SDiv => "SDiv" | .SMod => "SMod"
  | .Not => "Not" | .And => "And" | .Or => "Or" | .Xor => "Xor"
  | .Shl => "Shl" | .UShr => "UShr" | .SShr => "SShr"
  | .ULt => "ULt" | .ULe => "ULe" | .UGt => "UGt" | .UGe => "UGe"
  | .SLt => "SLt" | .SLe => "SLe" | .SGt => "SGt" | .SGe => "SGe"
  | .Concat => "Concat"
  | .SafeAdd => "SafeAdd" | .SafeSub => "SafeSub"
  | .SafeMul => "SafeMul" | .SafeNeg => "SafeNeg"
  | .SafeUAdd => "SafeUAdd" | .SafeUSub => "SafeUSub"
  | .SafeUMul => "SafeUMul" | .SafeUNeg => "SafeUNeg"
  | .SafeSDiv => "SafeSDiv" | .SafeSMod => "SafeSMod"
  | .SAddOverflow => "SAddOverflow" | .SSubOverflow => "SSubOverflow"
  | .SMulOverflow => "SMulOverflow" | .SNegOverflow => "SNegOverflow"
  | .SDivOverflow => "SDivOverflow"
  | .UAddOverflow => "UAddOverflow" | .USubOverflow => "USubOverflow"
  | .UMulOverflow => "UMulOverflow" | .UNegOverflow => "UNegOverflow"

instance : ToString BvOpKind := ⟨BvOpKind.toString⟩

def BvOpKind.ofString? : String → Option BvOpKind
  | "Neg" => some .Neg | "Add" => some .Add | "Sub" => some .Sub | "Mul" => some .Mul
  | "UDiv" => some .UDiv | "UMod" => some .UMod | "SDiv" => some .SDiv | "SMod" => some .SMod
  | "Not" => some .Not | "And" => some .And | "Or" => some .Or | "Xor" => some .Xor
  | "Shl" => some .Shl | "UShr" => some .UShr | "SShr" => some .SShr
  | "ULt" => some .ULt | "ULe" => some .ULe | "UGt" => some .UGt | "UGe" => some .UGe
  | "SLt" => some .SLt | "SLe" => some .SLe | "SGt" => some .SGt | "SGe" => some .SGe
  | "Concat" => some .Concat
  | "SafeAdd" => some .SafeAdd | "SafeSub" => some .SafeSub
  | "SafeMul" => some .SafeMul | "SafeNeg" => some .SafeNeg
  | "SafeUAdd" => some .SafeUAdd | "SafeUSub" => some .SafeUSub
  | "SafeUMul" => some .SafeUMul | "SafeUNeg" => some .SafeUNeg
  | "SafeSDiv" => some .SafeSDiv | "SafeSMod" => some .SafeSMod
  | "SAddOverflow" => some .SAddOverflow | "SSubOverflow" => some .SSubOverflow
  | "SMulOverflow" => some .SMulOverflow | "SNegOverflow" => some .SNegOverflow
  | "SDivOverflow" => some .SDivOverflow
  | "UAddOverflow" => some .UAddOverflow | "USubOverflow" => some .USubOverflow
  | "UMulOverflow" => some .UMulOverflow | "UNegOverflow" => some .UNegOverflow
  | _ => none

def NumericType.toString : NumericType → String
  | .int => "Int" | .real => "Real"

instance : ToString NumericType := ⟨NumericType.toString⟩

def NumericType.ofString? : String → Option NumericType
  | "Int" => some .int | "Real" => some .real | _ => none

def NumericOpKind.toString : NumericOpKind → String
  | .Add => "Add" | .Sub => "Sub" | .Mul => "Mul" | .Neg => "Neg"
  | .Div => "Div" | .Mod => "Mod" | .DivT => "DivT" | .ModT => "ModT"
  | .SafeDiv => "SafeDiv" | .SafeMod => "SafeMod"
  | .SafeDivT => "SafeDivT" | .SafeModT => "SafeModT"
  | .Lt => "Lt" | .Le => "Le" | .Gt => "Gt" | .Ge => "Ge"

instance : ToString NumericOpKind := ⟨NumericOpKind.toString⟩

def NumericOpKind.ofString? : String → Option NumericOpKind
  | "Add" => some .Add | "Sub" => some .Sub | "Mul" => some .Mul | "Neg" => some .Neg
  | "Div" => some .Div | "Mod" => some .Mod | "DivT" => some .DivT | "ModT" => some .ModT
  | "SafeDiv" => some .SafeDiv | "SafeMod" => some .SafeMod
  | "SafeDivT" => some .SafeDivT | "SafeModT" => some .SafeModT
  | "Lt" => some .Lt | "Le" => some .Le | "Gt" => some .Gt | "Ge" => some .Ge
  | _ => none

def BoolOpKind.toString : BoolOpKind → String
  | .And => "And" | .Or => "Or" | .Not => "Not"
  | .Implies => "Implies" | .Equiv => "Equiv"

instance : ToString BoolOpKind := ⟨BoolOpKind.toString⟩

def BoolOpKind.ofString? : String → Option BoolOpKind
  | "And" => some .And | "Or" => some .Or | "Not" => some .Not
  | "Implies" => some .Implies | "Equiv" => some .Equiv
  | _ => none

def StrOpKind.toString : StrOpKind → String
  | .Length => "Length" | .Concat => "Concat" | .Substr => "Substr"
  | .ToRegEx => "ToRegEx" | .InRegEx => "InRegEx"

instance : ToString StrOpKind := ⟨StrOpKind.toString⟩

def StrOpKind.ofString? : String → Option StrOpKind
  | "Length" => some .Length | "Concat" => some .Concat | "Substr" => some .Substr
  | "ToRegEx" => some .ToRegEx | "InRegEx" => some .InRegEx
  | _ => none

def ReOpKind.toString : ReOpKind → String
  | .All => "All" | .AllChar => "AllChar" | .Range => "Range"
  | .Concat => "Concat" | .Star => "Star" | .Plus => "Plus" | .Loop => "Loop"
  | .Union => "Union" | .Inter => "Inter" | .Comp => "Comp" | .None => "None"

instance : ToString ReOpKind := ⟨ReOpKind.toString⟩

def ReOpKind.ofString? : String → Option ReOpKind
  | "All" => some .All | "AllChar" => some .AllChar | "Range" => some .Range
  | "Concat" => some .Concat | "Star" => some .Star | "Plus" => some .Plus
  | "Loop" => some .Loop | "Union" => some .Union | "Inter" => some .Inter
  | "Comp" => some .Comp | "None" => some .None
  | _ => none

def MapOpKind.toString : MapOpKind → String
  | .Const => "const" | .Select => "select" | .Update => "update"

instance : ToString MapOpKind := ⟨MapOpKind.toString⟩

def MapOpKind.ofString? : String → Option MapOpKind
  | "const" => some .Const | "select" => some .Select | "update" => some .Update
  | _ => none

def SeqOpKind.toString : SeqOpKind → String
  | .Length => "length" | .Empty => "empty" | .Append => "append"
  | .Select => "select" | .Build => "build" | .Update => "update"
  | .Contains => "contains" | .Take => "take" | .Drop => "drop"

instance : ToString SeqOpKind := ⟨SeqOpKind.toString⟩

def SeqOpKind.ofString? : String → Option SeqOpKind
  | "length" => some .Length | "empty" => some .Empty | "append" => some .Append
  | "select" => some .Select | "build" => some .Build | "update" => some .Update
  | "contains" => some .Contains | "take" => some .Take | "drop" => some .Drop
  | _ => none

def TriggerOpKind.toString : TriggerOpKind → String
  | .EmptyTriggers => "Triggers.empty"
  | .AddGroup => "Triggers.addGroup"
  | .EmptyGroup => "TriggerGroup.empty"
  | .AddTrigger => "TriggerGroup.addTrigger"

instance : ToString TriggerOpKind := ⟨TriggerOpKind.toString⟩

def TriggerOpKind.ofString? : String → Option TriggerOpKind
  | "Triggers.empty" => some .EmptyTriggers
  | "Triggers.addGroup" => some .AddGroup
  | "TriggerGroup.empty" => some .EmptyGroup
  | "TriggerGroup.addTrigger" => some .AddTrigger
  | _ => none

/-! ### CoreOp ↔ String Conversion -/

/-- Convert a `CoreOp` to its canonical string name (as used in `Func.name`). -/
def CoreOp.toString : CoreOp → String
  | .bv op => s!"Bv{op.size}.{op.kind}"
  | .numeric op => s!"{op.ty}.{op.kind}"
  | .bool kind => s!"Bool.{kind}"
  | .str kind => s!"Str.{kind}"
  | .re kind => s!"Re.{kind}"
  | .map kind => kind.toString
  | .seq kind => s!"Sequence.{kind}"
  | .bvExtract size hi lo => s!"Bv{size}.Extract_{hi}_{lo}"
  | .trigger kind => kind.toString
  | .other name => name

instance : ToString CoreOp := ⟨CoreOp.toString⟩

/-- Try to parse a BV extract suffix like "Extract_7_0" given a known size. -/
private def parseBvExtract? (size : Nat) (rest : String) : Option CoreOp := do
  guard (rest.startsWith "Extract_")
  let nums := (rest.drop 8).toString.splitOn "_"  -- drop "Extract_"
  match nums with
  | [hiStr, loStr] => do
    let hi ← hiStr.toNat?
    let lo ← loStr.toNat?
    return .bvExtract size hi lo
  | _ => .none

/-- Try to parse a BV op name like "Bv32.Add" or "Bv8.Extract_7_0". -/
private def parseBvOp? (name : String) : Option CoreOp := do
  guard (name.startsWith "Bv")
  let parts := name.splitOn "."
  guard (parts.length == 2)
  let size ← (parts[0]!.drop 2).toNat?
  let rest := parts[1]!
  match BvOpKind.ofString? rest with
  | some kind => return .bv ⟨size, kind⟩
  | none => parseBvExtract? size rest

/-- Parse a string operator name into a structured `CoreOp`.
    Returns `CoreOp.other name` for unrecognized names. -/
def CoreOp.ofString (name : String) : CoreOp :=
  -- Try BV ops: "Bv{size}.{kind}"
  match parseBvOp? name with
  | some op => op
  | none =>
  -- Try numeric ops: "Int.{kind}" or "Real.{kind}"
  let numPrefixes := [("Int.", NumericType.int), ("Real.", NumericType.real)]
  let numResult := numPrefixes.findSome? fun (pfx, ty) =>
    if name.startsWith pfx then
      match NumericOpKind.ofString? (name.drop pfx.length).toString with
      | some kind => some (.numeric ⟨ty, kind⟩)
      | none => none
    else none
  match numResult with
  | some op => op
  | none =>
  -- Try Bool ops
  -- Note: String.drop returns String.Slice in Lean 4.27, so .toString is
  -- needed to convert back to String for the ofString? calls below.
  if name.startsWith "Bool." then
    match BoolOpKind.ofString? (name.drop 5).toString with
    | some kind => .bool kind
    | none => .other name
  -- Try Str ops
  else if name.startsWith "Str." then
    match StrOpKind.ofString? (name.drop 4).toString with
    | some kind => .str kind
    | none => .other name
  -- Try Re ops
  else if name.startsWith "Re." then
    match ReOpKind.ofString? (name.drop 3).toString with
    | some kind => .re kind
    | none => .other name
  -- Try Sequence ops
  else if name.startsWith "Sequence." then
    match SeqOpKind.ofString? (name.drop 9).toString with
    | some kind => .seq kind
    | none => .other name
  -- Try Map ops (no prefix — "const", "select", "update")
  else match MapOpKind.ofString? name with
  | some kind => .map kind
  | none =>
  -- Try Trigger ops
  match TriggerOpKind.ofString? name with
  | some kind => .trigger kind
  | none => .other name

/-- Try to parse a string into a `CoreOp`, returning `none` for unrecognized names. -/
def CoreOp.ofString? (name : String) : Option CoreOp :=
  match CoreOp.ofString name with
  | .other _ => none
  | op => some op

/-! ### Round-trip proofs: ofString? ∘ toString = some

These ensure that toString and ofString? stay in sync for every
constructor of each sub-type. -/

theorem BvOpKind.ofString_toString (k : BvOpKind) :
    BvOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem NumericType.ofString_toString (t : NumericType) :
    NumericType.ofString? t.toString = some t := by cases t <;> decide

theorem NumericOpKind.ofString_toString (k : NumericOpKind) :
    NumericOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem BoolOpKind.ofString_toString (k : BoolOpKind) :
    BoolOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem StrOpKind.ofString_toString (k : StrOpKind) :
    StrOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem ReOpKind.ofString_toString (k : ReOpKind) :
    ReOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem MapOpKind.ofString_toString (k : MapOpKind) :
    MapOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem SeqOpKind.ofString_toString (k : SeqOpKind) :
    SeqOpKind.ofString? k.toString = some k := by cases k <;> decide

theorem TriggerOpKind.ofString_toString (k : TriggerOpKind) :
    TriggerOpKind.ofString? k.toString = some k := by cases k <;> decide

-- TODO: prove CoreOp.ofString (CoreOp.toString op) = op at the composite level.
-- Currently blocked by native_decide being needed for string operations in
-- CoreOp.ofString (splitOn, startsWith). Revisit when Lean gets better
-- kernel-level string reduction.

end -- public section
end Core
