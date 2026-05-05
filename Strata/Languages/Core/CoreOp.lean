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

/-! ### Table-driven name lookup

Each OpKind type defines a `names` list as the single source of truth
mapping constructors to their string representations. Both `toString`
and `ofString?` are derived from this list, and round-trip correctness
is proved by `decide`. -/

/-- Look up the string name for a constructor. The names lists are small
    (≤43 entries), so linear scan is negligible. Using List.find? rather than
    a HashMap is intentional: it enables the kernel to reduce these functions,
    which is required for the round-trip `decide` proofs below. -/
private def lookupName [BEq α] (names : List (α × String)) (k : α) : String :=
  match names.find? (·.1 == k) with
  | some (_, s) => s
  | none => "" -- unreachable: round-trip proofs guarantee completeness of names

private def lookupKind [BEq β] (names : List (α × β)) (s : β) : Option α :=
  match names.find? (·.2 == s) with
  | some (k, _) => some k
  | none => none

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

def BvOpKind.names : List (BvOpKind × String) :=
  [(.Neg, "Neg"), (.Add, "Add"), (.Sub, "Sub"), (.Mul, "Mul"),
   (.UDiv, "UDiv"), (.UMod, "UMod"), (.SDiv, "SDiv"), (.SMod, "SMod"),
   (.Not, "Not"), (.And, "And"), (.Or, "Or"), (.Xor, "Xor"),
   (.Shl, "Shl"), (.UShr, "UShr"), (.SShr, "SShr"),
   (.ULt, "ULt"), (.ULe, "ULe"), (.UGt, "UGt"), (.UGe, "UGe"),
   (.SLt, "SLt"), (.SLe, "SLe"), (.SGt, "SGt"), (.SGe, "SGe"),
   (.Concat, "Concat"),
   (.SafeAdd, "SafeAdd"), (.SafeSub, "SafeSub"),
   (.SafeMul, "SafeMul"), (.SafeNeg, "SafeNeg"),
   (.SafeUAdd, "SafeUAdd"), (.SafeUSub, "SafeUSub"),
   (.SafeUMul, "SafeUMul"), (.SafeUNeg, "SafeUNeg"),
   (.SafeSDiv, "SafeSDiv"), (.SafeSMod, "SafeSMod"),
   (.SAddOverflow, "SAddOverflow"), (.SSubOverflow, "SSubOverflow"),
   (.SMulOverflow, "SMulOverflow"), (.SNegOverflow, "SNegOverflow"),
   (.SDivOverflow, "SDivOverflow"),
   (.UAddOverflow, "UAddOverflow"), (.USubOverflow, "USubOverflow"),
   (.UMulOverflow, "UMulOverflow"), (.UNegOverflow, "UNegOverflow")]

def BvOpKind.toString (k : BvOpKind) : String := lookupName names k
instance : ToString BvOpKind := ⟨BvOpKind.toString⟩
def BvOpKind.ofString? (s : String) : Option BvOpKind := lookupKind names s

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

def NumericType.names : List (NumericType × String) :=
  [(.int, "Int"), (.real, "Real")]

def NumericType.toString (t : NumericType) : String := lookupName names t
instance : ToString NumericType := ⟨NumericType.toString⟩
def NumericType.ofString? (s : String) : Option NumericType := lookupKind names s

def NumericOpKind.names : List (NumericOpKind × String) :=
  [(.Add, "Add"), (.Sub, "Sub"), (.Mul, "Mul"), (.Neg, "Neg"),
   (.Div, "Div"), (.Mod, "Mod"), (.DivT, "DivT"), (.ModT, "ModT"),
   (.SafeDiv, "SafeDiv"), (.SafeMod, "SafeMod"),
   (.SafeDivT, "SafeDivT"), (.SafeModT, "SafeModT"),
   (.Lt, "Lt"), (.Le, "Le"), (.Gt, "Gt"), (.Ge, "Ge")]

def NumericOpKind.toString (k : NumericOpKind) : String := lookupName names k
instance : ToString NumericOpKind := ⟨NumericOpKind.toString⟩
def NumericOpKind.ofString? (s : String) : Option NumericOpKind := lookupKind names s

/-! ### Boolean Operations -/

inductive BoolOpKind where
  | And | Or | Not | Implies | Equiv
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def BoolOpKind.names : List (BoolOpKind × String) :=
  [(.And, "And"), (.Or, "Or"), (.Not, "Not"),
   (.Implies, "Implies"), (.Equiv, "Equiv")]

def BoolOpKind.toString (k : BoolOpKind) : String := lookupName names k
instance : ToString BoolOpKind := ⟨BoolOpKind.toString⟩
def BoolOpKind.ofString? (s : String) : Option BoolOpKind := lookupKind names s

/-! ### String Operations -/

inductive StrOpKind where
  | Length | Concat | Substr | ToRegEx | InRegEx | PrefixOf | SuffixOf
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def StrOpKind.names : List (StrOpKind × String) :=
  [(.Length, "Length"), (.Concat, "Concat"), (.Substr, "Substr"),
   (.ToRegEx, "ToRegEx"), (.InRegEx, "InRegEx"),
   (.PrefixOf, "PrefixOf"), (.SuffixOf, "SuffixOf")]

def StrOpKind.toString (k : StrOpKind) : String := lookupName names k
instance : ToString StrOpKind := ⟨StrOpKind.toString⟩
def StrOpKind.ofString? (s : String) : Option StrOpKind := lookupKind names s

/-! ### Regular Expression Operations -/

inductive ReOpKind where
  | All | AllChar | Range | Concat | Star | Plus | Loop
  | Union | Inter | Comp | None
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def ReOpKind.names : List (ReOpKind × String) :=
  [(.All, "All"), (.AllChar, "AllChar"), (.Range, "Range"),
   (.Concat, "Concat"), (.Star, "Star"), (.Plus, "Plus"), (.Loop, "Loop"),
   (.Union, "Union"), (.Inter, "Inter"), (.Comp, "Comp"), (.None, "None")]

def ReOpKind.toString (k : ReOpKind) : String := lookupName names k
instance : ToString ReOpKind := ⟨ReOpKind.toString⟩
def ReOpKind.ofString? (s : String) : Option ReOpKind := lookupKind names s

/-! ### Map Operations -/

inductive MapOpKind where
  | Const | Select | Update
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def MapOpKind.names : List (MapOpKind × String) :=
  [(.Const, "const"), (.Select, "select"), (.Update, "update")]

def MapOpKind.toString (k : MapOpKind) : String := lookupName names k
instance : ToString MapOpKind := ⟨MapOpKind.toString⟩
def MapOpKind.ofString? (s : String) : Option MapOpKind := lookupKind names s

/-! ### Sequence Operations -/

inductive SeqOpKind where
  | Length | Empty | Append | Select | Build | Update | Contains | Take | Drop
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def SeqOpKind.names : List (SeqOpKind × String) :=
  [(.Length, "length"), (.Empty, "empty"), (.Append, "append"),
   (.Select, "select"), (.Build, "build"), (.Update, "update"),
   (.Contains, "contains"), (.Take, "take"), (.Drop, "drop")]

def SeqOpKind.toString (k : SeqOpKind) : String := lookupName names k
instance : ToString SeqOpKind := ⟨SeqOpKind.toString⟩
def SeqOpKind.ofString? (s : String) : Option SeqOpKind := lookupKind names s

/-! ### Trigger Operations -/

inductive TriggerOpKind where
  | EmptyTriggers | AddGroup | EmptyGroup | AddTrigger
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

def TriggerOpKind.names : List (TriggerOpKind × String) :=
  [(.EmptyTriggers, "Triggers.empty"), (.AddGroup, "Triggers.addGroup"),
   (.EmptyGroup, "TriggerGroup.empty"), (.AddTrigger, "TriggerGroup.addTrigger")]

def TriggerOpKind.toString (k : TriggerOpKind) : String := lookupName names k
instance : ToString TriggerOpKind := ⟨TriggerOpKind.toString⟩
def TriggerOpKind.ofString? (s : String) : Option TriggerOpKind := lookupKind names s

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
  -- Note: String.drop returns String.Slice, so .toString is needed to
  -- convert back to String for the ofString? calls below.
  if name.startsWith "Bool." then
    match BoolOpKind.ofString? (name.drop 5).toString with
    | some kind => .bool kind
    | none => .other name
  else if name.startsWith "Str." then
    match StrOpKind.ofString? (name.drop 4).toString with
    | some kind => .str kind
    | none => .other name
  else if name.startsWith "Re." then
    match ReOpKind.ofString? (name.drop 3).toString with
    | some kind => .re kind
    | none => .other name
  else if name.startsWith "Sequence." then
    match SeqOpKind.ofString? (name.drop 9).toString with
    | some kind => .seq kind
    | none => .other name
  else match MapOpKind.ofString? name with
  | some kind => .map kind
  | none =>
  match TriggerOpKind.ofString? name with
  | some kind => .trigger kind
  | none => .other name

/-- Try to parse a string into a `CoreOp`, returning `none` for unrecognized names. -/
def CoreOp.ofString? (name : String) : Option CoreOp :=
  match CoreOp.ofString name with
  | .other _ => none
  | op => some op

/-! ### Round-trip proofs: ofString? ∘ toString = some

Since both `toString` and `ofString?` are derived from the same `names`
list for each sub-type, these proofs are guaranteed to hold. Adding a
new constructor to any OpKind without adding it to `names` will cause
a build failure. -/

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
-- Currently blocked by string operations in CoreOp.ofString (splitOn, startsWith)
-- not reducing in the kernel. Revisit when Lean improves string reduction.

end -- public section
end Core
