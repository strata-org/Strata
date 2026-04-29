/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.TypeCheck.AbstractType
public import Strata.Languages.Python.SSA.IR

/-!
# Transfer Table for Type Propagation

Extensible, table-driven dispatch for operator and expression transfer
functions.  Each transfer function ("proc") is keyed by operator kind
and operand type tags, stored in a HashMap for O(1) lookup.

Lookup probes at three specificity levels:
1. `(op, literal, literal)` — constant folding
2. `(op, widened lhs, widened rhs)` — type-level rules
3. `(op, .any, .any)` — fallback (blame propagation)

The first proc returning `some` at the most-specific matching level wins.
-/

public section
namespace Strata.Python.TypeCheck

open Strata.Python.SSA
open Strata.Python.TypeCheck

/-! ## Type Tags -/

inductive TypeTag where
  | int | str | float | bool | none | bytes | object
  | literal
  | instance_ (className : String)
  | any
  | other
deriving Inhabited, Repr, BEq

def TypeTag.hash : TypeTag → UInt64
  | .int => 0 | .str => 1 | .float => 2 | .bool => 3
  | .none => 4 | .bytes => 5 | .object => 6
  | .literal => 7
  | .instance_ n => mixHash 8 (Hashable.hash n)
  | .any => 9
  | .other => 10

instance : Hashable TypeTag where
  hash := TypeTag.hash

def AbstractType.tag : AbstractType → TypeTag
  | .bottom => .other
  | .any _ => .any
  | .int => .int
  | .str => .str
  | .bool => .bool
  | .float => .float
  | .none => .none
  | .bytes => .bytes
  | .object => .object
  | .literal _ => .literal
  | .union _ => .other
  | .instance_ n => .instance_ n
  | .callable _ => .other

def AbstractType.widenTag (t : AbstractType) : TypeTag :=
  match t with
  | .literal v => match v.baseTypeName with
    | "int" => .int | "str" => .str | "bool" => .bool
    | "float" => .float | "None" => .none | _ => .other
  | _ => t.tag

/-! ## Operator Ordinals (for hashing without modifying SSA IR) -/

def binOpOrd : BinOpKind → UInt64
  | .add => 0 | .sub => 1 | .mult => 2 | .div => 3
  | .floorDiv => 4 | .mod => 5 | .pow => 6

def unaryOpOrd : UnaryOpKind → UInt64
  | .not_ => 0 | .uSub => 1

def cmpOpOrd : CmpOpKind → UInt64
  | .eq => 0 | .notEq => 1 | .lt => 2 | .ltE => 3
  | .gt => 4 | .gtE => 5 | .is_ => 6 | .isNot => 7
  | .in_ => 8 | .notIn => 9

/-! ## Transfer Proc Types -/

abbrev BinOpProc := AbstractType → AbstractType → Option AbstractType

abbrev UnaryOpProc := AbstractType → Option AbstractType

abbrev CmpOpProc := AbstractType → AbstractType → Option AbstractType

/-! ## Key Types -/

structure BinTransferKey where
  op  : BinOpKind
  lhs : TypeTag
  rhs : TypeTag
deriving Inhabited, BEq

instance : Hashable BinTransferKey where
  hash k := mixHash (mixHash (binOpOrd k.op) k.lhs.hash) k.rhs.hash

structure UnaryTransferKey where
  op      : UnaryOpKind
  operand : TypeTag
deriving Inhabited, BEq

instance : Hashable UnaryTransferKey where
  hash k := mixHash (unaryOpOrd k.op) k.operand.hash

structure CmpTransferKey where
  op  : CmpOpKind
  lhs : TypeTag
  rhs : TypeTag
deriving Inhabited, BEq

instance : Hashable CmpTransferKey where
  hash k := mixHash (mixHash (cmpOpOrd k.op) k.lhs.hash) k.rhs.hash

/-! ## Transfer Table -/

structure TransferTable where
  binOps   : Std.HashMap BinTransferKey (Array BinOpProc)
  unaryOps : Std.HashMap UnaryTransferKey (Array UnaryOpProc)
  cmpOps   : Std.HashMap CmpTransferKey (Array CmpOpProc)

instance : Inhabited TransferTable where
  default := { binOps := {}, unaryOps := {}, cmpOps := {} }

namespace TransferTable

def empty : TransferTable := { binOps := {}, unaryOps := {}, cmpOps := {} }

def addBinOp (t : TransferTable) (op : BinOpKind) (lhs rhs : TypeTag)
    (proc : BinOpProc) : TransferTable :=
  let key : BinTransferKey := ⟨op, lhs, rhs⟩
  let procs := (t.binOps.getD key #[]).push proc
  { t with binOps := t.binOps.insert key procs }

def addUnaryOp (t : TransferTable) (op : UnaryOpKind) (operand : TypeTag)
    (proc : UnaryOpProc) : TransferTable :=
  let key : UnaryTransferKey := ⟨op, operand⟩
  let procs := (t.unaryOps.getD key #[]).push proc
  { t with unaryOps := t.unaryOps.insert key procs }

def addCmpOp (t : TransferTable) (op : CmpOpKind) (lhs rhs : TypeTag)
    (proc : CmpOpProc) : TransferTable :=
  let key : CmpTransferKey := ⟨op, lhs, rhs⟩
  let procs := (t.cmpOps.getD key #[]).push proc
  { t with cmpOps := t.cmpOps.insert key procs }

def lookupBinOp (t : TransferTable) (op : BinOpKind)
    (lhs rhs : AbstractType) : Option AbstractType := Id.run do
  let lTag := lhs.tag
  let rTag := rhs.tag
  let wlTag := lhs.widenTag
  let wrTag := rhs.widenTag
  let probes : Array BinTransferKey := #[
    ⟨op, lTag, rTag⟩,
    ⟨op, wlTag, wrTag⟩,
    ⟨op, .any, .any⟩
  ]
  for key in probes do
    if let some procs := t.binOps.get? key then
      if let some result := procs.findSome? (· lhs rhs) then
        return result
  return .none

def lookupUnaryOp (t : TransferTable) (op : UnaryOpKind)
    (operand : AbstractType) : Option AbstractType := Id.run do
  let tag := operand.tag
  let wTag := operand.widenTag
  let probes : Array UnaryTransferKey := #[
    ⟨op, tag⟩,
    ⟨op, wTag⟩,
    ⟨op, .any⟩
  ]
  for key in probes do
    if let some procs := t.unaryOps.get? key then
      if let some result := procs.findSome? (· operand) then
        return result
  return .none

def lookupCmpOp (t : TransferTable) (op : CmpOpKind)
    (lhs rhs : AbstractType) : Option AbstractType := Id.run do
  let lTag := lhs.tag
  let rTag := rhs.tag
  let wlTag := lhs.widenTag
  let wrTag := rhs.widenTag
  let probes : Array CmpTransferKey := #[
    ⟨op, lTag, rTag⟩,
    ⟨op, wlTag, wrTag⟩,
    ⟨op, .any, .any⟩
  ]
  for key in probes do
    if let some procs := t.cmpOps.get? key then
      if let some result := procs.findSome? (· lhs rhs) then
        return result
  return .none

end TransferTable

/-! ## Builder Monad -/

abbrev TransferTableM := StateM TransferTable

namespace TransferTableM

def addBinOp (op : BinOpKind) (lhs rhs : TypeTag) (proc : BinOpProc) : TransferTableM Unit :=
  modify (·.addBinOp op lhs rhs proc)

def addUnaryOp (op : UnaryOpKind) (operand : TypeTag) (proc : UnaryOpProc) : TransferTableM Unit :=
  modify (·.addUnaryOp op operand proc)

def addCmpOp (op : CmpOpKind) (lhs rhs : TypeTag) (proc : CmpOpProc) : TransferTableM Unit :=
  modify (·.addCmpOp op lhs rhs proc)

def build (m : TransferTableM Unit) : TransferTable :=
  (m.run .empty).snd

end TransferTableM

open TransferTableM

/-- Build the default transfer table with built-in Python semantics. -/
def defaultTransferTable : TransferTable := build do
  let allBinOps : Array BinOpKind := #[.add, .sub, .mult, .div, .floorDiv, .mod, .pow]
  let allUnaryOps : Array UnaryOpKind := #[.not_, .uSub]
  let allCmpOps : Array CmpOpKind := #[.eq, .notEq, .lt, .ltE, .gt, .gtE, .is_, .isNot, .in_, .notIn]

  -- Blame propagation (fallback for all ops)
  let blameBin : BinOpProc := fun
    | .any blame, _ | _, .any blame => some (.any blame)
    | _, _ => .none
  for op in allBinOps do
    addBinOp op .any .any blameBin
  for op in allCmpOps do
    addCmpOp op .any .any blameBin
  for op in allUnaryOps do
    addUnaryOp op .any fun
      | .any blame => some (.any blame)
      | _ => .none

  -- Constant folding (literal × literal)
  addBinOp .add .literal .literal fun
    | .literal (.int a), .literal (.int b) => some (.literal (.int (a + b)))
    | _, _ => .none
  addBinOp .add .literal .literal fun
    | .literal (.str a), .literal (.str b) => some (.literal (.str (a ++ b)))
    | _, _ => .none
  addBinOp .sub .literal .literal fun
    | .literal (.int a), .literal (.int b) => some (.literal (.int (a - b)))
    | _, _ => .none
  addBinOp .mult .literal .literal fun
    | .literal (.int a), .literal (.int b) => some (.literal (.int (a * b)))
    | _, _ => .none
  let strRepeat : BinOpProc := fun
    | .literal (.str s), .literal (.int n) =>
      if n ≥ 0 then some (.literal (.str ("".intercalate (List.replicate n.toNat s))))
      else some (.literal (.str ""))
    | .literal (.int n), .literal (.str s) =>
      if n ≥ 0 then some (.literal (.str ("".intercalate (List.replicate n.toNat s))))
      else some (.literal (.str ""))
    | _, _ => .none
  addBinOp .mult .literal .literal strRepeat
  addUnaryOp .not_ .literal fun
    | .literal (.bool b) => some (.literal (.bool !b))
    | _ => .none
  addUnaryOp .uSub .literal fun
    | .literal (.int v) => some (.literal (.int (-v)))
    | _ => .none

  -- Type-level rules (widened tags)
  for op in #[.add, .sub, .mult, .floorDiv, .mod, .pow] do
    addBinOp op .int .int fun _ _ => some .int
  addBinOp .div .int .int fun _ _ => some .float

  for op in allBinOps do
    addBinOp op .float .float fun _ _ => some .float
    addBinOp op .float .int   fun _ _ => some .float
    addBinOp op .int .float   fun _ _ => some .float

  addBinOp .add  .str .str fun _ _ => some .str
  addBinOp .mult .str .str fun _ _ => some .str
  addBinOp .mult .str .int fun _ _ => some .str
  addBinOp .mult .int .str fun _ _ => some .str

  addUnaryOp .not_ .bool fun _ => some .bool
  addUnaryOp .uSub .int   fun _ => some .int
  addUnaryOp .uSub .float fun _ => some .float

  for op in allCmpOps do
    addCmpOp op .any .any fun _ _ => some .bool

end Strata.Python.TypeCheck
end -- public section
