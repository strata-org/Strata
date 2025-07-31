/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.Deser
import Strata.DDM.Util.Ion.AST

namespace Ion

structure TypeDesc where
  ofByte :: toByte : UInt8

def TypeDesc.code (d : TypeDesc) : UInt8 := d.toByte >>> 0x4
def TypeDesc.length (d : TypeDesc) : UInt8 := d.toByte &&& 0xF

open Strata.Deser

inductive PartialValue
| list (vals : Array (Ion SymbolId))
| sexp (vals : Array (Ion SymbolId))
| struct (vals : Array (SymbolId × Ion SymbolId))
| ann (annot : Array SymbolId)
deriving Inhabited, Repr

namespace PartialValue

def append (pv : PartialValue) (s : SymbolId) (v : Ion SymbolId) : PartialValue ⊕ Ion SymbolId :=
  match pv with
  | .list vals => .inl <| .list <| vals.push v
  | .sexp vals => .inl <| .sexp <| vals.push v
  | .struct vals => .inl <| .struct <| vals.push (s, v)
  | .ann a => .inr <| .mk (.annotation a v)

end PartialValue

def readTypeDesc : SReader TypeDesc := .ofByte <$> .readByte

def readVarUInt : SReader Nat :=
  .readWhile 0 fun v b =>
    let v := (v <<< 7) ||| (b &&& 0x7f).toNat
    if b &&& 0x80 = 0x80 then
      .done v
    else
      .yield v

def readVarInt : SReader Int :=
  .readWhile 0 fun (v : Nat) b =>
    if b &&& 0x80 = 0x80 then
      let isNeg := b &&& 0x40 = 0x40
      let v := (v <<< 7) ||| (b &&& 0x3f).toNat
      let v := if isNeg then .negOfNat v else .ofNat v
      .done v
    else
      let v := (v <<< 7) ||| (b &&& 0x7f).toNat
      .yield v

def readUInt (limit : Nat) : AReader Nat := do
  .readUpto 0 limit fun v => (v <<< 8 ||| ·.toNat) <$> .readByte

def readInt (limit : Nat) : SReader (Bool × Nat) := do
  .bindAny .readByte fun b => do
  let isNeg := b &&& 0x80 = 0x80
  let r ← .readUpto (b &&& 0x7f).toNat limit fun v =>
    (v <<< 8 ||| ·.toNat) <$> .readByte
  pure (isNeg, r)

@[reducible] def NatLe (n : Nat) := { x : Nat // x ≤ n }

instance : Inhabited (NatLe n) where
  default := ⟨0, by omega⟩

def readLength (td : TypeDesc) (limit : Nat) : AReader (NatLe limit) := do
  let len := td.length.toNat
  if len < 14 then
    let off ← .curOffset
    if p : off + len ≤ limit then
      pure <| .mk (off + len) p
    else
      .fail ((←.curOffset) - 1) s!"Length is too large"
  else
    let off ← .curOffset
    let len ← .ofLT readVarUInt
    if p : off + len ≤ limit then
      return .mk (off + len) p
    else
      .fail off s!"Length is too large"

def readString (limit : Nat) : AReader String := do
  let off ← .curOffset
  let b ← .readBuffer (limit - off)
  match String.fromUTF8? b with
  | some s => pure s
  | none => .fail off s!"Invalid UTF8 string"

def readDouble : AReader Float := do
  let n ← readUInt <| (←.curOffset) + 8
  pure <| .ofBits n.toUInt64

inductive Token (limit : Nat)
| null (tp : CoreType)
| bool (b : Bool)
| int (i : Int)
| float (f : Float)
| decimal (d : Decimal)
-- TODO: Add timestamp
| string (s : String)
| symbol (s : SymbolId)
| bvm (major minor : UInt8)
| nop
| startList (end_limit : NatLe limit)
| startSExp (end_limit : NatLe limit)
| startStruct (end_limit : NatLe limit)
| startAnn (end_limit : NatLe limit) (annot : Array SymbolId)
deriving Inhabited

def readToken (limit : Nat) : SReader (Token limit) :=
  .bind .curOffset fun off =>
  .bindAny readTypeDesc fun typeDesc => do
    if typeDesc.length = 15 then
      match typeDesc.code with
      | 0xE =>
        .fail off s!"Annotation cannot have length 15"
      | 0xF =>
        .fail off s!"Reserved type descriptor code {typeDesc.code}"
      | _ =>
        return .null (Ion.CoreType.codes[typeDesc.code.toNat]!)
    match typeDesc.code with
    | 0x0 =>
      -- This is a no-op
      let .mk limit _ ← readLength typeDesc limit
      .skip off (limit - (←.curOffset))
      return .nop
    | 0x1 =>
      match typeDesc.length with
      | 0 =>
        return .bool false
      | 1 =>
        return .bool true
      | _ =>
        .fail off s!"Invalid bool type description length {typeDesc.length}"
    | 0x2 | 0x3 =>
      let .mk limit _ ← readLength typeDesc limit
      let off ← .curOffset
      let mag ← readUInt limit
      if typeDesc.code = 0x3 then
        if mag = 0 then
          .fail off s!"Negative number must have non-zero agnitude."
        return .int (.negOfNat mag)
      else
        return .int (.ofNat mag)
    | 0x4 =>
      let .mk limit _ ← readLength typeDesc limit
      if limit ≠ (← .curOffset) + 8 then
        .fail off s!"Only double float fields supported."
      let v ← readDouble
      return .float v
    | 0x5 => -- decimal
      if typeDesc.length = 0 then
        return .decimal .zero
      else
        let .mk limit _ ← readLength typeDesc limit
        let e ← .ofLT readVarInt
        let (isn, c) ← .ofLT <| readInt limit
        let mantissa : Int := if isn then .negOfNat c else .ofNat c
        let d : Decimal := { mantissa, exponent := e }
        pure (.decimal d)
    | 0x6 =>
      .fail off "Timestamps not supported"
    | 0x7 => -- symbol
      let .mk limit _ ← readLength typeDesc limit
      let symId ← Ion.SymbolId.mk <$> readUInt limit
      return (.symbol symId)
    | 0x8 => -- string
      let .mk limit _ ← readLength typeDesc limit
      let s ← readString limit
      return .string s
    | 0x9 =>
      .fail off "clob not supported"
    | 0xA =>
      .fail off "blob not supported"
    | 0xB => -- list
      .startList <$> readLength typeDesc limit
    | 0xC => -- sexp
      .startSExp <$> readLength typeDesc limit
    | 0xD => -- struct
      .startStruct <$> readLength typeDesc limit
    | 0xE => -- annotation
      let len := typeDesc.length
      if len = 0 then
        -- binary Version marker
        let off ← .curOffset
        let contents ← read
        if p : off+2 < contents.size then
          let major := contents[off]
          let minor := contents[off+1]
          let marker := contents[off+2]
          if (major, minor) ≠ (1, 0) then
            .fail (off-1) s!"Ion {major}.{minor} not supported."
          if marker ≠ 0xea then
            .fail (off-1) s!"Bad terminator for binary version marker {marker}"
          .skip! 3
          pure (.bvm major minor)
        else
          .fail off s!"End of file"
      else
        let limit ← readLength typeDesc limit
        let annot_len ← .ofLT readVarUInt
        let annot_limit := (← .curOffset) + annot_len
        if annot_limit ≥ limit.val then
          .fail (← .curOffset) "Annotation missing value."
        let ann ← .readSeqUpto annot_limit (.mk <$> readVarUInt)
        pure (.startAnn limit ann)
    | _ =>
      .fail off s!"Reserved type descriptor code {typeDesc.code}"

structure DeserializeState (size : Nat) where
  prev : Array (Array (Ion SymbolId))
  cur : Array (Ion SymbolId)
  stack : Array (SymbolId × PartialValue × NatLe size)
deriving Inhabited, Repr

namespace DeserializeState

def empty (size : Nat) : DeserializeState size where
  prev := #[]
  cur := #[]
  stack := #[]

def inStruct {size} (r : DeserializeState size) : Bool :=
  match r.stack.back? with
  | some (_, .struct _, _) => true
  | _ => false

def limit {size} (r : DeserializeState size) : NatLe size :=
  match r.stack.back? with
  | none => ⟨size, Nat.le_refl _⟩
  | some (_, _, l) => l

def appendValue {size : Nat} (r : DeserializeState size) (s : SymbolId) (v : Ion SymbolId) : DeserializeState size :=
  if isz : r.stack.size = 0 then
    { r with cur := r.cur.push v }
  else
    let (old_sym, pv, limit) := r.stack.back!
    let stack' := r.stack.pop
    match p : pv.append s v with
    | .inl pv =>
      { r with stack := stack'.push (old_sym, pv, limit) }
    | .inr v =>
      have _ : stack'.size < r.stack.size := by
        simp [stack']
        omega
      let r' := { r with stack := stack' }
      r'.appendValue old_sym v
termination_by r.stack.size

theorem appendValue_stackSize {size : Nat} (r : DeserializeState size) (s : SymbolId) (v : Ion SymbolId) :
  (r.appendValue s v).stack.size ≤ r.stack.size := by
  unfold appendValue
  if isz : r.stack.size = 0 then
    simp [isz]
  else
    simp [isz]
    split
    case h_1 eq =>
      simp
      omega
    case h_2 eq =>
      apply Nat.le_trans
      apply appendValue_stackSize
      simp
termination_by r.stack.size

/--
Updates the deserialization state by finalizing finished partial values on top of stack.
-/
def popFinishedValues {size} (off : Nat) (ds : DeserializeState size) : Except String (DeserializeState size) :=
  if off < ds.limit.val then
    pure ds
  else if p : ds.stack.size = 0 then
    pure ds
  else do
    let (sym, pv, _) := ds.stack.back!
    let top2 : DeserializeState size := { ds with stack := ds.stack.pop }
    have p : top2.stack.size < ds.stack.size := by
      simp [top2]
      omega
    let v : Value SymbolId ←
      match pv with
      | .list a => pure <| .mk <| .list a
      | .sexp a => pure <| .mk <| .sexp a
      | .struct a => pure <| .mk <| .struct a
      | .ann _ => .error s!"Annotation without value"
    let top3 : DeserializeState size := top2.appendValue sym v
    have q := top2.appendValue_stackSize sym v
    have p : top3.stack.size < ds.stack.size := by
      simp [top3]
      omega
    popFinishedValues off top3
termination_by ds.stack.size

def close {size} (r : DeserializeState size) : Array (Array (Ion SymbolId)) := r.prev.push r.cur

def startNew {size} (r : DeserializeState size) : DeserializeState size :=
  { prev := r.close, cur := #[], stack := #[] }

def pushPartialValue {size} (r : DeserializeState size) (sym : SymbolId) (pv : PartialValue) (limit : NatLe size) : DeserializeState size :=
  { r with stack := r.stack.push (sym, pv, limit) }

end DeserializeState

def cleanupRecords {size} (s : DeserializeState size) : AReader (DeserializeState size) := do
  let off ← .curOffset
  match s.popFinishedValues off with
  | .error msg =>
    .fail off msg
    return default
  | .ok top =>
    pure top

/--
Main loop driving deserialization
-/
def deserializeAux {size} (ds : DeserializeState size) : AReader (DeserializeState size) := do
  .readUpto (init := ds) size fun ds =>
    .bind
      (if ds.inStruct then
        Ion.SymbolId.mk <$> .ofLT readVarUInt
      else
        pure Ion.SymbolId.zero) fun sym =>
    .bindAny (readToken size) fun tkn =>
      match tkn with
      | .null tp =>
        cleanupRecords <| ds.appendValue sym (.null tp)
      | .bool b =>
        cleanupRecords <| ds.appendValue sym (.bool b)
      | .int i =>
        cleanupRecords <| ds.appendValue sym (.int i)
      | .float v =>
        cleanupRecords <| ds.appendValue sym (.float v)
      | .decimal v =>
        cleanupRecords <| ds.appendValue sym (.decimal v)
      | .symbol v =>
        cleanupRecords <| ds.appendValue sym (.symbol v)
      | .string v =>
        cleanupRecords <| ds.appendValue sym (.string v)
      | .bvm major minor => do
        if !ds.stack.isEmpty then
          .fail (←.curOffset) s!"Encountered binary version marker inside term"
        if (major, minor) ≠ (1, 0) then
          .fail (←.curOffset) s!"Unxpected Ion version {major}.{minor}"
        pure <| ds.startNew
      | .nop =>
        cleanupRecords ds
      | .startList l  =>
        cleanupRecords <| ds.pushPartialValue sym (.list #[]) l
      | .startSExp l =>
        cleanupRecords <| ds.pushPartialValue sym (.sexp #[]) l
      | .startStruct l =>
        cleanupRecords <| ds.pushPartialValue sym (.struct #[]) l
      | .startAnn l annot =>
        cleanupRecords  <| ds.pushPartialValue sym (.ann annot) l

def deserialize (contents : ByteArray) : Except (Nat × String) (Array (Array (Ion.Ion SymbolId))) :=
  if contents.isEmpty then
    return #[]
  else
    match BufferM.ofReader contents.size (deserializeAux (.empty contents.size)) contents with
    | .error (pos, msg) => .error (pos, msg)
    | .ok (r, _) => .ok r.close
