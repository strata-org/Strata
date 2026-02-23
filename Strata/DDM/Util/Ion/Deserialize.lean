/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.Ion.AST

import Strata.DDM.Util.ByteArray

namespace Ion

structure TypeDesc where
  ofByte :: toByte : UInt8

def TypeDesc.code (d : TypeDesc) : UInt8 := d.toByte >>> 0x4
def TypeDesc.length (d : TypeDesc) : UInt8 := d.toByte &&& 0xF

inductive Step (α : Type u) (β : Type v) where
  | done  : β → Step α β
  | yield : α → Step α β
  deriving Inhabited

abbrev ReadM := Except (Nat × String)

abbrev SReadM (off : Nat) (α : Type) := ReadM (α × { new : Nat // new > off })

@[inline]
def rfail {α} (off : Nat) (msg : String) : ReadM α := .error (off, msg)

@[specialize]
def readWhileAux {α β} (bytes : @ByteArray) (base : Nat) (init : α) (off : Nat) (act : α → UInt8 → Step α β) (p : off ≥ base := by omega) : SReadM base β :=
  if p : off < bytes.size then
    match act init bytes[off] with
    | .done r => .ok (r, ⟨off+1, by omega⟩)
    | .yield a => readWhileAux bytes base a (off+1) act
  else
    rfail off "Unexpected end of file"

@[inline]
def readWhile {α β} (bytes : @ByteArray) (init : α) (base : Nat) (p : base < bytes.size) (act : α → UInt8 → Step α β) : SReadM base β := do
  match act init bytes[base] with
  | .done r =>
    .ok (r, ⟨base+1, by omega⟩)
  | .yield a =>
    readWhileAux bytes base a (base+1) act

@[specialize]
def readUpTo {α} (bytes : @ByteArray) (init : α) (off : Nat) (limit : Nat) (limitp : limit ≤ bytes.size) (f : α → UInt8 → α) : α :=
  if offp : off < limit then
    let b := bytes[off]
    let v := f init b
    readUpTo bytes v (off+1) limit limitp f
  else
    init

@[inline]
def readVarUInt (bytes : @ByteArray) (off : Nat) (p : off < bytes.size := by omega) : SReadM off Nat :=
  let b := bytes[off]
  if b &&& 0x80 = 0x80 then
    let v := b &&& 0x7f
    (pure (v.toNat, ⟨off+1, by omega⟩) : ReadM _)
  else
    -- VarUInts are on critical path so we special case for 16bit version too.
    let base := off
    let off := off + 1
    if p : off ≥ bytes.size then
      rfail off s!"Unexpected end of file"
    else
      let v := b
      let b := bytes[off]
      if b &&& 0x80 = 0x80 then
        let v := (v.toNat.toUInt16 <<< 7) ||| (b &&& 0x7f).toNat.toUInt16
        .ok (v.toNat, ⟨off+1, by omega⟩)
      else
        let v := (v.toNat <<< 7) ||| b.toNat
        readWhileAux bytes base v (off+1) fun v b =>
          let v := (v <<< 7) ||| (b &&& 0x7f).toNat
          if b &&& 0x80 = 0x80 then
            .done v
          else
            .yield v

@[inline]
def readVarUInt' (bytes : @ByteArray) (off : Nat) : SReadM off Nat := do
  let .isTrue p := inferInstanceAs (Decidable (off < bytes.size))
    | rfail off s!"Unexpected end of file"
  readVarUInt bytes off

def readVarInt (bytes : @ByteArray) (off : Nat) (p : off < bytes.size := by omega) : SReadM off Int := do
  let b := bytes[off]
  let isNeg := b &&& 0x40 = 0x40
  let v := (b &&& 0x3f).toNat
  if b &&& 0x80 = 0x80 then
    let v : Int := if isNeg then .negOfNat v else .ofNat v
    .ok (v, ⟨off+1, by omega⟩)
  else
    readWhileAux bytes off v (off+1) fun (v : Nat) b =>
      let v := (v <<< 7) ||| (b &&& 0x7f).toNat
      if b &&& 0x80 = 0x80 then
        .done <| if isNeg then .negOfNat v else .ofNat v
      else
        .yield v

/-
  readWhile bytes 0 off (by omega) fun (v : Nat) b =>
    if b &&& 0x80 = 0x80 then
      let isNeg := b &&& 0x40 = 0x40
      let v := (v <<< 7) ||| (b &&& 0x3f).toNat
      let v := if isNeg then .negOfNat v else .ofNat v
      .done v
    else
      let v := (v <<< 7) ||| (b &&& 0x7f).toNat
      .yield v
-/

@[inline]
def readUInt (bytes : @ByteArray) (off : Nat) (limit : Nat) (limitp : limit ≤ bytes.size := by omega) : Nat :=
  if limit ≤ off + 8 then
    let r := readUpTo (α := UInt64) bytes 0 off limit limitp fun v b => v <<< 8 ||| b.toNat.toUInt64
    r.toNat
  else
    readUpTo bytes 0 off limit limitp fun v b => v <<< 8 ||| b.toNat

@[inline]
def readInt (bytes : @ByteArray) (off : Nat) (limit : Nat) (limitp : limit ≤ bytes.size) : Bool × Nat :=
  let b := bytes[off]!
  let isNeg := b &&& 0x80 = 0x80
  let r := readUpTo bytes (b &&& 0x7f).toNat (off+1) limit limitp fun v b => v <<< 8 ||| b.toNat
  (isNeg, r)

@[reducible] def NatLe (n : Nat) := { x : Nat // x ≤ n }

instance {n} : Inhabited (NatLe n) where
  default := ⟨0, by omega⟩

@[inline]
def readString (bytes : @ByteArray) (off : Nat) (limit : Nat) : ReadM String := do
  let b := bytes.extract off limit
  if h : b.IsValidUTF8 then
    pure <| String.fromUTF8 b h
  else
    rfail off s!"Invalid UTF8 string"

def readDouble  (bytes : @ByteArray) (off : Nat) (limitp : off + 8 ≤ bytes.size) : Float :=
  let n := readUInt bytes off (off+8)
  .ofBits n.toUInt64

inductive Token (limit : Nat)
| startList (end_limit : NatLe limit)
| startSExp (end_limit : NatLe limit)
| startStruct (end_limit : NatLe limit)
| startAnn (end_limit : NatLe limit) (annot : Array SymbolId)
deriving Inhabited

@[specialize]
def readSymbolIdSeqAux (bytes : @ByteArray) (ss : Array SymbolId) (off : Nat) (limit : Nat) (limitp : limit ≤ bytes.size) : ReadM (Array SymbolId) := do
  if p : off < limit then
    let (symId, ⟨off, _⟩) ← readVarUInt bytes off
    let ss := ss.push (.mk symId)
    readSymbolIdSeqAux bytes ss off limit limitp
  else
    .ok ss

@[inline]
def readSymbolIdSeq (bytes : @ByteArray) (off : Nat) (limit : Nat) (limitp : limit ≤ bytes.size) : ReadM (Array SymbolId) := do
  readSymbolIdSeqAux bytes #[] off limit limitp

structure Length (off : Nat) (limit : Nat) where
  new_off : Nat
  new_limit : Nat
  valid : off ≤ new_off ∧ new_off ≤ new_limit ∧ new_limit ≤ limit

@[inline]
def readLength (bytes : @ByteArray) (off : Nat)(td_length : UInt8)
   : ReadM (Length off bytes.size) := do
  let len := td_length.toNat
  if len < 14 then
    if p : off + len ≤ bytes.size then
      return ⟨off, off+len, by omega⟩
    else
      rfail (off - 1) s!"Length {len} at {off} is too large"
  else
    let (len, ⟨off, offp⟩) ← readVarUInt' bytes off
    if p : off + len ≤ bytes.size then
      return ⟨off, off + len, by omega⟩
    else
      rfail off s!"Long length is too large"

abbrev NatGT base := { new : Nat // new > base }

@[inline]
def appendIfNonempty (prev : Array (Array (Ion SymbolId))) (v : Array (Ion SymbolId)) : Array (Array (Ion SymbolId)) :=
  if v.isEmpty then
    prev
  else
    prev.push v

inductive PartialTag
| list
| sexp
| struct
| ann (annot : Array SymbolId)
deriving Inhabited, Repr

namespace PartialTag

@[inline]
def isList : PartialTag → Bool
| .list => true
| _ => false

@[inline]
def isStruct : PartialTag → Bool
| .struct => true
| _ => false

end PartialTag

structure DeserializeState (size : Nat) where
  prev : Array (Array (Ion SymbolId))
  symbols : Array SymbolId
  values : Array (Ion SymbolId)
  tags : Array PartialTag
  value_indices : Vector Nat tags.size
  limits : Vector (NatLe size) tags.size
  off : Nat
deriving Inhabited, Repr

namespace DeserializeState

@[inline]
def empty (size : Nat) : DeserializeState size where
  prev := #[]
  symbols := #[]
  values := #[]
  tags := #[]
  value_indices := #v[]
  limits := #v[]
  off := 0

def limit {size} (r : DeserializeState size) : NatLe size :=
  match r.limits.back? with
  | some l => l
  | none => ⟨size, Nat.le_refl _⟩

/--
Updates the deserialization state by finalizing finished partial values on top of stack.
-/
partial def popFinishedValues {size} {base} (ds : DeserializeState size) (off : Nat) (p : off > base := by grind)
    :  ReadM { s : DeserializeState size // s.off > base } :=
  if h : ds.tags.size = 0 then
    return ⟨{ds with off := off }, p⟩
  else do
    let { prev, symbols, values, tags, value_indices, limits, .. } := ds
    have _ : NeZero tags.size := ⟨h⟩
    let ⟨limit, _⟩ := limits.back
    if off < limit then
      return ⟨{ds with off := off }, p⟩
    let value_index := value_indices.back
    let (symbols, v) ←
      match tags.back with
      | .list =>
        let a := values.extract value_index
        pure <| (symbols, Ion.mk (.list a))
      | .sexp =>
        let a := values.extract value_index
        pure (symbols, .mk <| (.sexp a))
      | .struct =>
        let cnt := values.size - value_index
        let .isTrue symp := inferInstanceAs (Decidable (symbols.size ≥ cnt))
          | rfail off "Bad symbols"
        let base := symbols.size - cnt
        let v := Array.ofFn fun (i : Fin cnt) => (symbols[base + i.val], values[value_index + i])
        pure (symbols.shrink base, .mk <| .struct v)
      | .ann ann =>
        let a := values.extract value_index
        if p : a.size = 1 then
          pure (symbols, .annotation ann a[0])
        else
          rfail off s!"Annotation without value"
    let values := values.shrink value_index
    let ds := {
      prev
      symbols
      values := values.push v
      tags := tags.pop
      value_indices := value_indices.pop.cast (by grind)
      limits := limits.pop.cast (by grind)
      off
    }
    popFinishedValues ds off p

def startNew {size} (ds : DeserializeState size) (_ : ds.tags.size = 0) : DeserializeState size :=
  assert! ds.symbols.size = 0
  if ds.values.isEmpty then
    ds
  else
    { ds with prev := appendIfNonempty ds.prev ds.values, values := #[] }

@[inline]
def pushValue {size : Nat} (ds : DeserializeState size) (v : Ion SymbolId) : DeserializeState size :=
  { ds with values := ds.values.push v }

@[inline]
def appendValue {size : Nat} {base : Nat} (ds : DeserializeState size) (off : Nat) (v : Ion SymbolId) (p : base < off := by omega)
    : ReadM { s : DeserializeState size // s.off > base } := do
  ds |>.pushValue v |>.popFinishedValues off

@[inline]
def pushPartialValue {size} {base}
      (ds : DeserializeState size)
      (off : Nat)
      (tag : PartialTag)
      (limit : NatLe size)
      (p : off > base := by omega)
      : ReadM { s : DeserializeState size // s.off > base } := do
  if off < limit then
    let ds := {
      ds with
      tags := ds.tags.push tag
      value_indices := ds.value_indices.push ds.values.size |>.cast (by simp)
      limits := ds.limits.push limit |>.cast (by simp)
      off := off
    }
    pure ⟨ds, p⟩
  else
    let v ←
      match tag with
      | .list =>
        pure <| Ion.mk (.list #[])
      | .sexp =>
        pure <| Ion.mk (.sexp #[])
      | .struct =>
        pure <| .mk (.struct #[])
      | .ann ann =>
        rfail off s!"Annotation without value"
    ds.pushValue v |>.popFinishedValues off p

end DeserializeState

def readNopToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  -- This is a no-op
  let ⟨_, limit, vp⟩ ← readLength bytes (off+1) td_length
  ds.popFinishedValues limit

def readBoolToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  if td_length ≥ 2 then
    rfail off s!"Invalid bool type description length {td_length}"
  let b := td_length == 1
  ds.appendValue (off+1) (.bool b)

def readPosIntToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  let mag := readUInt bytes off limit
  let v := .ofNat mag
  ds.appendValue limit (.int v)

def readNegIntToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  let mag := readUInt bytes off limit
  if mag = 0 then
    rfail off s!"Negative number must have non-zero agnitude."
  let v := .negOfNat mag
  ds.appendValue limit (.int v)

def readDoubleToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off2, limit, p⟩ ← readLength bytes (off+1) td_length
  if h : limit ≠ off2 + 8 then
    rfail off s!"Only double float fields supported."
  else
    let v := readDouble bytes off2 (by grind)
    ds.appendValue limit (.float v)

def readDecimalToken  (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  if td_length = 0 then
    ds.appendValue (off+1) (.decimal .zero)
  else
    let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
    let .isTrue p := inferInstanceAs (Decidable (off < limit))
      | rfail off s!"Unexpected empty decimal"
    let ⟨e, off⟩ ← readVarInt bytes off
    let d : Decimal :=
      if off < limit then
        let (isn, c) := readInt bytes off limit (by omega)
        let mantissa : Int := if isn then .negOfNat c else .ofNat c
        { mantissa, exponent := e }
      else
        { mantissa := 0, exponent := e }
    ds.appendValue limit (.decimal d)

def readSymbolToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  let symId := Ion.SymbolId.mk <| readUInt bytes off limit
  ds.appendValue limit (.symbol symId)

def readStringToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  let s ← readString bytes off limit
  ds.appendValue limit (.string s)

def readBlobToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  let a := bytes.extract off limit
  ds.appendValue limit (.blob a)

def readListToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  ds.pushPartialValue off .list ⟨limit, by omega⟩

def readSexpToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  ds.pushPartialValue off .sexp ⟨limit, by omega⟩

def readStructToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let ⟨off, limit, p⟩ ← readLength bytes (off+1) td_length
  ds.pushPartialValue off .struct ⟨limit, by omega⟩

def readAnnotationToken (bytes : @ByteArray) (ds : DeserializeState bytes.size)
      (td_length : UInt8) (off : Nat) (_ : off < bytes.size)
      : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let off := off+1
  if td_length = 0 then
    -- binary Version marker
    if p : off+2 < bytes.size then
      let major := bytes[off]
      let minor := bytes[off+1]
      let marker := bytes[off+2]
      if (major, minor) ≠ (1, 0) then
        rfail (off-1) s!"Ion {major}.{minor} not supported."
      if marker ≠ 0xea then
        rfail (off-1) s!"Bad terminator for binary version marker {marker}"
      if p : !ds.tags.isEmpty then
        rfail off s!"Encountered binary version marker inside term"
      else
        return ⟨{ ds.startNew (by simp_all) with off := off + 3 }, by grind⟩
    else
      rfail off s!"End of file"
  else
    let ⟨off, limit, validp⟩ ← readLength bytes off td_length
    let ⟨annot_len, off⟩ ← readVarUInt' bytes off
    let annot_limit := off + annot_len
    if h : annot_limit ≥ limit then
      rfail off "Annotation missing value."
    else
      let ann ← readSymbolIdSeq bytes off annot_limit (by omega)
      ds.pushPartialValue annot_limit (.ann ann) ⟨limit, by omega⟩

@[inline]
def readNotSupportedToken {α} (name : String) (off : Nat) : ReadM α :=
  rfail off s!"{name} not supported"

@[inline]
def readToken (bytes : @ByteArray) (ds : DeserializeState bytes.size) (off : Nat) (p : off < bytes.size := by omega)
    : ReadM { s : DeserializeState bytes.size // s.off > off } := do
  let typeDesc := TypeDesc.ofByte bytes[off]
  let td_code := typeDesc.code
  let td_length := typeDesc.length
  if td_length = 15 then
    if q : td_code.toNat < Ion.CoreType.codes.size then
      let tp := Ion.CoreType.codes[td_code.toNat]
      return ← ds.appendValue (off+1) (.null tp)
    else
    if td_code = 0xE then
      rfail off s!"Annotation cannot have length 15"
    else
      rfail off s!"Reserved type descriptor code {td_code}"
  match td_code.toNat with
  | 0 => readNopToken bytes ds td_length off (by omega)
  | 1 => readBoolToken bytes ds td_length off (by omega)
  | 2 => readPosIntToken bytes ds td_length off (by omega)
  | 3 => readNegIntToken bytes ds td_length off (by omega)
  | 4 => readDoubleToken bytes ds td_length off (by omega)
  | 5 => readDecimalToken bytes ds td_length off (by omega)
  | 6 => readNotSupportedToken "Timestamps" off
  | 7 => readSymbolToken bytes ds td_length off (by omega)
  | 8 => readStringToken bytes ds td_length off (by omega)
  | 9 => readNotSupportedToken "Clob" off
  | 10 => readBlobToken bytes ds td_length off (by omega)
  | 11 => readListToken bytes ds td_length off (by omega)
  | 12 => readSexpToken bytes ds td_length off (by omega)
  | 13 => readStructToken bytes ds td_length off (by omega)
  | 14 => readAnnotationToken bytes ds td_length off (by omega)
  | _ => rfail off s!"Reserved type descriptor code {td_code}"

abbrev InRange base limit := { n : Nat // base ≤ n ∧ n < limit }
/--
Main loop driving deserialization
-/
def deserializeAux (bytes : ByteArray) (ds : DeserializeState bytes.size)
    : ReadM (DeserializeState bytes.size) :=
  if init_offp : ds.off < bytes.size then do
    let inStruct :=
      if p : ds.tags.size = 0 then
        false
      else
        ds.tags.back.isStruct
    let off0 := ds.off
    let (ds, ⟨off, sym_offp⟩) ←
      if inStruct then
        let (symId, ⟨off, offp⟩) ← readVarUInt bytes ds.off
        let .isTrue offp := inferInstanceAs (Decidable (off < bytes.size))
          | rfail off "Unexpected end of file"
        let ds := { ds with symbols := ds.symbols.push ⟨symId⟩ }
        let off' : InRange off0 bytes.size := ⟨off, by omega⟩
        pure (ds, off')
      else
        let off' : InRange off0 bytes.size := ⟨ds.off, by omega⟩
        pure (ds, off')
    let ⟨ds_new, p⟩ ← readToken bytes ds off
    deserializeAux bytes ds_new
  else do
    pure ds
termination_by bytes.size - ds.off
decreasing_by
  omega

public def deserialize (contents : ByteArray) : Except (Nat × String) (Array (Array (Ion.Ion SymbolId))) :=
  if contents.isEmpty then
    return #[]
  else
    match deserializeAux contents (.empty contents.size) with
    | .error (pos, msg) => .error (pos, msg)
    | .ok r => .ok <| appendIfNonempty r.prev r.values

end Ion
