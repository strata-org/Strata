/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.Ion.AST
import Strata.DDM.Util.ByteArray

namespace Ion

namespace CoreType

def code : CoreType → UInt8
| .null => 0x0
| .bool => 0x1
| .int => 0x2
| .float => 0x4
| .decimal => 0x5
| .timestamp => 0x6
| .symbol => 0x7
| .string => 0x8
| .clob => 0x9
| .blob => 0xA
| .list => 0xB
| .sexp => 0xC
| .struct => 0xD

end CoreType

namespace Ion

abbrev SerializeM := StateM ByteArray

abbrev Serialize := SerializeM Unit

def runSerialize (act : Serialize) : SerializeM ByteArray :=
  return act .empty |>.snd

def encodeTypeByte (tp : UInt8) (v : UInt8) : UInt8 := tp <<< 4 ||| v

def emitByte (v : UInt8) : Serialize := do
  modify (·.push v)

def emitBytes (bytes : ByteArray) : Serialize :=
  modify (· ++ bytes)

def emitReversed (bytes : ByteArray) : Serialize :=
  modify fun s => bytes.foldr (init := s) fun b s => s.push b

def encodeVarUIntLsb (x : Nat) : ByteArray :=
  let rec aux (x : Nat) (b : ByteArray) : ByteArray :=
        if x = 0 then
          b
        else
          aux (x >>> 7) (b.push (x.toUInt8 &&& 0x7f))
  let init : ByteArray := .empty |>.push (0x80 ||| (x.toUInt8 &&& 0x7f))
  aux (x >>> 7) init

def encodeVarIntLsb (i : Int) : ByteArray :=
  let rec aux (x : Nat) (b : ByteArray) (l : UInt8) : ByteArray × UInt8 :=
        if x = 0 then
          (b, l)
        else
          aux (x >>> 7) (b.push l) (x.toUInt8 &&& 0x7f)
  let n := i.natAbs
  let first := 0x80 ||| (n.toUInt8 &&& 0x7f)
  let (b, l) := aux (n >>> 7) .empty first
  let signValue : UInt8 := if i < 0 then 0x40 else 0
  if l &&& 0x40 = 0 then
    b |>.push (l ||| signValue)
  else
    b |>.push l |>.push signValue

def emitVarUInt (x : Nat) : Serialize :=
  emitReversed <| encodeVarUIntLsb x

def encodeUIntLsbAux (x : Nat) (b : ByteArray) : ByteArray :=
  if x = 0 then
    b
  else
    encodeUIntLsbAux (x >>> 8) (b.push x.toUInt8)

def encodeUIntLsb0 (x : Nat) : ByteArray :=
  encodeUIntLsbAux x .empty

def encodeUIntLsb1 (x : Nat) : ByteArray :=
  let init : ByteArray := .empty |>.push x.toUInt8
  encodeUIntLsbAux (x >>> 8) init

/-
Emit a UInt64 with most-significant byte first.
-/
def emitUInt64_msb (u : UInt64) : Serialize :=
  let rec appendBytes cnt s :=
        match cnt with
        | 0 => s
        | cnt + 1 => appendBytes cnt (s.push (u >>> (8*cnt).toUInt64).toUInt8)
  modify (appendBytes 8)

def encodeIntLsb (isNeg : Bool) (x : Nat) : ByteArray :=
  let rec aux (x : Nat) (b : ByteArray) (l : UInt8) : ByteArray × UInt8 :=
    if x = 0 then
      (b, l)
    else
      aux (x >>> 8) (b.push l) x.toUInt8
  let (b, l) := aux (x >>> 8) .empty x.toUInt8
  let signValue : UInt8 := if isNeg then 0x80 else 0
  if l &&& 0x80 = 0 then
    b |>.push (l ||| signValue)
  else
    b |>.push l |>.push signValue

def emitTypeByte (tp : UInt8) (v : UInt8) : Serialize :=
  emitByte <| encodeTypeByte tp v

def emitTypeAndLen (tp : UInt8) (len : Nat) : Serialize :=
  if len < 14 then
    emitTypeByte tp len.toUInt8
  else do
    emitTypeByte tp 14
    emitVarUInt len

def emitTypedBytes (tp : CoreType) (contents : ByteArray) : Serialize := do
  emitTypeAndLen tp.code contents.size
  emitBytes contents

def serialize : Ion SymbolId → Serialize
| .mk app =>
  match app with
  | .null tp =>
    emitTypeByte tp.code 0xf
  | .bool b =>
    emitTypeByte CoreType.bool.code (if b then 1 else 0)
  | .int i => do
    let b := encodeUIntLsb0 i.natAbs
    emitTypeAndLen (if i ≥ 0 then 2 else 3) b.size
    emitReversed b
  | .float v => do
    emitTypeByte CoreType.float.code 8
    emitUInt64_msb v.toBits
  | .decimal v => do
    if v = .zero then
      emitTypeByte CoreType.decimal.code 0
    else
      let exp := encodeVarIntLsb v.exponent
      let coef := encodeIntLsb (v.mantissa < 0) v.mantissa.natAbs
      let len := exp.size + coef.size
      emitTypeAndLen CoreType.decimal.code len
      emitReversed exp
      emitReversed coef
  | .symbol v => do
    let sym := encodeUIntLsb0 v.value
    let len := sym.size
    emitTypeAndLen CoreType.symbol.code len
    emitReversed sym
  | .string v => do
    emitTypedBytes .string v.toUTF8
  | .list v => do
    let s ← runSerialize (v.size.forM fun i isLt => serialize v[i])
    emitTypedBytes .list s
  | .sexp v => do
    let s ← runSerialize (v.size.forM fun i isLt => serialize v[i])
    emitTypedBytes .sexp s
  | .struct v => do
    let s ← runSerialize <| v.size.forM fun i isLt => do
      let p := v[i]
      emitVarUInt p.fst.value
      have p1 : sizeOf v[i].snd < sizeOf v[i] := by
        match v[i] with
        | ⟨nm, v⟩ => decreasing_trivial
      have p2 : sizeOf v[i] < sizeOf v := by
        apply Array.sizeOf_getElem
      serialize p.snd
    emitTypedBytes .struct s
  | .annotation annot v => do
    let s ← runSerialize do
      let s := annot.foldl (init := .empty) (fun s v => s ++ encodeVarUIntLsb v.value)
      emitVarUInt s.size
      emitReversed s
      v.serialize
    emitTypeAndLen 0xE s.size
    emitBytes s

end Ion

/-- Create binary version marker -/
def binaryVersionMarker (major : UInt8 := 1) (minor : UInt8 := 0) : ByteArray :=
  .mk #[ 0xE0, major, minor, 0xEA ]

def serialize (values : Array (Ion SymbolId)) : ByteArray :=
  values.foldl (init := binaryVersionMarker) fun s v => v.serialize s |>.snd
