/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.Ion.AST
import all Strata.DDM.Util.ByteArray

namespace Strata.ByteArray

theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (p : _) : (a.set i v p).size = a.size := by
  simp only [ByteArray.set, ByteArray.size, Array.set]
  simp

theorem size_push (as : ByteArray) (v : UInt8) : (as.push v).size = as.size + 1 := by
  simp only [ByteArray.size]
  simp

public def zeros (n : Nat) : ByteArray :=
  n.fold (init := .emptyWithCapacity n) fun _ _ a => a.push 0

@[simp]
theorem zeros_size (n : Nat) : (zeros n).size = n := by
  unfold zeros
  induction n with
  | zero =>
    simp
  | succ n hyp =>
    simp_all [ByteArray.size_push]
    exact hyp

end Strata.ByteArray

namespace Ion

abbrev ByteVector n := { a : ByteArray // a.size = n }

namespace ByteVector

@[inline]
def set {n} (bs : ByteVector n) (i : Nat) (b : UInt8) (p : i < n := by get_elem_tactic) : ByteVector n :=
  match bs with
  | ⟨a, p⟩ => ⟨a.set i b, by simp [Strata.ByteArray.size_set]; exact p⟩

def setBytes {n} (v : ByteVector n) (off : Nat) (bs : ByteArray)
     (p : off + bs.size ≤ n) : ByteVector n :=
  let ⟨as, ap⟩ := v
  ⟨bs.copySlice 0 as off bs.size, by
    let ⟨as⟩ := as
    let ⟨bs⟩ := bs
    simp only [ByteArray.copySlice, ByteArray.size, Array.size_append] at *;
    simp
    omega⟩

@[specialize]
def setFoldrBytes' {n} {α β} (s : Nat) (e : Nat) (ep : e ≤ n)
      (f : α → UInt8 × α)
      (g : α → ByteVector n → β)
      (x : α)
      (cur : ByteVector n) : β :=
  if p : s < e then
    let e := e - 1
    let (b, x) := f x
    setFoldrBytes' s e (by omega) f g x (cur.set e b)
  else
    g x cur
termination_by e

@[inline]
def setFoldrBytes {n} {α} (s : Nat) (e : Nat) (ep : e ≤ n) (f : α → UInt8 × α) (x : α)
      (cur : ByteVector n) : ByteVector n :=
  setFoldrBytes' s e ep f (fun _ bytes => bytes) x cur

open Strata

def zeros (n : Nat) : ByteVector n :=
  ⟨.zeros n, ByteArray.zeros_size n⟩

end ByteVector

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

structure SerializeState where
  prev : Array (Σ (a : ByteArray), Fin a.size)
  prev_size : Nat
  cur : ByteArray
  next : Nat
  next_valid : next ≤ cur.size := by grind

namespace SerializeState

abbrev init_cap := 1024

def empty : SerializeState where
  prev := #[]
  prev_size := 0
  cur := .empty
  next := 0

instance : Inhabited SerializeState where
  default := empty

def size (s : SerializeState) : Nat := s.prev_size + (s.cur.size - s.next)

def render (s : SerializeState) : ByteArray :=
  let a := ByteArray.emptyWithCapacity s.size
  let a := ByteArray.copySlice s.cur s.next a 0 (s.cur.size - s.next)
  let r := s.prev.foldr (init := a) fun ⟨c, o⟩ a =>
    c.copySlice o.val a a.size (c.size - o.val)
  assert! r.size = s.size
  r


end SerializeState


def Serialize := SerializeState → SerializeState

@[inline]
def Serialize.cat (a : Serialize) (b : Serialize) : Serialize := fun s => a (b s)

@[inline]
def withReserve (cnt : Nat)
       (act : ∀{n}, ByteVector n → ∀(i : Nat), i + cnt ≤ n → ByteVector n)
      : Serialize := fun s =>
  let { prev, prev_size, cur, next, next_valid } := s
  if p : next ≥ cnt then
    let next' := next - cnt
    let ⟨cur, curp⟩ := act ⟨cur, Eq.refl cur.size⟩ next' (by omega)
    { prev, prev_size, cur, next := next', next_valid := by omega }
  else
    let prev :=
      if p : next < cur.size then
        prev.push ⟨cur, ⟨next, p⟩⟩
      else
        prev
    let prev_size := prev_size + (cur.size - next)
    let min := SerializeState.init_cap
    if p : min > cnt then
      let cur := Strata.ByteArray.zeros min
      let next' := min - cnt
      have p : cur.size = min := by simp [cur]
      let ⟨cur, curp⟩ := act ⟨cur, p⟩ next' (by omega)
      { prev, prev_size, cur, next := next', next_valid := by omega }
    else
      let cur := Strata.ByteArray.zeros cnt
      have p : cur.size = cnt := by simp [cur]
      let ⟨cur, curp⟩ := act ⟨cur, p⟩ 0 (by omega)
      { prev, prev_size, cur, next := 0, next_valid := by omega }

def serializeArray (a : ByteArray) : Serialize :=
  withReserve a.size fun bytes off offp =>
    bytes.setBytes off a offp

def encodeTypeByte (tp : UInt8) (v : UInt8) : UInt8 := tp <<< 4 ||| v

/--
Return the number of bytes required to encode a natural number.
-/
@[specialize]
def bytesRequired (x : Nat) : Nat := aux 0 x
  where aux c x :=
          if x = 0 then
            c
          else
            aux (c+1) (x >>> 8)
        termination_by x

/--
Return the number of bytes using the 7-bit varint encoding.
-/
@[specialize]
def varbytesRequired (x : Nat) : Nat := aux 0 x
  where aux c x :=
          if x = 0 then
            c
          else
            aux (c+1) (x >>> 7)
        termination_by x

def appendUInt {n} (x : Nat) (cnt : Nat)
      (bytes : ByteVector n) (off : Nat) (offp : off + cnt ≤ n := by omega) : ByteVector n :=
  let f x := (x.toUInt8, x >>> 8)
  bytes.setFoldrBytes off (off+cnt) offp f x

/--
`appendVarUInt x nt_cnt bytes off p` encodes `7*(nt_cnt + 1)` low order
bits of `x` into `bytes` starting at offset `off`.
-/
def appendVarUInt (x : Nat) (nt_cnt : Nat) {n} (bytes : ByteVector n) (off : Nat) (offp : off + nt_cnt < n) : ByteVector n :=
  let f x : UInt8 × Nat := ((x.toUInt8 &&& 0x7f), x >>> 7)
  let bytes := bytes.set (off+nt_cnt) (0x80 ||| (x.toUInt8 &&& 0x7f))
  let bytes := bytes.setFoldrBytes off (off+nt_cnt) (by omega) f (x >>> 7)
  bytes

def serializeVarUInt (x : Nat) : Serialize :=
  let cnt := varbytesRequired (x >>> 7)
  withReserve (cnt+1) fun bytes off offp =>
    appendVarUInt x cnt bytes off offp

/--
Emit a UInt64 with most-significant byte first.
-/
def appendUInt64 {n} (u : UInt64)
  (bytes : ByteVector n) (off : Nat) (offp : off + 8 ≤ n) : ByteVector n :=
  let f (x : UInt64) := (x.toUInt8, x >>> 8)
  bytes.setFoldrBytes off (off+8) offp f u

/--
Given an integer, return a pair consisting of the number of bytes
and the natural number value to encode.
-/
def encodeInt (v : Int) : Nat × Nat :=
  if v = 0 then
    (0, 0)
  else
    let isNeg := v < 0
    let x := v.natAbs
    -- Compute number of bytes required excluding byte with sign.
    let base_cnt := bytesRequired (x >>> 7)
    let r := if isNeg then (0x80 <<< (8 * base_cnt)) ||| x else x
    (base_cnt + 1, r)

def encodeVarInt (v : Int) : Nat × Nat :=
  let isNeg := v < 0
  let x := v.natAbs
  -- Compute number of bytes required excluding byte with sign.
  let base_cnt := varbytesRequired (x >>> 6)
  let r := if isNeg then (0x40 <<< (7 * base_cnt)) ||| x else x
  (base_cnt, r)

@[inline]
def serializeTypeDesc (tp : UInt8) (v : UInt8) : Serialize :=
  withReserve 1 fun bytes off offp =>
    bytes.set off (encodeTypeByte tp v) offp

def typeDescSize (contents_size : Nat) : Nat :=
  if contents_size < 14 then
    1
  else if contents_size < 0x80 then
    2
  else
    2 + varbytesRequired (contents_size >>> 7)

def appendTypeDesc
      {n len cnt}
      (tp : UInt8)
      (cnt_eq : cnt = typeDescSize len)
      (bytes : ByteVector n)
      (off : Nat)
      (offp : off + cnt ≤ n)
      : ByteVector n :=
  if h : len < 14 then
    have p : cnt > 0 := by simp [cnt_eq, typeDescSize]; grind
    bytes.set off (encodeTypeByte tp len.toUInt8)
  else
    have cntp : cnt ≥ 2 := by simp [cnt_eq, typeDescSize, h]; grind
    let bytes := bytes.set off (encodeTypeByte tp 14)
    appendVarUInt len (cnt-2) bytes (off+1) (by omega)

def serializeTypedBytes (tp : CoreType) (contents : ByteArray) : Serialize :=
  let cnt := typeDescSize contents.size
  withReserve (cnt + contents.size) fun bytes off offp =>
    let bytes := appendTypeDesc tp.code (.refl cnt) bytes off (by omega)
    let bytes := bytes.setBytes (off+cnt) contents (by omega)
    bytes

@[inline]
def serializeTyped (tp : UInt8) (act : Serialize) : Serialize := fun s =>
  let old_mark := s.size
  let s := act s
  let new_mark := s.size
  assert! new_mark ≥ old_mark
  let contents_size := new_mark - old_mark
  let header_size := typeDescSize contents_size
  let header_act {n} (bytes : ByteVector n) off offp :=
    appendTypeDesc tp (.refl header_size) bytes off offp
  withReserve header_size header_act s

@[inline]
def serializeTypedUInt (tp : UInt8) (x : Nat) : Serialize :=
  let len := bytesRequired x
  let cnt := typeDescSize len
  withReserve (cnt+len) fun bytes off offp =>
    let bytes := appendTypeDesc tp (.refl cnt) bytes off (by omega)
    appendUInt x len bytes (off + cnt)

@[inline]
def serializeTypedArray {α} (tp : UInt8) (as : Array α) (act : α → Serialize) : Serialize :=
  serializeTyped tp (fun s => as.foldr (init := s) act)

namespace Ion

partial def serialize : Ion SymbolId → Serialize
| .mk app =>
  match app with
  | .null tp =>
    serializeTypeDesc tp.code 0xf
  | .bool b =>
    serializeTypeDesc CoreType.bool.code (if b then 1 else 0)
  | .int i =>
     serializeTypedUInt (if i ≥ 0 then 2 else 3) i.natAbs
  | .float v =>
    withReserve 9 fun bytes off offp =>
      let bytes := bytes.set off (encodeTypeByte CoreType.float.code 8)
      appendUInt64 v.toBits bytes (off+1) (by omega)

  | .decimal v =>
    if v = .zero then
      serializeTypeDesc CoreType.decimal.code 0
    else
      let (nt_exp_cnt, exp) := encodeVarInt v.exponent
      let (mantissa_cnt, mantissa) := encodeInt v.mantissa
      let contents_size := nt_exp_cnt + 1 + mantissa_cnt
      let header_size := typeDescSize contents_size
      withReserve (header_size + contents_size) fun bytes off offp =>
        let code := CoreType.decimal.code
        let bytes := appendTypeDesc code (.refl header_size) bytes off (by omega)
        let off := off + header_size
        let bytes := appendVarUInt exp nt_exp_cnt bytes off (by omega)
        let off := off + nt_exp_cnt + 1
        appendUInt mantissa mantissa_cnt bytes off
  | .string v =>
    serializeTypedBytes .string v.toUTF8
  | .symbol v =>
    serializeTypedUInt CoreType.symbol.code v.value
  | .blob v =>
    serializeTypedBytes .blob v
  | .list v =>
    serializeTypedArray CoreType.list.code v.attach fun ⟨e, _⟩ => serialize e
  | .sexp v =>
    serializeTypedArray CoreType.sexp.code v.attach fun ⟨e, _⟩ => serialize e
  | .struct v =>
    serializeTypedArray CoreType.struct.code v.attach fun ⟨⟨sym, e⟩, _⟩ =>
      .cat (serializeVarUInt sym.value) (serialize e)
  | .annotation annot v =>
    serializeTyped 0xE $ fun s =>
      let s := v.serialize s
      let old_mark := s.size
      let s := annot.foldr (fun v s => serializeVarUInt v.value s) s
      let new_mark := s.size
      assert! new_mark ≥ old_mark
      serializeVarUInt (new_mark - old_mark) s

end Ion

/-- Create binary version marker -/
public def binaryVersionMarker (major : UInt8 := 1) (minor : UInt8 := 0) : ByteArray :=
  .mk #[ 0xE0, major, minor, 0xEA ]

public def serialize (values : Array (Ion SymbolId)) : ByteArray :=
  let s : Ion.SerializeState := .empty
  let s := values.foldr (init := s) fun v s => v.serialize s
  let s := Ion.serializeArray binaryVersionMarker s
  s.render
