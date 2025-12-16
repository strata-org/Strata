/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Functions for ByteArray that could potentially be upstreamed to Lean.
-/
import Std.Data.HashMap

namespace ByteArray

deriving instance DecidableEq for ByteArray

def back! (a : ByteArray) : UInt8 := a.get! (a.size - 1)

def back? (a : ByteArray) : Option UInt8 := a[a.size - 1]?

def pop (a : ByteArray) : ByteArray := a.extract 0 (a.size - 1)

@[inline]
def foldr {β} (f : UInt8 → β → β) (init : β) (as : ByteArray) (start := as.size) (stop := 0) : β :=
  let rec aux (i : Nat) (p : i ≤ as.size) (b : β) :=
      if h : i ≤ stop then
        b
      else
        have q : i - i < as.size := by omega
        aux (i-1) (by omega) (f as[i-1] b)
  aux (min start as.size) (Nat.min_le_right _ _) init

def byteToHex (b : UInt8) : String :=
  let cl := Nat.toDigits 16 b.toNat
  let cl := if cl.length < 2 then '0' :: cl else cl
  cl.asString

def asHex (a : ByteArray) : String :=
  a.foldl (init := "") fun s b => s ++ byteToHex b

def startsWith (a pre : ByteArray) :=
  if isLt : a.size < pre.size then
    false
  else
    pre.size.all fun i _ => a[i] = pre[i]

instance : Repr ByteArray where
  reprPrec a p := Repr.addAppParen ("ByteArray.mk " ++ reprArg a.data) p

def ofNatArray (a : Array Nat) : ByteArray := .mk (a.map UInt8.ofNat)

instance : Lean.Quote ByteArray where
  quote b := Lean.Syntax.mkCApp ``ofNatArray #[Lean.quote (b.data.map fun b => b.toNat)]

end ByteArray

#guard (ByteArray.empty |>.back!) = default
#guard (ByteArray.empty |>.push 4 |>.back!) = 4

#guard (ByteArray.empty |>.pop) = .empty
#guard let a := ByteArray.empty |>.push 0 |>.push 1; (a |>.push 2 |>.pop) = a

namespace Strata.ByteArray

def escapedBytes : Std.HashMap UInt8 Char := Std.HashMap.ofList [
    (9, 't'),
    (10, 'n'),
    (13, 'r'),
    (34, '"'),
    (92, '\\'),
]

def escapeBytes (b : ByteArray) : String :=
  (b.foldl (init := "b\"") fun s b => s ++ aux b) ++ "\""
where aux (b : UInt8) : String :=
        match escapedBytes[b]? with
        | some c => "\\".push c
        | none =>
          if 32 ≤ b ∧ b < 127 then
            Char.ofUInt8 b |>.toString
          else
            "\\x" ++ ByteArray.byteToHex b

@[inline]
def hexDigitToUInt8 (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then
    .some <| c.toUInt8 - '0'.toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then
    .some <| c.toUInt8 - 'A'.toUInt8 + 10
  else if 'a' ≤ c ∧ c ≤ 'f' then
    .some <| c.toUInt8 - 'a'.toUInt8 + 10
  else
    none

def escapeChars : Std.HashMap Char UInt8 := .ofList <|
    ByteArray.escapedBytes.toList |>.map fun (i, c) => (c, i)

partial def unescapeBytesRawAux (s : String) (i0 : String.Pos.Raw) (a : ByteArray) : Except (String.Pos.Raw × String.Pos.Raw × String) (ByteArray × String.Pos.Raw) :=
  if i0 = s.endPos then
    .error (i0, i0, "unexpected end of input, expected closing quote")
  else
    let ch := i0.get s
    let i := i0.next s
    if ch == '"' then
      .ok (a, i)
    else if ch == '\\' then
      -- Escape sequence
      if i = s.endPos then
        .error (i0, i, "unexpected end of input after backslash")
      else
        let escCh := i.get s
        let i := i.next s
        if escCh = 'x' then
          -- Hex escape: \xHH
          if i = s.endPos then
            .error (i0, i, "incomplete hex escape sequence")
          else
            let c1 := i.get s
            let j := i.next s
            if j = s.endPos then
              .error (i0, j, "incomplete hex escape sequence")
            else
              let c2 := j.get s
              let k := j.next s
              match hexDigitToUInt8 c1, hexDigitToUInt8 c2 with
              | some b1, some b2 =>
                let b := b1 * 16 + b2
                unescapeBytesRawAux s k (a.push b)
              | none, _ => .error (i0, k, "Invalid hex escape sequence")
              | _, none => .error (i0, k, "Invalid hex escape sequence")
        else
          match escapeChars[escCh]? with
          | some b =>
            unescapeBytesRawAux s i (a.push b)
          | none =>
            .error (i0, i, "invalid escape sequence: {escCh}")
    else
      unescapeBytesRawAux s i (a.push ch.toUInt8)

partial def unescapeBytesAux (s : String) (i0 : String.ValidPos s) (a : ByteArray) : Except (String.ValidPos s × String.ValidPos s × String) (ByteArray × String.ValidPos s) :=
  if h : i0 = s.endValidPos then
    .error (i0, i0, "unexpected end of input, expected closing quote")
  else
    let ch := i0.get h
    let i := i0.next h
    if ch == '"' then
      .ok (a, i)
    else if ch == '\\' then
      -- Escape sequence
      if h : i = s.endValidPos then
        .error (i0, i, "unexpected end of input after backslash")
      else
        let escCh := i.get h
        let i := i.next h
        if escCh = 'x' then
          -- Hex escape: \xHH
          if h : i = s.endValidPos then
            .error (i0, i, "incomplete hex escape sequence")
          else
            let c1 := i.get h
            let j := i.next h
            if h : j = s.endValidPos then
              .error (i0, j, "incomplete hex escape sequence")
            else
              let c2 := j.get h
              let k := j.next h
              match hexDigitToUInt8 c1, hexDigitToUInt8 c2 with
              | some b1, some b2 =>
                let b := b1 * 16 + b2
                unescapeBytesAux s k (a.push b)
              | none, _ => .error (i0, k, "Invalid hex escape sequence")
              | _, none => .error (i0, k, "Invalid hex escape sequence")
        else
          match escapeChars[escCh]? with
          | some b =>
            unescapeBytesAux s i (a.push b)
          | none =>
            .error (i0, i, "invalid escape sequence: {escCh}")
    else
      unescapeBytesAux s i (a.push ch.toUInt8)

def unescapeBytes (s : String) : Except (String.ValidPos s × String.ValidPos s × String) ByteArray :=
  let i : String.ValidPos s := s.startValidPos  |>.next! |>.next!
  match unescapeBytesAux s i .empty with
  | .error (f, e, msg) => .error (f, e, msg)
  | .ok (a, _) => .ok a

end Strata.ByteArray
