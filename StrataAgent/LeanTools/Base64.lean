/-
Base64 decoder for receiving Lean code from Python.
-/

namespace StrataAgent.LeanTools.Base64

/-- Helper to convert Option to Except -/
def Option.toExcept {α : Type} (o : Option α) (err : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error err

/-- Base64 character to 6-bit value mapping -/
def charToValue (c : Char) : Option UInt8 :=
  if 'A' ≤ c ∧ c ≤ 'Z' then
    some (c.toNat - 'A'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some (c.toNat - 'a'.toNat + 26).toUInt8
  else if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat + 52).toUInt8
  else if c = '+' then
    some 62
  else if c = '/' then
    some 63
  else
    none

partial def loop (i : Nat) (result : ByteArray) (chars : List Char) : Except String ByteArray :=
  if i >= chars.length then
    .ok result
  else
    -- Get 4 characters (or remaining)
    let c1 := chars[i]!
    let c2 := if i + 1 < chars.length then chars[i + 1]! else '='
    let c3 := if i + 2 < chars.length then chars[i + 2]! else '='
    let c4 := if i + 3 < chars.length then chars[i + 3]! else '='

    match Option.toExcept (charToValue c1) "Invalid base64 character" with
    | .error e => .error e
    | .ok v1 =>
      match Option.toExcept (charToValue c2) "Invalid base64 character" with
      | .error e => .error e
      | .ok v2 =>
        -- First byte is always present
        let b1 := (v1.toNat <<< 2 ||| (v2.toNat >>> 4)).toUInt8
        let result := result.push b1

        -- Second byte if c3 exists
        if c3 ≠ '=' then
          match Option.toExcept (charToValue c3) "Invalid base64 character" with
          | .error e => .error e
          | .ok v3 =>
            let b2 := ((v2.toNat &&& 0xF) <<< 4 ||| (v3.toNat >>> 2)).toUInt8
            let result := result.push b2

            -- Third byte if c4 exists
            if c4 ≠ '=' then
              match Option.toExcept (charToValue c4) "Invalid base64 character" with
              | .error e => .error e
              | .ok v4 =>
                let b3 := ((v3.toNat &&& 0x3) <<< 6 ||| v4.toNat).toUInt8
                loop (i + 4) (result.push b3) chars
            else
              loop (i + 4) result chars
        else
          loop (i + 4) result chars

/-- Decode a base64 string to bytes -/
def decodeBytes (s : String) : Except String ByteArray :=
  let chars := s.trim.toList.filter (· ≠ '=')
  loop 0 ByteArray.empty chars

/-- Decode a base64 string to UTF-8 string -/
def decode (s : String) : Except String String := do
  let bytes ← decodeBytes s
  match String.fromUTF8? bytes with
  | some str => return str
  | none => throw "Invalid UTF-8 encoding"

end StrataAgent.LeanTools.Base64
