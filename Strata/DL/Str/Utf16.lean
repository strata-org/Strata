/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.Predicates

/-! # UTF-16

`encodeUtf16` writes a code-point string as UTF-16 units, splitting each code point
at or above `0x10000` into a high and a low surrogate, and writing every other code
point, a lone surrogate included, as the unit of the same value (Python's
`surrogatepass`). `decodeUtf16` reads units back, joining each high surrogate directly
followed by a low one into one code point and keeping every other unit as itself
(Java's `codePoints()`).

Proved in `Strata.DL.Str.Utf16Props`: decoding loses nothing, `encodeUtf16 (decodeUtf16 us) = us` for every unit string
(`encodeUtf16_decodeUtf16`), so `decodeUtf16` is injective on units
(`decodeUtf16_injective`). The other round trip holds exactly on code-point strings
in which no high surrogate is directly followed by a low one
(`decodeUtf16_encodeUtf16`): the code points `[0xD83D, 0xDE00]`, two lone surrogates,
encode to the units of `😀` and decode back as the one code point `0x1F600`
(`decodeUtf16_encodeUtf16_pair`). -/

@[expose] public section

namespace Strata.Str

/-- The UTF-16 units of the code point `c`, with a lone surrogate written as itself. -/
def utf16Units (c : Nat) : List Nat :=
  if c < 0x10000 then [c]
  else [0xD800 + (c - 0x10000) / 0x400, 0xDC00 + (c - 0x10000) % 0x400]

/-- Encode a code-point string as UTF-16 units, lone surrogates written as themselves. -/
def encodeUtf16 (cs : List Nat) : List Nat := cs.flatMap utf16Units

/-- The code point a high surrogate `u` and a low surrogate `v` encode. -/
def joinSurrogates (u v : Nat) : Nat := 0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00)

/-- Decode UTF-16 units into code points, joining each high surrogate directly followed
    by a low one, and keeping every other unit as itself. -/
def decodeUtf16 : List Nat → List Nat
  | [] => []
  | [u] => [u]
  | u :: v :: rest =>
    if isHighSurrogate u && isLowSurrogate v then joinSurrogates u v :: decodeUtf16 rest
    else u :: decodeUtf16 (v :: rest)

end Strata.Str

end
