/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Functions for ByteArray that could potentially be upstreamed to Lean.
-/
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

def asHex (a : ByteArray) : String :=
  a.foldl (init := "") fun s b =>
    let cl := Nat.toDigits 16 b.toNat
    let cl := if cl.length < 2 then '0' :: cl else cl
    s ++ cl.asString

end ByteArray

#guard (ByteArray.empty |>.back!) = default
#guard (ByteArray.empty |>.push 4 |>.back!) = 4

#guard (ByteArray.empty |>.pop) = .empty
#guard let a := ByteArray.empty |>.push 0 |>.push 1; (a |>.push 2 |>.pop) = a
