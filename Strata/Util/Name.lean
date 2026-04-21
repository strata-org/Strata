/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Name disambiguation utilities

Shared helpers for generating unique names with `@N` suffixes.
Used by the SMT encoder (for UF/bound-variable disambiguation) and
the symbolic evaluator (for readable generated variable names).
-/

public section

namespace Strata.Name

/-- Generate a disambiguated name by appending `@suffix`. -/
def disambiguate (baseName : String) (suffix : Nat) : String :=
  s!"{baseName}@{suffix}"

/-- Parse a list of digit characters as a natural number. -/
def digitsToNat (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Break a potentially disambiguated name into its base name and next suffix.
    If the name has an `@N` suffix, returns `(base, N + 1)`.
    Otherwise returns `(name, 1)`. -/
def breakDisambiguated (name : String) : String × Nat :=
  let cs := name.toList
  let digitSuffix := cs.reverse.takeWhile Char.isDigit |>.reverse
  let rest := cs.reverse.dropWhile Char.isDigit |>.reverse
  match rest.reverse, digitSuffix with
  | '@' :: _, _ :: _ => (String.ofList rest.dropLast, digitsToNat digitSuffix + 1)
  | _, _ => (name, 1)

/-- Find a unique name by trying candidates with increasing `@N` suffixes.
    The `isUsed` predicate checks if a candidate name is already taken. -/
def findUnique (baseName : String) (startSuffix : Nat)
    (isUsed : String → Bool) (limit : Nat := 1000) : String :=
  let rec loop (candidate : String) (suffix : Nat) (remaining : Nat) : String :=
    if h : remaining == 0 then candidate
    else if isUsed candidate then
      loop (disambiguate baseName suffix) (suffix + 1) (remaining - 1)
    else
      candidate
  termination_by remaining
  decreasing_by
    have : remaining ≠ 0 := by intro h'; simp [h'] at h
    omega
  loop (if startSuffix == 1 then baseName
        else disambiguate baseName (startSuffix - 1))
       startSuffix limit

end Strata.Name

end -- public section
