/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashSet.Basic

/-! # Name disambiguation utilities

Shared helpers for generating unique names. Bare names are preferred;
`@N` suffixes are added only when disambiguation is needed.
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

/-- Fast candidate search with a fuel counter. Returns `none` if fuel is exhausted. -/
def findUniqueFast (baseName : String) (candidate : String) (suffix : Nat)
    (usedNames : Std.HashSet String) (fuel : Nat) : Option String :=
  if !usedNames.contains candidate then some candidate
  else match fuel with
    | 0 => none
    | fuel + 1 =>
      findUniqueFast baseName (disambiguate baseName suffix) (suffix + 1) usedNames fuel

/-- Provably-terminating fallback via list erasure.
    Uses `usedSet` (a `HashSet`) for O(1) membership checks and `remaining`
    (a list that shrinks via erasure) for termination.
    Returns `none` only if `remaining` is exhausted before finding a
    candidate outside `usedSet` — unreachable when `remaining` covers
    `usedSet` and candidates are distinct. -/
def findUniqueSlow (baseName : String) (candidate : String) (suffix : Nat)
    (usedSet : Std.HashSet String) (remaining : List String) : Option String :=
  if !usedSet.contains candidate then some candidate
  else if h : remaining.contains candidate then
    have : (remaining.erase candidate).length < remaining.length := by grind
    findUniqueSlow baseName (disambiguate baseName suffix) (suffix + 1)
                   usedSet (remaining.erase candidate)
  else none
termination_by remaining.length

/-- Find a unique name by trying candidates with increasing `@N` suffixes.
    Uses a fast counter-based loop, falling back to a provably-terminating
    list-erasure search if the counter is exhausted (so we never panic). -/
def findUnique (baseName : String) (startSuffix : Nat)
    (usedNames : Std.HashSet String) : String :=
  let firstCandidate :=
    if startSuffix == 1 then baseName
    else disambiguate baseName (startSuffix - 1)
  match findUniqueFast baseName firstCandidate startSuffix usedNames 1000000 with
  | some name => name
  | none =>
    let slowSuffix := startSuffix + 1000000
    let usedList := usedNames.toList
    match findUniqueSlow baseName (disambiguate baseName slowSuffix)
                         (slowSuffix + 1) usedNames usedList with
    | some name => name
    | none => disambiguate baseName (slowSuffix + usedList.length + 1)

end Strata.Name

end -- public section
