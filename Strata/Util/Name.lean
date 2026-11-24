/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Init
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

/-- The first of the candidates `cand i`, `cand (i + 1)`, … that is not `taken`, giving up after
    `fuel` more candidates. -/
def firstUntaken (taken : String → Bool) (cand : Nat → String) : Nat → Nat → String
  | 0, i => cand i
  | fuel + 1, i => if taken (cand i) then firstUntaken taken cand fuel (i + 1) else cand i

/-- `base` if it is not `taken`, else the first of `base_1`, `base_2`, … that is not. The search
    stops after `fuel + 1` candidates, so it finds an untaken one when at most `fuel` names are
    taken. The result avoids only what `taken` accepts: a caller must
    make `taken` accept every name the new one must not clash with. -/
def freshNameBy (taken : String → Bool) (fuel : Nat) (base : String) : String :=
  firstUntaken taken (fun k => if k = 0 then base else base ++ "_" ++ toString k) (fuel + 1) 0

/-- A fresh name for each of `bases` in turn, as `freshNameBy` picks it, avoiding the names
    `taken` accepts and the names picked before it. `fuel` bounds the number of taken names. -/
def freshNamesBy (taken : String → Bool) (fuel : Nat) : List String → List String
  | [] => []
  | b :: rest =>
    let n := freshNameBy taken fuel b
    n :: freshNamesBy (fun m => taken m || m == n) (fuel + 1) rest

/-- `base`, or `base_k` for the smallest `k ≥ 1` that makes it differ from
every name in `taken`. Generated lemmas, abstracted calls
and generated types are named this way, so that they never clash with a name of
the program or with each other.

The result avoids only the names in `taken`, so a caller must put in `taken`
every name the new one must not clash with: for a new block label, for example,
every jump target and the entry label as well as every block label. -/
def freshName (taken : Std.HashSet String) (base : String) : String :=
  freshNameBy taken.contains taken.size base

/-- A fresh name for each of `bases` in turn, as `freshName` picks it, avoiding
the names in `taken` and the names picked before it.
Returns the names and `taken` with them added. As for `freshName`, `taken` must
hold every name the new ones must not clash with. -/
def freshNames (taken : Std.HashSet String) (bases : List String) :
    List String × Std.HashSet String :=
  let names := freshNamesBy taken.contains taken.size bases
  (names, names.foldl (fun t n => t.insert n) taken)

/-! ## The namespace of generated names

Names starting with `$__` (`internalMarker`) are reserved for the names Strata generates. A
program records prefixes covering the names it has in that namespace
(`Core.Program.usedIdentPrefixes`), so that a pass whose prefix no recorded prefix is comparable
with (`prefixesComparable`) can tell that no name of the program starts with it. -/

/-- The start of every name in the namespace reserved for generated names. -/
@[expose] def internalMarker : String := "$__"

/-- Is `n` in the namespace reserved for generated names? -/
@[expose] def isInternal (n : String) : Bool := n.startsWith internalMarker

/-- The prefix recorded for the internal name `n`: `$__` followed by the letters that follow it,
    so `$__ty12` gives `$__ty` and `$__ndelim_ite$_0` gives `$__ndelim`. When no letter follows
    `$__`, the character that does is kept, so `$__0` gives `$__0` rather than `$__`, which would
    overlap every prefix. Any prefix of `n` would do; a shorter one overlaps more prefixes. -/
@[expose] def internalPrefixOf (n : String) : String :=
  let rest := n.toList.drop internalMarker.length
  let letters := rest.takeWhile Char.isAlpha
  internalMarker ++ String.ofList (if letters.isEmpty then rest.take 1 else letters)

/-- Is one of `a` and `b` a prefix of the other? A name can start with both only if they are. -/
@[expose] def prefixesComparable (a b : String) : Bool := a.startsWith b || b.startsWith a

end Strata.Name

end -- public section
