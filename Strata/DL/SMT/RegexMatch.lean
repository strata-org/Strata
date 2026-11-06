/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.StringLit

/-! # Matching SMT-LIB regular expressions

Regular expressions with their SMT-LIB meaning, and a matcher for literal
strings. Matching takes the derivative of the expression by each character in
turn (Brzozowski's method) and checks whether the rest accepts the empty
string. For example, the derivative of `"ab" ++ c*` by `a` and then `b` is
`c*`, which accepts the empty string, so `"ab"` matches. -/

public section

namespace Strata.SMT.Regex

/-- A regular expression over the SMT-LIB string alphabet. -/
inductive Re where
  /-- `re.none`: no string. -/
  | none
  /-- `re.all`: every string. -/
  | all
  /-- `re.allchar`: every string of one character. -/
  | allChar
  /-- `str.to_re s`: the string `s`. -/
  | str (s : List Char)
  /-- `re.range` with single-character bounds. -/
  | range (lo hi : Char)
  /-- `re.++` -/
  | cat (a b : Re)
  /-- `re.union` -/
  | union (a b : Re)
  /-- `re.inter` -/
  | inter (a b : Re)
  /-- `re.*` -/
  | star (a : Re)
  /-- `re.comp`: the complement of `a`. -/
  | comp (a : Re)
  /-- `re.loop`: `lo` to `hi` repetitions of `a`; no string when `lo > hi`. -/
  | loop (a : Re) (lo hi : Nat)
  deriving DecidableEq, Ord, Inhabited, Repr

/-- The node count above which `matches?` gives no answer. -/
def maxSize : Nat := 10000

namespace Re

/-- `re.range` of two strings: the characters between them when both have one
    character, and no string otherwise. -/
def ofRange (lo hi : String) : Re :=
  match lo.toList, hi.toList with
  | [l], [h] => .range l h
  | _, _ => .none

/-- `re.+`: one or more repetitions. -/
def plus (a : Re) : Re := .cat a (.star a)

/-- Whether `r` has at most `n` nodes. Counting stops once it passes `n`, so
    the check is cheap even on a tree with shared subterms, such as nested
    `plus`. -/
def sizeLe (n : Nat) (r : Re) : Bool := (go n r).isSome
where
  /-- `n` less the number of nodes of `r`, or `none` past `n`. -/
  go : Nat → Re → Option Nat
    | 0, _ => Option.none
    | n + 1, .none | n + 1, .all | n + 1, .allChar | n + 1, .str _
    | n + 1, .range .. => some n
    | n + 1, .cat a b | n + 1, .union a b | n + 1, .inter a b => do
      go (← go n a) b
    | n + 1, .star a | n + 1, .comp a | n + 1, .loop a .. => go n a

/-- Concatenation, simplified when a side is `none` or the empty string. -/
def mkCat : Re → Re → Re
  | .none, _ | _, .none => .none
  | .str [], b => b
  | a, .str [] => a
  | a, b => .cat a b

/-- The alternatives of `r`, with nested unions flattened. -/
def alts : Re → List Re
  | .union a b => a.alts ++ b.alts
  | r => [r]

/-- `rs` with each element equal to the one before it removed. -/
def dedupAdjacent : List Re → List Re
  | a :: rest@(b :: _) =>
    if a = b then dedupAdjacent rest else a :: dedupAdjacent rest
  | rs => rs

/-- The union of `rs`, nested to the right, or `none` when `rs` is empty. -/
def ofAlts : List Re → Re
  | [] => .none
  | [a] => a
  | a :: rs => .union a (ofAlts rs)

/-- Union, normalized: the alternatives of both sides are sorted, with
    repeats and `none` removed, and the union is `all` when one of them is.
    This keeps derivatives small: those of `re.all ++ "a" ++ re.all` by each
    character would otherwise grow with the length of the string. A union of
    more than `maxSize` nodes is left as is, so the sort never runs on a
    large term; `matches?` gives up on a derivative that contains it. -/
def mkUnion (a b : Re) : Re :=
  if !(Re.union a b).sizeLe maxSize then .union a b
  else
    let rs := (a.alts ++ b.alts).filter (· != .none)
    if rs.contains .all then .all
    else ofAlts (dedupAdjacent (rs.mergeSort (compare · · != .gt)))

/-- Intersection, which is `none` when either side is. -/
def mkInter : Re → Re → Re
  | .none, _ | _, .none => .none
  | a, b => .inter a b

/-- Whether `r` matches the empty string. -/
def nullable : Re → Bool
  | .none | .allChar | .range .. => false
  | .all | .star _ => true
  | .str s => s.isEmpty
  | .cat a b => a.nullable && b.nullable
  | .union a b => a.nullable || b.nullable
  | .inter a b => a.nullable && b.nullable
  | .comp a => !a.nullable
  | .loop a lo hi => lo ≤ hi && (lo == 0 || a.nullable)

/-- The derivative of `r` by `c`, the strings `s` such that `r` matches
    `c :: s`, and whether `r` is `nullable`. Computing both in one pass avoids
    recomputing `nullable` at every `cat`. -/
def derivNullable (c : Char) : Re → Re × Bool
  | .none => (.none, false)
  | .all => (.all, true)
  | .allChar => (.str [], false)
  | .str [] => (.none, true)
  | .str (d :: s) => (if c == d then .str s else .none, false)
  | .range lo hi => (if lo ≤ c && c ≤ hi then .str [] else .none, false)
  | .cat a b =>
    let (da, na) := derivNullable c a
    let (db, nb) := derivNullable c b
    let left := mkCat da b
    (if na then mkUnion left db else left, na && nb)
  | .union a b =>
    let (da, na) := derivNullable c a
    let (db, nb) := derivNullable c b
    (mkUnion da db, na || nb)
  | .inter a b =>
    let (da, na) := derivNullable c a
    let (db, nb) := derivNullable c b
    (mkInter da db, na && nb)
  | .star a => (mkCat (derivNullable c a).1 (.star a), true)
  | .comp a =>
    let (da, na) := derivNullable c a
    (.comp da, !na)
  -- The derivative of `a^k` is the derivative of `a` followed by `a^(k-1)`;
  -- when `a` matches the empty string the other terms of the product rule are
  -- contained in it.
  | .loop a lo hi =>
    let (da, na) := derivNullable c a
    (if hi == 0 || lo > hi then .none
     else mkCat da (.loop a (lo - 1) (hi - 1)), lo ≤ hi && (lo == 0 || na))

end Re

/-- Whether `r` matches `s`, or `none` when `r` or a derivative has more than
    `maxSize` nodes or `s` has a character outside the SMT-LIB alphabet. -/
def matches? (r : Re) (s : String) : Option Bool :=
  if !StringLit.isValid s || !r.sizeLe maxSize then none
  else
    let step (acc : Option Re) (c : Char) : Option Re :=
      acc.bind fun r =>
        let r' := (r.derivNullable c).1
        if r'.sizeLe maxSize then some r' else none
    (s.toList.foldl step (some r)).map Re.nullable

end Strata.SMT.Regex

end
