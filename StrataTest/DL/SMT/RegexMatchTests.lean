/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.RegexMatch

meta section

/-! # Tests for the SMT-LIB regular expression matcher

Each operator, its SMT-LIB edge cases, and the inputs with no answer. -/

namespace Strata.SMT.Regex.Tests

open Re

private def s (x : String) : Re := .str x.toList

private def noFinalPeriod : Re := .comp (.cat .all (s "."))

#guard matches? noFinalPeriod "hello." == some false
#guard matches? noFinalPeriod "." == some false
#guard matches? noFinalPeriod "bye!" == some true
#guard matches? noFinalPeriod "" == some true

private def optionallyA : Re := .loop (s "a") 0 1

#guard matches? optionallyA "a" == some true
#guard matches? optionallyA "" == some true
#guard matches? optionallyA "b" == some false
#guard matches? optionallyA "aa" == some false

/-- One to ten characters from `a-z`, `0-9`, `.` and `-`. -/
private def okChars : Re :=
  .loop (.union (.ofRange "a" "z") (.union (.ofRange "0" "9")
    (.union (s ".") (s "-")))) 1 10

#guard matches? okChars "test-str-1" == some true
#guard matches? okChars "test-str!" == some false
#guard matches? okChars "" == some false
#guard matches? okChars "0123456789a" == some false

/-! SMT-LIB edge cases and each operator on the empty string. -/

#guard matches? .none "" == some false
#guard matches? .none "a" == some false
#guard matches? .all "" == some true
#guard matches? .all "abc" == some true
#guard matches? (.ofRange "ab" "z") "b" == some false
#guard matches? (.ofRange "" "z") "a" == some false
#guard matches? (.ofRange "z" "a") "m" == some false
#guard matches? (.loop (s "a") 2 1) "aa" == some false
#guard matches? (.loop (.str []) 2 1) "" == some false
#guard matches? (.loop (.star (s "a")) 2 3) "" == some true
#guard matches? (.loop (s "a") 0 0) "" == some true
#guard matches? (.loop (s "a") 0 0) "a" == some false
#guard matches? (.comp (.comp (s "a"))) "a" == some true
#guard matches? (.comp (.comp (s "a"))) "b" == some false
#guard matches? (.star (.star (s "ab"))) "abab" == some true
#guard matches? (.star (.star (s "ab"))) "aba" == some false
#guard matches? (.plus (s "ab")) "ababab" == some true
#guard matches? (.plus (s "ab")) "" == some false
#guard matches? (.inter (.star .allChar) (.comp (s "x"))) "x" == some false
#guard matches? .allChar "é" == some true
#guard matches? .allChar "" == some false
#guard matches? (.range 'a' 'z') "" == some false
#guard matches? (s "a") "" == some false
#guard matches? (.cat .all (s "a")) "" == some false
#guard matches? (.cat .all .all) "" == some true
#guard matches? (.union (s "a") (.str [])) "" == some true
#guard matches? (.inter .all (s "a")) "" == some false
#guard matches? (.comp (s "a")) "" == some true
#guard matches? (.star (s "a")) "" == some true

/-- `rate(N days)` for 1 to 999 days, or `rate(N hours)` for 4 to 23. -/
private def rate : Re :=
  let digit := ofRange "0" "9"
  let nonZero := ofRange "1" "9"
  let days := .cat (.union nonZero (.union (.cat nonZero digit)
      (.cat nonZero (.cat digit digit))))
    (.union (s " day") (s " days"))
  let hours := .cat (.union (ofRange "4" "9") (.union (.cat (s "1") digit)
      (.cat (s "2") (ofRange "0" "3"))))
    (.union (s " hour") (s " hours"))
  .cat (s "rate(") (.cat (.union days hours) (s ")"))

#guard matches? rate "rate(30 days)" == some true
#guard matches? rate "rate(2 hours)" == some false
#guard matches? rate "rate(0 days)" == some false

/-! Union normalization keeps derivatives small, so these regexes are decided
on strings of 5,000 characters without reaching `maxSize`. -/

/-- The derivative of `r` by `str`, one character at a time. -/
private def derivs (r : Re) (str : String) : Re :=
  str.toList.foldl (fun r c => (r.derivNullable c).1) r

private def run (n : Nat) (x : String) : String :=
  String.join (List.replicate n x)

private def around (x : String) : Re := .cat .all (.cat (s x) .all)

-- `.*a.*` on a run of `a` and a run of `b`, with its derivative a few nodes.
#guard matches? (around "a") (run 5000 "a") == some true
#guard matches? (around "a") (run 5000 "b") == some false
#guard (derivs (around "a") (run 5000 "a")).sizeLe 10
-- `.*ab.*` on a run of `a`, without and with a final `b`.
#guard matches? (around "ab") (run 5000 "a") == some false
#guard (derivs (around "ab") (run 5000 "a")).sizeLe 20
#guard matches? (around "ab") (run 5000 "a" ++ "b") == some true

private def aOrB : Re := .union (s "a") (s "b")

/-- `(a|b)*a(a|b){k}`: the character `k + 1` from the end is `a`. -/
private def fromLast (k : Nat) : Re :=
  .cat (.star aOrB) (.cat (s "a") (.loop aOrB k k))

-- An `a` or a `b` eleven characters from the end of a long `ab` run.
#guard matches? (fromLast 10) (run 2495 "ab" ++ "a" ++ run 10 "b") ==
  some true
#guard matches? (fromLast 10) (run 2495 "ab" ++ run 11 "b") == some false

-- `(a|ab)*` on a long `ab` run, without and with a final `b`.
#guard matches? (.star (.union (s "a") (s "ab"))) (run 2500 "ab") ==
  some true
#guard matches? (.star (.union (s "a") (s "ab"))) (run 2500 "ab" ++ "b") ==
  some false

-- `(a*)*b` on a long run of `a`, with and without a final `b`.
#guard matches? (.cat (.star (.star (s "a"))) (s "b")) (run 5000 "a" ++ "b") ==
  some true
#guard matches? (.cat (.star (.star (s "a"))) (s "b")) (run 5000 "a") ==
  some false

/-! No answer: a code point above `0x2FFFF`, or an expression past `maxSize`.
The derivative of `stars 200` by `a` copies each suffix and exceeds
`maxSize`. -/

#guard (matches? .all (String.singleton (Char.ofNat 0x30000))).isNone
-- `0x2FFFF` itself is in the alphabet.
#guard matches? .all (String.singleton (Char.ofNat 0x2FFFF)) == some true

private def stars (n : Nat) : Re :=
  (List.range n).foldl (fun r _ => .cat (.star (s "a")) r) (.str [])

#guard matches? (stars 3000) "" == some true
#guard (matches? (stars 200) "a").isNone
#guard (matches? (stars 4000) "").isNone

/-- `k` nested `plus` of `"a"`: a tree of about `2^k` nodes that shares its
    subtrees. -/
private def nestedPlus (k : Nat) : Re :=
  (List.range k).foldl (fun r _ => .plus r) (s "a")

#guard matches? (nestedPlus 3) "aaa" == some true
#guard (matches? (nestedPlus 40) "a").isNone

end Strata.SMT.Regex.Tests

end
