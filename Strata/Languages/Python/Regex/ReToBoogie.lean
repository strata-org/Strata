/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReParser
import Strata.Languages.Boogie.Factory

namespace Strata
namespace Python

-------------------------------------------------------------------------------

open Lambda.LExpr
open Boogie

/--
Python regexes can be interpreted differently based on the matching mode.

Consider the regex pattern that does not contain any anchors: `x`.
For search, this is equivalent to `.*x.*`.
For match, this is equivalent to `x.*`.
For fullmatch, this is exactly `x`.

Consider the regex pattern: `^x`.
For search, this is equivalent to `x.*`.
For match, this is equivalent to `x.*`.
Again for fullmatch, this is exactly `x`.

Consider the regex pattern: `x$`.
For search, this is equivalent to `.*x`.
For match, this is equivalent to `x`.
Again for fullmatch, this is exactly `x`.

Consider the regex pattern: `^x$`.
For search, match, and fullmatch, this is equivalent to `x`.
-/
inductive MatchMode where
  | search     -- `re.search()`    - match anywhere in string
  | match      -- `re.match()`     - match at start of string
  | fullmatch  -- `re.fullmatch()` - match entire string
  deriving Repr, BEq

/--
When `r` is definitely consuming, this function returns `true`.
Returns `false` otherwise (i.e., when it _may_ not be consuming).
-/
def RegexAST.alwaysConsume (r : RegexAST) : Bool :=
  match r with
  | .char _ => true
  | .range _ _ => true
  | .union r1 r2 => alwaysConsume r1 && alwaysConsume r2
  | .concat r1 r2 => alwaysConsume r1 || alwaysConsume r2
  | .anychar => true
  | .star _ => false
  | .plus r1 => alwaysConsume r1
  | .optional _ => false
  | .loop r1 n _ => alwaysConsume r1 && n ≠ 0
  | .anchor_start => false
  | .anchor_end => false
  | .group r1 => alwaysConsume r1
  | .empty => false
  | .complement _ => true

/--
Empty regex pattern; matches an empty string.
-/
def Boogie.emptyRegex : Boogie.Expression.Expr :=
  mkApp () (.op () strToRegexFunc.name none) [strConst () ""]

/--
Unmatchable regex pattern.
-/
def Boogie.unmatchableRegex : Boogie.Expression.Expr :=
  mkApp () (.op () reNoneFunc.name none) []

partial def RegexAST.toBoogie (r : RegexAST) (atStart atEnd : Bool) :
    Boogie.Expression.Expr :=
  match r with
  | .char c =>
    (mkApp () (.op () strToRegexFunc.name none) [strConst () (toString c)])
  | .range c1 c2 =>
    mkApp () (.op () reRangeFunc.name none) [strConst () (toString c1), strConst () (toString c2)]
  | .anychar =>
    mkApp () (.op () reAllCharFunc.name none) []
  | .empty => Boogie.emptyRegex
  | .complement r =>
    let rb := toBoogie r atStart atEnd
    mkApp () (.op () reCompFunc.name none) [rb]
  | .anchor_start =>
    if atStart then Boogie.emptyRegex else Boogie.unmatchableRegex
  | .anchor_end =>
    if atEnd then Boogie.emptyRegex else Boogie.unmatchableRegex
  | .plus r1 =>
    toBoogie (.concat r1 (.star r1)) atStart atEnd
  | .star r1 =>
    let r1b := toBoogie r1 atStart atEnd
    let r2b :=
      match (alwaysConsume r1) with
      | true =>
        let r1b := toBoogie r1 atStart false -- r1 at the beginning
        let r2b := toBoogie r1 false false   -- r1s in the middle
        let r3b := toBoogie r1 false atEnd   -- r1 at the end
        let r2b := mkApp () (.op () reStarFunc.name none) [r2b]
        mkApp () (.op () reConcatFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1b, r2b], r3b]
      | false =>
        mkApp () (.op () reStarFunc.name none) [r1b]
    mkApp () (.op () reUnionFunc.name none)
      [mkApp () (.op () reUnionFunc.name none) [Boogie.emptyRegex, r1b], r2b]
  | .optional r1 =>
    toBoogie (.union .empty r1) atStart atEnd
  | .loop r1 n m =>
    match n, m with
    | 0, 0 => Boogie.emptyRegex
    | 0, 1 => toBoogie (.union .empty r1) atStart atEnd
    | 0, m => -- Note: m >= 2
      let r1b := toBoogie r1 atStart atEnd
      let r2b := match (alwaysConsume r1) with
                | true =>
                  let r1b := toBoogie r1 atStart false -- r1 at the beginning
                  let r2b := toBoogie r1 false false   -- r1s in the middle
                  let r3b := toBoogie r1 false atEnd   -- r1 at the end
                  let r2b := mkApp () (.op () reLoopFunc.name none) [r2b, intConst () 0, intConst () (m-2)]
                  mkApp () (.op () reConcatFunc.name none) [mkApp () (.op () reConcatFunc.name none) [r1b, r2b], r3b]
                | false =>
                  mkApp () (.op () reLoopFunc.name none) [r1b, intConst () 0, intConst () m]
      mkApp () (.op () reUnionFunc.name none)
            [mkApp () (.op () reUnionFunc.name none) [Boogie.emptyRegex, r1b],
            r2b]
    | _, _ =>
      toBoogie (.concat r1 (.loop r1 (n - 1) (m - 1))) atStart atEnd
  | .group r1 => toBoogie r1 atStart atEnd
  | .concat r1 r2 =>
    match (alwaysConsume r1), (alwaysConsume r2) with
    | true, true =>
      let r1b := toBoogie r1 atStart false
      let r2b := toBoogie r2 false atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | true, false =>
      let r1b := toBoogie r1 atStart atEnd
      let r2b := toBoogie r2 false atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, true =>
      let r1b := toBoogie r1 atStart false
      let r2b := toBoogie r2 true atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, false =>
      let r1b := toBoogie r1 atStart atEnd
      let r2b := toBoogie r2 atStart atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
  | .union r1 r2 =>
      let r1b := toBoogie r1 atStart atEnd
      let r2b := toBoogie r2 atStart atEnd
      mkApp () (.op () reUnionFunc.name none) [r1b, r2b]

def pythonRegexToBoogie (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Boogie.Expression.Expr × Option ParseError :=
  match parseTop pyRegex with
  | .error err => (mkApp () (.op () reAllFunc.name none) [], some err)
  | .ok ast =>
    let dotStar := (RegexAST.star (.anychar))
    -- Wrap with `.*` based on mode.
    let ast := match mode with
    | .fullmatch => ast
    | .match => .concat ast dotStar
    | .search => .concat dotStar (.concat ast dotStar)
    let result := RegexAST.toBoogie ast true true
    (result, none)

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) (~Str.ToRegEx #b))) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "ab.*" -- Encoded as `ab(|.|..*.)`

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) (~Str.ToRegEx #b))) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ((~Re.Concat (~Str.ToRegEx #c)) (~Str.ToRegEx #)))) ((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #c)) ~Re.None)) (~Re.Star ((~Re.Concat (~Str.ToRegEx #c)) ~Re.None)))) ((~Re.Concat (~Str.ToRegEx #c)) (~Str.ToRegEx #))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "ab(c$)*"

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) (~Str.ToRegEx #b))) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ((~Re.Concat ((~Re.Concat ~Re.None) (~Str.ToRegEx #c))) (~Str.ToRegEx #)))) ((~Re.Concat ((~Re.Concat ((~Re.Concat ((~Re.Concat ~Re.None) (~Str.ToRegEx #c))) ~Re.None)) (~Re.Star ((~Re.Concat ((~Re.Concat ~Re.None) (~Str.ToRegEx #c))) ~Re.None)))) ((~Re.Concat ((~Re.Concat ~Re.None) (~Str.ToRegEx #c))) (~Str.ToRegEx #))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "ab(^c$)*"

/-- info: (((~Re.Concat (~Str.ToRegEx #a)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "ab"

/-- info: (((~Re.Union (~Str.ToRegEx #a)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "a|b"

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "^ab"

/--
info: (((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #b))) (~Str.ToRegEx #)),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "^ab$"

/-- info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToBoogie "(a$)b"

/--
info: (((~Re.Concat ((~Re.Concat ((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #))) (~Str.ToRegEx #))) (~Str.ToRegEx #a))) (~Str.ToRegEx #))) (~Str.ToRegEx #)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^^^a$$"

/--
info: (((~Re.Concat (~Str.ToRegEx #)) ((~Re.Concat ((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #))) (~Str.ToRegEx #a))) (~Str.ToRegEx #))) (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^(^^a$$)"

/--
info: (((~Re.Union ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #))) ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #b))) (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "(^a$)|(^b$)"

/--
info: (((~Re.Concat (~Str.ToRegEx #c)) ((~Re.Union ((~Re.Concat ~Re.None) (~Str.ToRegEx #a))) ((~Re.Concat ~Re.None) (~Str.ToRegEx #b)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "c((^a)|(^b))"

/--
info: (((~Re.Concat ((~Re.Union ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) ((~Re.Concat (~Str.ToRegEx #b)) ~Re.None))) (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "((a$)|(b$))c"

/--
info: (((~Re.Concat ((~Re.Union ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) (~Str.ToRegEx #b))) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "((a$)|(b))c"

/--
info: (((~Re.Concat (~Str.ToRegEx #c)) ((~Re.Union ((~Re.Concat (~Str.ToRegEx #a)) (~Str.ToRegEx #))) ((~Re.Concat ((~Re.Concat ~Re.None) (~Str.ToRegEx #b))) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "c((a$)|(^b$))"

/--
info: (((~Re.Concat ((~Re.Union ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) (~Str.ToRegEx #b))) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "((a$)|(b))c"

/-- info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) ~Re.None)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^$b"

/--
info: (((~Re.Union ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #))) ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) ~Re.None)) (~Str.ToRegEx #b))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a$|^$b"

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #c)) ((~Re.Union ((~Re.Concat ~Re.None) (~Str.ToRegEx #a))) ((~Re.Concat (~Str.ToRegEx #b)) ~Re.None)))) (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "c(^a|b$)d"

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #c)) ((~Re.Union ((~Re.Concat ~Re.None) (~Str.ToRegEx #a))) ((~Re.Concat (~Str.ToRegEx #b)) ~Re.None)))) (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "(c(^a|b$))d"

/--
info: (((~Re.Concat ((~Re.Union ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) ((~Re.Concat (~Str.ToRegEx #b)) ~Re.None))) ((~Re.Union ((~Re.Concat ~Re.None) (~Str.ToRegEx #c))) ((~Re.Concat (~Str.ToRegEx #d)) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "(^a|b$)(^c|d$)"

/--
info: (((~Re.Concat ((~Re.Concat ((~Re.Union ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) ((~Re.Concat (~Str.ToRegEx #b)) ~Re.None))) ~Re.None)) (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "((^a|b$)^)c"

/-- info: (((~Re.Concat ((~Re.Union (~Str.ToRegEx #)) ~Re.None)) (~Str.ToRegEx #c)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "(^|$)c"

/-- info: (((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^^"

/--
info: (((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #))) (~Str.ToRegEx #))) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^$$^"

/-- info: (((~Re.Concat ((~Re.Union (~Str.ToRegEx #)) (~Str.ToRegEx #))) (~Str.ToRegEx #)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "(^|$)^"

/--
info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a$" .fullmatch

/--
info: (~Re.All,
 some Pattern error at position 1: Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100 in pattern 'x{100,2}')
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "x{100,2}" .fullmatch

-- (unmatchable)
/-- info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a^b" .fullmatch

/--
info: (((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) ~Re.None)) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a^b" .fullmatch

/-- info: (((~Re.Concat ((~Re.Concat (~Str.ToRegEx #a)) ~Re.None)) (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a$b" .fullmatch

/-- info: ((~Re.Comp (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "[^b]" .fullmatch

/-- info: ((~Re.Comp ((~Re.Range #A) #Z)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "[^A-Z]" .fullmatch

/-- info: ((~Re.Comp (~Str.ToRegEx #^)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "[^^]" .fullmatch

/-- info: ((~Str.ToRegEx #a), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a" .fullmatch

/--
info: (((~Re.Concat (~Str.ToRegEx #a)) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a" .match

-- search mode tests
/--
info: (((~Re.Concat ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar))) ((~Re.Concat (~Str.ToRegEx #a)) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a" .search

/--
info: (((~Re.Concat ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar))) ((~Re.Concat ((~Re.Concat ((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a))) (~Str.ToRegEx #))) ((~Re.Union ((~Re.Union (~Str.ToRegEx #)) ~Re.AllChar)) ((~Re.Concat ((~Re.Concat ~Re.AllChar) (~Re.Star ~Re.AllChar))) ~Re.AllChar)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a$" .search

/-- info: (((~Re.Concat (~Str.ToRegEx #)) (~Str.ToRegEx #a)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a" .fullmatch

-- -- BAD
-- #eval Std.format $ pythonRegexToBoogie "a$.*" .fullmatch
--
-- -- BAD
-- #eval Std.format $ pythonRegexToBoogie "a$" .match


-------------------------------------------------------------------------------
