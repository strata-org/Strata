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
Map `RegexAST` nodes to Boogie expressions. Note that anchor nodes are not
handled here. See `pythonRegexToBoogie` for a preprocessing pass.
-/
def RegexAST.toBoogie (ast : RegexAST) : Except ParseError Boogie.Expression.Expr := do
  match ast with
  | .char c =>
    return (mkApp () (.op () strToRegexFunc.name none) [strConst () (toString c)])
  | .range c1 c2 =>
    return mkApp () (.op () reRangeFunc.name none) [strConst () (toString c1), strConst () (toString c2)]
  | .union r1 r2 =>
    let r1b ← toBoogie r1
    let r2b ← toBoogie r2
    return mkApp () (.op () reUnionFunc.name none) [r1b, r2b]
  | .concat r1 r2 =>
    let r1b ← toBoogie r1
    let r2b ← toBoogie r2
    return mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
  | .star r =>
    let rb ← toBoogie r
    return mkApp () (.op () reStarFunc.name none) [rb]
  | .plus r =>
    let rb ← toBoogie r
    return mkApp () (.op () rePlusFunc.name none) [rb]
  | .optional r =>
    let rb ← toBoogie r
    return mkApp () (.op () reLoopFunc.name none) [rb, intConst () 0, intConst () 1]
  | .loop r min max =>
    let rb ← toBoogie r
    return mkApp () (.op () reLoopFunc.name none) [rb, intConst () min, intConst () max]
  | .anychar =>
    return mkApp () (.op () reAllCharFunc.name none) []
  | .group r => toBoogie r
  | .empty => return mkApp () (.op () strToRegexFunc.name none) [strConst () ""]
  | .complement r =>
    let rb ← toBoogie r
    return mkApp () (.op () reCompFunc.name none) [rb]
  | .anchor_start => throw (.patternError "Anchor should not appear in AST conversion" "" 0)
  | .anchor_end => throw (.patternError "Anchor should not appear in AST conversion" "" 0)

/--
Python regexes can be interpreted differently based on the matching mode.
Consider the regex pattern `x`.
For search, this is equivalent to `.*x.*`.
For match, this is equivalent to `x.*`.
For full match, this is exactly `x`.
-/
inductive MatchMode where
  | search     -- `re.search()`    - match anywhere in string
  | match      -- `re.match()`     - match at start of string
  | fullmatch  -- `re.fullmatch()` - match entire string
  deriving Repr, BEq


/--
Map `pyRegex` -- a string indicating a regular expression pattern -- to a
corresponding Boogie expression, taking match mode semantics into account.
Returns a pair of (result, optional error). On error, returns `re.all` as
fallback.
-/
def pythonRegexToBoogie (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Boogie.Expression.Expr × Option ParseError :=
  let reAll  := mkApp () (.op () reAllFunc.name none) []
  match parseAll pyRegex 0 [] with
  | .error err => (reAll, some err)
  | .ok asts =>

  -- Detect start and end anchors, if any.
  let hasStartAnchor := match asts.head? with | some .anchor_start => true | _ => false
  let hasEndAnchor := match asts.getLast? with | some .anchor_end => true | _ => false

  -- Check for anchors in middle positions.
  let middle := if hasStartAnchor then asts.tail else asts
  let middle := if hasEndAnchor && !middle.isEmpty then middle.dropLast else middle
  let hasMiddleAnchor := middle.any (fun ast => match ast with | .anchor_start | .anchor_end => true | _ => false)

    -- If anchors in middle, return `re.none` (unmatchable pattern).
    -- NOTE: this is a heavy-ish semantic transform.
    if hasMiddleAnchor then
      let reNone := mkApp () (.op () reNoneFunc.name none) []
      (reNone, none)
    else

      -- `filtered` does not have any anchors.
      let filtered := middle

      -- Handle empty pattern.
      if filtered.isEmpty then
        (mkApp () (.op () strToRegexFunc.name none) [strConst () ""], none)
      else
        -- Concatenate filtered ASTs.
        let core := match filtered with
          | [single] => single
          | head :: tail => tail.foldl RegexAST.concat head
          | [] => unreachable!

        -- Convert core pattern.
        match RegexAST.toBoogie core with
        | .error err => (reAll, some err)
        | .ok coreExpr =>
          -- Wrap with `Re.All` based on mode and anchors
          let result := match mode, hasStartAnchor, hasEndAnchor with
            -- Explicit anchors always override match mode.
            | _, true, true =>
               -- ^pattern$ - exact match.
              coreExpr
            | _, true, false =>
              -- ^pattern - starts with.
              mkApp () (.op () reConcatFunc.name none) [coreExpr, reAll]
            | _, false, true =>
              -- pattern$ - ends with.
              mkApp () (.op () reConcatFunc.name none) [reAll, coreExpr]
            -- No anchors - apply match mode.
            | .fullmatch, false, false =>
              -- exact match
              coreExpr
            | .match, false, false =>
              -- match at start
              mkApp () (.op () reConcatFunc.name none) [coreExpr, reAll]
            | .search, false, false =>
              -- match anywhere
              mkApp () (.op () reConcatFunc.name none) [reAll, mkApp () (.op () reConcatFunc.name none) [coreExpr, reAll]]
          (result, none)

-------------------------------------------------------------------------------

section Test.pythonRegexToBoogie


/--
info: (~Re.All,
 some Pattern error at position 1: Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100 in pattern 'x{100,2}')
-/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "x{100,2}" .fullmatch

-- (unmatchable)
/-- info: (~Re.None, none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a^b" .fullmatch

/-- info: (~Re.None, none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a^b" .fullmatch

/-- info: (~Re.None, none) -/
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

/-- info: (((~Re.Concat (~Str.ToRegEx #a)) ~Re.All), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a" .match

-- search mode tests
/-- info: (((~Re.Concat ~Re.All) ((~Re.Concat (~Str.ToRegEx #a)) ~Re.All)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a" .search

/-- info: ((~Str.ToRegEx #a), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a$" .search

/-- info: (((~Re.Concat (~Str.ToRegEx #a)) ~Re.All), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "^a" .fullmatch

/-- info: (((~Re.Concat ~Re.All) (~Str.ToRegEx #a)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToBoogie "a$" .match

end Test.pythonRegexToBoogie

-------------------------------------------------------------------------------
