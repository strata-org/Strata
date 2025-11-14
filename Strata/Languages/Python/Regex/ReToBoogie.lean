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
    return (mkApp (.op strToRegexFunc.name none) [strConst (toString c)])
  | .range c1 c2 =>
    return mkApp (.op reRangeFunc.name none) [strConst (toString c1), strConst (toString c2)]
  | .union r1 r2 =>
    let r1b ← toBoogie r1
    let r2b ← toBoogie r2
    return mkApp (.op reUnionFunc.name none) [r1b, r2b]
  | .concat r1 r2 =>
    let r1b ← toBoogie r1
    let r2b ← toBoogie r2
    return mkApp (.op reConcatFunc.name none) [r1b, r2b]
  | .star r =>
    let rb ← toBoogie r
    return mkApp (.op reStarFunc.name none) [rb]
  | .plus r =>
    let rb ← toBoogie r
    return mkApp (.op rePlusFunc.name none) [rb]
  | .optional r =>
    let rb ← toBoogie r
    return mkApp (.op reLoopFunc.name none) [rb, intConst 0, intConst 1]
  | .loop r min max =>
    let rb ← toBoogie r
    return mkApp (.op reLoopFunc.name none) [rb, intConst min, intConst max]
  | .anychar =>
    return mkApp (.op reAllCharFunc.name none) []
  | .group r => toBoogie r
  | .empty => return mkApp (.op strToRegexFunc.name none) [strConst ""]
  | .complement r =>
    let rb ← toBoogie r
    return mkApp (.op reCompFunc.name none) [rb]
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
-/
def pythonRegexToBoogie (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Except ParseError Boogie.Expression.Expr := do
  let asts ← parseAll pyRegex 0 []

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
    return mkApp (.op reNoneFunc.name none) []

  -- `filtered` does not have any anchors.
  let filtered := middle

  -- Handle empty pattern.
  if filtered.isEmpty then
    return mkApp (.op strToRegexFunc.name none) [strConst ""]

  -- Concatenate filtered ASTs.
  let core := match filtered with
    | [single] => single
    | head :: tail => tail.foldl RegexAST.concat head
    | [] => unreachable!

  -- Convert core pattern.
  let coreExpr ← RegexAST.toBoogie core

  -- Wrap with `Re.All` based on mode and anchors
  let reAll := mkApp (.op reAllFunc.name none) []
  let result := match mode, hasStartAnchor, hasEndAnchor with
    -- Explicit anchors always override match mode.
    | _, true, true =>
       -- ^pattern$ - exact match.
      coreExpr
    | _, true, false =>
      -- ^pattern - starts with.
      mkApp (.op reConcatFunc.name none) [coreExpr, reAll]
    | _, false, true =>
      -- pattern$ - ends with.
      mkApp (.op reConcatFunc.name none) [reAll, coreExpr]
    -- No anchors - apply match mode.
    | .fullmatch, false, false =>
      -- exact match
      coreExpr
    | .match, false, false =>
      -- match at start
      mkApp (.op reConcatFunc.name none) [coreExpr, reAll]
    | .search, false, false =>
      -- match anywhere
      mkApp (.op reConcatFunc.name none) [reAll, mkApp (.op reConcatFunc.name none) [coreExpr, reAll]]

  return result

-------------------------------------------------------------------------------

section Test.pythonRegexToBoogie

-- (unmatchable)
/-- info: ok: ~Re.None -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a^b" .fullmatch
         return (Std.format ans)

/-- info: ok: ~Re.None -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "^a^b" .fullmatch
         return (Std.format ans)

/-- info: ok: ~Re.None -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a$b" .fullmatch
         return (Std.format ans)

/-- info: ok: (~Re.Comp (~Str.ToRegEx #b)) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "[^b]" .fullmatch
         return (Std.format ans)

/-- info: ok: (~Re.Comp ((~Re.Range #A) #Z)) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "[^A-Z]" .fullmatch
         return (Std.format ans)

/-- info: ok: (~Re.Comp (~Str.ToRegEx #^)) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "[^^]" .fullmatch
         return (Std.format ans)

/-- info: ok: (~Str.ToRegEx #a) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a" .fullmatch
         return (Std.format ans)

-- match mode tests
/-- info: ok: ((~Re.Concat (~Str.ToRegEx #a)) ~Re.All) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a" .match
         return (Std.format ans)

-- search mode tests
/-- info: ok: ((~Re.Concat ~Re.All) ((~Re.Concat (~Str.ToRegEx #a)) ~Re.All)) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a" .search
         return (Std.format ans)

-- Explicit anchors override mode
/-- info: ok: (~Str.ToRegEx #a) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "^a$" .search
         return (Std.format ans)

/-- info: ok: ((~Re.Concat (~Str.ToRegEx #a)) ~Re.All) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "^a" .fullmatch
         return (Std.format ans)

/-- info: ok: ((~Re.Concat ~Re.All) (~Str.ToRegEx #a)) -/
#guard_msgs in
#eval do let ans ← pythonRegexToBoogie "a$" .match
         return (Std.format ans)

end Test.pythonRegexToBoogie

-------------------------------------------------------------------------------
