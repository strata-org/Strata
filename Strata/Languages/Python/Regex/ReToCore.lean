/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReParser
import Strata.Languages.Core.Factory

namespace Strata
namespace Python

-------------------------------------------------------------------------------

open Lambda.LExpr
open Core

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
def Core.emptyRegex : Core.Expression.Expr :=
  mkApp () (.op () strToRegexFunc.name none) [strConst () ""]

/--
Unmatchable regex pattern.
-/
def Core.unmatchableRegex : Core.Expression.Expr :=
  mkApp () (.op () reNoneFunc.name none) []

partial def RegexAST.toCore (r : RegexAST) (atStart atEnd : Bool) :
    Core.Expression.Expr :=
  match r with
  | .char c =>
    (mkApp () (.op () strToRegexFunc.name none) [strConst () (toString c)])
  | .range c1 c2 =>
    mkApp () (.op () reRangeFunc.name none) [strConst () (toString c1), strConst () (toString c2)]
  | .anychar =>
    mkApp () (.op () reAllCharFunc.name none) []
  | .empty => Core.emptyRegex
  | .complement r =>
    let rb := toCore r atStart atEnd
    mkApp () (.op () reCompFunc.name none) [rb]
  | .anchor_start =>
    if atStart then Core.emptyRegex else Core.unmatchableRegex
  | .anchor_end =>
    if atEnd then Core.emptyRegex else Core.unmatchableRegex
  | .plus r1 =>
    toCore (.concat r1 (.star r1)) atStart atEnd
  | .star r1 =>
    let r1b := toCore r1 atStart atEnd
    let r2b :=
      match (alwaysConsume r1) with
      | true =>
        let r1b := toCore r1 atStart false -- r1 at the beginning
        let r2b := toCore r1 false false   -- r1s in the middle
        let r3b := toCore r1 false atEnd   -- r1 at the end
        let r2b := mkApp () (.op () reStarFunc.name none) [r2b]
        mkApp () (.op () reConcatFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1b, r2b], r3b]
      | false =>
        mkApp () (.op () reStarFunc.name none) [r1b]
    mkApp () (.op () reUnionFunc.name none)
      [mkApp () (.op () reUnionFunc.name none) [Core.emptyRegex, r1b], r2b]
  | .optional r1 =>
    toCore (.union .empty r1) atStart atEnd
  | .loop r1 n m =>
    match n, m with
    | 0, 0 => Core.emptyRegex
    | 0, 1 => toCore (.union .empty r1) atStart atEnd
    | 0, m => -- Note: m >= 2
      let r1b := toCore r1 atStart atEnd
      let r2b := match (alwaysConsume r1) with
                | true =>
                  let r1b := toCore r1 atStart false -- r1 at the beginning
                  let r2b := toCore r1 false false   -- r1s in the middle
                  let r3b := toCore r1 false atEnd   -- r1 at the end
                  let r2b := mkApp () (.op () reLoopFunc.name none) [r2b, intConst () 0, intConst () (m-2)]
                  mkApp () (.op () reConcatFunc.name none) [mkApp () (.op () reConcatFunc.name none) [r1b, r2b], r3b]
                | false =>
                  mkApp () (.op () reLoopFunc.name none) [r1b, intConst () 0, intConst () m]
      mkApp () (.op () reUnionFunc.name none)
            [mkApp () (.op () reUnionFunc.name none) [Core.emptyRegex, r1b],
            r2b]
    | _, _ =>
      toCore (.concat r1 (.loop r1 (n - 1) (m - 1))) atStart atEnd
  | .group r1 => toCore r1 atStart atEnd
  | .concat r1 r2 =>
    match (alwaysConsume r1), (alwaysConsume r2) with
    | true, true =>
      let r1b := toCore r1 atStart false
      let r2b := toCore r2 false atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | true, false =>
      let r1b := toCore r1 atStart atEnd
      let r2b := toCore r2 false atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, true =>
      let r1b := toCore r1 atStart false
      let r2b := toCore r2 true atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, false =>
      let r1b := toCore r1 atStart atEnd
      let r2b := toCore r2 atStart atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
  | .union r1 r2 =>
      let r1b := toCore r1 atStart atEnd
      let r2b := toCore r2 atStart atEnd
      mkApp () (.op () reUnionFunc.name none) [r1b, r2b]

def pythonRegexToCore (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Core.Expression.Expr × Option ParseError :=
  match parseTop pyRegex with
  | .error err => (mkApp () (.op () reAllFunc.name none) [], some err)
  | .ok ast =>
    let dotStar := (RegexAST.star (.anychar))
    -- Wrap with `.*` based on mode.
    let ast := match mode with
    | .fullmatch => ast
    | .match => .concat ast dotStar
    | .search => .concat dotStar (.concat ast dotStar)
    let result := RegexAST.toCore ast true true
    (result, none)

-------------------------------------------------------------------------------
