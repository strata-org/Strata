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

/-- Returns true if `r` contains an `anchor_end` (`$`) node anywhere. -/
def RegexAST.containsAnchorEnd (r : RegexAST) : Bool :=
  match r with
  | .anchor_end   => true
  | .concat r1 r2 => r1.containsAnchorEnd || r2.containsAnchorEnd
  | .union  r1 r2 => r1.containsAnchorEnd || r2.containsAnchorEnd
  | .star   r     => r.containsAnchorEnd
  | .plus   r     => r.containsAnchorEnd
  | .optional r   => r.containsAnchorEnd
  | .loop   r _ _ => r.containsAnchorEnd
  | .group  r     => r.containsAnchorEnd
  | _             => false

/-- Returns true if `r` contains an `anchor_start` (`^`) node anywhere. -/
def RegexAST.containsAnchorStart (r : RegexAST) : Bool :=
  match r with
  | .anchor_start => true
  | .concat r1 r2 => r1.containsAnchorStart || r2.containsAnchorStart
  | .union  r1 r2 => r1.containsAnchorStart || r2.containsAnchorStart
  | .star   r     => r.containsAnchorStart
  | .plus   r     => r.containsAnchorStart
  | .optional r   => r.containsAnchorStart
  | .loop   r _ _ => r.containsAnchorStart
  | .group  r     => r.containsAnchorStart
  | _             => false

/--
Returns true if `r` contains any character-matching node (char, range, anychar,
complement). Used to inform anchor interaction: when false, the regex can only
produce empty or none, regardless of the anchor context.
-/
def RegexAST.hasNonAnchorContent (r : RegexAST) : Bool :=
  match r with
  | .char _        => true
  | .range _ _     => true
  | .anychar       => true
  | .complement _  => true
  | .concat r1 r2  => r1.hasNonAnchorContent || r2.hasNonAnchorContent
  | .union  r1 r2  => r1.hasNonAnchorContent || r2.hasNonAnchorContent
  | .star   r      => r.hasNonAnchorContent
  | .plus   r      => r.hasNonAnchorContent
  | .optional r    => r.hasNonAnchorContent
  | .loop   r _ _  => r.hasNonAnchorContent
  | .group  r      => r.hasNonAnchorContent
  | _              => false

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
    -- atStart/atEnd are passed as false: the inner expression is a character-set
    -- description ([^...]) which never contains anchors, so position context is
    -- irrelevant. re.comp(X) is complement over all strings, so we intersect with
    -- re.allchar() to restrict to single characters, matching [^...] semantics.
    let rb := toCore r false false
    mkApp () (.op () reInterFunc.name none)
      [mkApp () (.op () reAllCharFunc.name none) [],
       mkApp () (.op () reCompFunc.name none) [rb]]
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
        -- When r1 contains anchors, re.*(toCore r1 atStart atEnd) is wrong:
        -- it passes the start/end context to every iteration, letting ^ or $ fire
        -- on all iterations instead of only the first or last (e.g. (^a?)* would
        -- translate to re.*(""│"a") which matches "aa", but Python says no match).
        -- Fix: apply the same first/middle/last split as | true =>.
        if r1.containsAnchorStart || r1.containsAnchorEnd then
          let r1b_start := toCore r1 atStart false
          let r1b_mid   := toCore r1 false false
          let r1b_end   := toCore r1 false atEnd
          let r1b_mid_star := mkApp () (.op () reStarFunc.name none) [r1b_mid]
          mkApp () (.op () reConcatFunc.name none)
            [mkApp () (.op () reConcatFunc.name none) [r1b_start, r1b_mid_star], r1b_end]
        else
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
                  -- Same anchor fix as star | false =>.
                  if r1.containsAnchorStart || r1.containsAnchorEnd then
                    let r1b_start := toCore r1 atStart false
                    let r1b_mid   := toCore r1 false false
                    let r1b_end   := toCore r1 false atEnd
                    let r1b_loop  := mkApp () (.op () reLoopFunc.name none) [r1b_mid, intConst () 0, intConst () (m-2)]
                    mkApp () (.op () reConcatFunc.name none) [mkApp () (.op () reConcatFunc.name none) [r1b_start, r1b_loop], r1b_end]
                  else
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
      -- r1 always consumes; r2 may be empty.
      -- When atEnd=true and r1 contains $, passing atEnd to r2 would let r2 expand
      -- beyond the end marker (e.g. a$.* matching "ab").  Fix: split into
      -- Case A (r2="", so $ in r1 fires at the true string end) and
      -- Case B (r2 non-empty, so r2 is the last consumer and r1 must not see atEnd).
      if atEnd && r1.containsAnchorEnd && r2.hasNonAnchorContent then
        let r1b_end := toCore r1 atStart true
        let r1b_mid := toCore r1 atStart false
        let r2b     := toCore r2 false true
        -- Restrict r2 to "" for Case A (r2 is non-consuming, so inter with "" works).
        let r2b_eps := mkApp () (.op () reInterFunc.name none) [r2b, Core.emptyRegex]
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1b_end, r2b_eps],
           mkApp () (.op () reConcatFunc.name none) [r1b_mid, r2b]]
      else
        let r1b := toCore r1 atStart atEnd
        let r2b := toCore r2 false atEnd
        mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, true =>
      -- r2 always consumes; r1 may be empty.
      -- The hardcoded atStart=true for r2 is wrong when r1 consumed non-empty content
      -- and r2 contains ^ (e.g. .*^a incorrectly matching "ba").  Fix: split into
      -- Case A (r1="", r2 starts at original position, atStart propagates) and
      -- Case B (r1 non-empty, r2 starts after r1, atStart must not propagate).
      if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
        let r1b       := toCore r1 atStart false
        -- Restrict r1 to "" for Case A (r1 is non-consuming, so inter with "" works).
        let r1b_eps   := mkApp () (.op () reInterFunc.name none) [r1b, Core.emptyRegex]
        let r2b_start := toCore r2 atStart atEnd
        let r2b_mid   := toCore r2 false atEnd
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1b_eps, r2b_start],
           mkApp () (.op () reConcatFunc.name none) [r1b, r2b_mid]]
      else
        let r1b := toCore r1 atStart false
        let r2b := toCore r2 true atEnd
        mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, false =>
      -- Both sides may be empty.  When atStart=true and r2 contains ^, passing
      -- atStart directly to r2 lets ^ fire even when r1 consumed non-empty content
      -- (e.g. .*^a, parsed as concat(concat(.*,^),a), hitting this case for concat(.*,^)).
      -- Fix: split into Case A (r1="", ^ fires correctly) and
      --      Case B (r1 non-empty, ^ must not fire, so atStart=false for r2).
      if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
        let r1b       := toCore r1 atStart atEnd
        let r1b_eps   := mkApp () (.op () reInterFunc.name none) [r1b, Core.emptyRegex]
        let r2b_start := toCore r2 atStart atEnd
        let r2b_mid   := toCore r2 false atEnd
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1b_eps, r2b_start],
           mkApp () (.op () reConcatFunc.name none) [r1b, r2b_mid]]
      else
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
    let mkConcat a b := mkApp () (.op () reConcatFunc.name none) [a, b]
    let mkUnion  a b := mkApp () (.op () reUnionFunc.name none)  [a, b]
    -- dotStar: passed with atStart=false, atEnd=false since anychar ignores both.
    let dotStar := RegexAST.toCore (.star .anychar) false false
    -- We compute toCore(ast, atStart, atEnd) for each combination of anchor
    -- activation and union the results.  When ^ is present, the atStart=false
    -- variants yield unmatchable (^ with atStart=false → re.none()), so those
    -- union branches vanish.  Likewise for $ and atEnd=false.  This correctly
    -- prevents anchors from being "swallowed" by a prepended/appended dotStar.
    let result := match mode with
    | .fullmatch => RegexAST.toCore ast true true
    | .match =>
        -- atStart always true (match anchors at string start).
        -- union: (1) $ fires → no trailing content; (2) $ absent → trailing .* .
        let core_tt := RegexAST.toCore ast true true
        let core_tf := RegexAST.toCore ast true false
        mkUnion core_tt (mkConcat core_tf dotStar)
    | .search =>
        -- Four combinations of (^ active, $ active).
        let core_tt := RegexAST.toCore ast true  true
        let core_tf := RegexAST.toCore ast true  false
        let core_ft := RegexAST.toCore ast false true
        let core_ff := RegexAST.toCore ast false false
        mkUnion core_tt
          (mkUnion (mkConcat core_tf dotStar)
            (mkUnion (mkConcat dotStar core_ft)
                     (mkConcat dotStar (mkConcat core_ff dotStar))))
    (result, none)

-------------------------------------------------------------------------------
