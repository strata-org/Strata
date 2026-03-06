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
Returns true if any node in `r` satisfies `p`, where `p` is intended to be used
for positional checks. As such, this does not recurse into
`.complement`: its child is a character-set description (`[^...]`) that
cannot contain positional nodes.
-/
private def RegexAST.anyNode (p : RegexAST → Bool) (r : RegexAST) : Bool :=
  p r || match r with
  | .concat r1 r2 => r1.anyNode p || r2.anyNode p
  | .union  r1 r2 => r1.anyNode p || r2.anyNode p
  | .star   r     => r.anyNode p
  | .plus   r     => r.anyNode p
  | .optional r   => r.anyNode p
  | .loop   r _ _ => r.anyNode p
  | .group  r     => r.anyNode p
  | _             => false

/-- Returns true if `r` contains an `anchor_end` (`$`) node anywhere. -/
def RegexAST.containsAnchorEnd (r : RegexAST) : Bool :=
  r.anyNode (· matches .anchor_end)

/-- Returns true if `r` contains an `anchor_start` (`^`) node anywhere. -/
def RegexAST.containsAnchorStart (r : RegexAST) : Bool :=
  r.anyNode (· matches .anchor_start)

/--
Returns true if `r` contains any character-matching node (char, range, anychar,
complement). Used to inform anchor interaction: when false, the regex can only
produce empty or none, regardless of the anchor context.
-/
def RegexAST.hasNonAnchorContent (r : RegexAST) : Bool :=
  r.anyNode (fun
    | .char _       => true
    | .range _ _    => true
    | .anychar      => true
    -- a complement class always matches one character
    | .complement _ => true
    | _             => false)

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

/--
Convert `r` to Core's expressions.

`atStart` should be `true` when nothing before `r` has consumed a character.
`atEnd` should be `true` when nothing after `r` will consume a character.

Intuition for `atStart` and `atEnd` flags: these flags are important
for preprocessing the regex to remove anchors, since SMTLib theory of strings
does not support them. We say an anchor "fires" when its appropriate positional
constraint is satisfied: `^` (`$`, resp.) fires when the current position is the
start of the string (end of the string, resp.). When an anchor fires, it
contributes an empty string to the regex, since anchors are zero-width
assertions. When an anchor does not fire (because it's in the wrong position),
then it contributes an unmatchable regex.

Now, when a non-consuming (possibly empty) sub-expression `X` is adjacent to `Y`
which carries an anchor, forwarding a flag to `Y` is wrong. If `X`
matches non-empty at runtime, `Y` is no longer at the perceived position, so the
anchor in `Y` should not fire. However, if `X` is consuming, its contribution is
never empty, so `Y`'s position relative to the string boundary is statically
determined at translation time and the flag can be forwarded.
-/
partial def RegexAST.toCore (r : RegexAST) (atStart atEnd : Bool) :
    Core.Expression.Expr :=
  match r with
  | .anchor_start =>
    if atStart then Core.emptyRegex else Core.unmatchableRegex
  | .anchor_end =>
    if atEnd then Core.emptyRegex else Core.unmatchableRegex
  | .char c =>
    (mkApp () (.op () strToRegexFunc.name none) [strConst () (toString c)])
  | .range c1 c2 =>
    mkApp () (.op () reRangeFunc.name none) [strConst () (toString c1), strConst () (toString c2)]
  | .anychar =>
    mkApp () (.op () reAllCharFunc.name none) []
  | .empty => Core.emptyRegex
  | .group r1 => toCore r1 atStart atEnd
  | .complement r =>
    -- atStart/atEnd are passed as false: the inner expression is a character-set
    -- description ([^...]) which never contains anchors, so position context is
    -- irrelevant.
    -- In SMTLib (and Core), `re.comp(X)` is complement over all strings (e.g.,
    -- the complement of a single character string would include multi-character
    -- string), so we intersect with `re.allchar()` to restrict to single
    -- characters, matching [^...] semantics.
    let rb := toCore r false false
    mkApp () (.op () reInterFunc.name none)
      [mkApp () (.op () reAllCharFunc.name none) [],
       mkApp () (.op () reCompFunc.name none) [rb]]
  | .plus r1 =>
    toCore (.concat r1 (.star r1)) atStart atEnd
  | .optional r1 =>
    toCore (.union .empty r1) atStart atEnd
  | .union r1 r2 =>
      let r1b := toCore r1 atStart atEnd
      let r2b := toCore r2 atStart atEnd
      mkApp () (.op () reUnionFunc.name none) [r1b, r2b]
  | .star r1 =>
    let r1b := toCore r1 atStart atEnd
    let r2b :=
      if alwaysConsume r1 || r1.containsAnchorStart || r1.containsAnchorEnd then
        let r1bStart    := toCore r1 atStart false
        let r1bMid      := toCore r1 false false
        let r1bEnd      := toCore r1 false atEnd
        let r1bMidStar := mkApp () (.op () reStarFunc.name none) [r1bMid]
        mkApp () (.op () reConcatFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1bStart, r1bMidStar], r1bEnd]
      else
        mkApp () (.op () reStarFunc.name none) [r1b]
    mkApp () (.op () reUnionFunc.name none)
      [mkApp () (.op () reUnionFunc.name none) [Core.emptyRegex, r1b], r2b]
  | .loop r1 n m =>
    match n, m with
    | 0, 0 => Core.emptyRegex
    | 0, 1 => toCore (.union .empty r1) atStart atEnd
    | 0, m => -- Note: m >= 2
      let r1b := toCore r1 atStart atEnd
      let r2b :=
        if alwaysConsume r1 || r1.containsAnchorStart || r1.containsAnchorEnd then
          let r1bStart := toCore r1 atStart false
          let r1bMid   := toCore r1 false false
          let r1bEnd   := toCore r1 false atEnd
          let r1bLoop  := mkApp () (.op () reLoopFunc.name none) [r1bMid, intConst () 0, intConst () (m-2)]
          mkApp () (.op () reConcatFunc.name none) [mkApp () (.op () reConcatFunc.name none) [r1bStart, r1bLoop], r1bEnd]
        else
          mkApp () (.op () reLoopFunc.name none) [r1b, intConst () 0, intConst () m]
      mkApp () (.op () reUnionFunc.name none)
            [mkApp () (.op () reUnionFunc.name none) [Core.emptyRegex, r1b],
            r2b]
    | _, _ =>
      toCore (.concat r1 (.loop r1 (n - 1) (m - 1))) atStart atEnd
  | .concat r1 r2 =>
    match (alwaysConsume r1), (alwaysConsume r2) with
    | true, true =>
      let r1b := toCore r1 atStart false
      let r2b := toCore r2 false atEnd
      mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | true, false =>
      -- `r1` always consumes; `r2` may be empty. `r1` might be last.
      -- When `atEnd=true` and `r1` contains `$`, passing `atEnd` to `r2` would
      -- let `r2` expand beyond the end marker (e.g. `a$.*` matching `"ab"`).
      -- So we split into two cases:
      -- Case 1: (`r2=""`, so `$` in `r1` fires at the true string end)
      -- Case 2: (`r2` non-empty, so `r2` is the last consumer and `r1` must not
      -- see `atEnd`).
      if atEnd && r1.containsAnchorEnd && r2.hasNonAnchorContent then
        let r1bEnd := toCore r1 atStart true
        let r1bMid := toCore r1 atStart false
        let r2b     := toCore r2 false true
        -- Restrict `r2` to `""` for Case 1 (`r2` is non-consuming, so
        -- intersection with `""` checks that `r2` can indeed match `""` here).
        let r2bEps := mkApp () (.op () reInterFunc.name none) [r2b, Core.emptyRegex]
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1bEnd, r2bEps],
           mkApp () (.op () reConcatFunc.name none) [r1bMid, r2b]]
      else
        let r1b := toCore r1 atStart atEnd
        let r2b := toCore r2 false atEnd
        mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, true =>
      -- `r2` always consumes; `r1` may be empty. `r2` might be first.
      -- Case 1: (`r1=""`, `r2` starts at original position, `atStart` propagates) and
      -- Case 2: (`r1` non-empty, `r2` starts after `r1`, `atStart` must not propagate).
      if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
        let r1b       := toCore r1 atStart false
        -- Restrict `r1` to "" for Case 1, as before.
        let r1bEps   := mkApp () (.op () reInterFunc.name none) [r1b, Core.emptyRegex]
        let r2bStart := toCore r2 atStart atEnd
        let r2bMid   := toCore r2 false atEnd
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1bEps, r2bStart],
           mkApp () (.op () reConcatFunc.name none) [r1b, r2bMid]]
      else
        let r1b := toCore r1 atStart false
        let r2b := toCore r2 atStart atEnd
        mkApp () (.op () reConcatFunc.name none) [r1b, r2b]
    | false, false =>
      -- Both sides may be empty.
      -- Case 1: (`r1=""`, `^` fires correctly) and
      -- Case 2: (`r1` non-empty, `^` must not fire, so `atStart=false` for `r2`).
      if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
        let r1b       := toCore r1 atStart atEnd
        let r1bEps   := mkApp () (.op () reInterFunc.name none) [r1b, Core.emptyRegex]
        let r2bStart := toCore r2 atStart atEnd
        let r2bMid   := toCore r2 false atEnd
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1bEps, r2bStart],
           mkApp () (.op () reConcatFunc.name none) [r1b, r2bMid]]
      -- Symmetric to `true, false`: when `$` is in `r1` and `r2` has non-anchor
      -- content, `r2` may match non-empty, in which case `r1` is not last and
      -- `atEnd` must not be forwarded to `r1`.
      -- Case 1: (`r2=""`, `r1` sees `atEnd`) and
      -- Case 2: (`r2` non-empty, `r1` must not see `atEnd`).
      else if atEnd && r1.containsAnchorEnd && r2.hasNonAnchorContent then
        let r1bEnd := toCore r1 atStart true
        let r1bMid := toCore r1 atStart false
        let r2b     := toCore r2 atStart true
        let r2bEps := mkApp () (.op () reInterFunc.name none) [r2b, Core.emptyRegex]
        mkApp () (.op () reUnionFunc.name none)
          [mkApp () (.op () reConcatFunc.name none) [r1bEnd, r2bEps],
           mkApp () (.op () reConcatFunc.name none) [r1bMid, r2b]]
      else
        let r1b := toCore r1 atStart atEnd
        let r2b := toCore r2 atStart atEnd
        mkApp () (.op () reConcatFunc.name none) [r1b, r2b]

def pythonRegexToCore (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Core.Expression.Expr × Option ParseError :=
  match parseTop pyRegex with
  | .error err => (mkApp () (.op () reAllFunc.name none) [], some err)
  | .ok ast =>
    let mkConcat a b := mkApp () (.op () reConcatFunc.name none) [a, b]
    let mkUnion  a b := mkApp () (.op () reUnionFunc.name none)  [a, b]
    -- dotStar: passed with `atStart=false`, `atEnd=false` since `anychar`
    -- ignores both.
    let dotStar := RegexAST.toCore (.star .anychar) false false
    -- We compute `toCore(ast, atStart, atEnd)` for each combination of anchor
    -- activation and union the results.  When `^` is present, the `atStart=false`
    -- variants yield unmatchable (`^` with `atStart=false` → `re.none()`), so
    -- those union branches vanish.  Likewise for `$` and `atEnd=false`.  This
    -- prevents anchors from being "swallowed" by a prepended/appended dotStar.
    let result := match mode with
    | .fullmatch => RegexAST.toCore ast true true
    | .match =>
        -- `atStart` always true (match anchors at string start).
        -- union: (1) `$` fires → no trailing content; (2) `$` absent → trailing .* .
        let core_tt := RegexAST.toCore ast true true
        let core_tf := RegexAST.toCore ast true false
        mkUnion core_tt (mkConcat core_tf dotStar)
    | .search =>
        -- Four combinations of (`^` active, `$` active).
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
