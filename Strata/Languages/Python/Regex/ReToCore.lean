/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.Regex.ReParser
public import Strata.Languages.Core.Factory

namespace Strata
namespace Python

-- Regex-to-Core translation builds Core expressions from parsed regex AST
-- nodes. These synthesized expressions carry `SourceRange.none` because
-- the regex AST has no source range metadata.

public section

-------------------------------------------------------------------------------

open Lambda.LExpr
open Lambda.LTy.Syntax
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
private def RegexAST.alwaysConsume (r : RegexAST) : Bool :=
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
private def RegexAST.containsAnchorEnd (r : RegexAST) : Bool :=
  r.anyNode (· matches .anchor_end)

/-- Returns true if `r` contains an `anchor_start` (`^`) node anywhere. -/
private def RegexAST.containsAnchorStart (r : RegexAST) : Bool :=
  r.anyNode (· matches .anchor_start)

/--
Returns true if `r` contains any character-matching node (char, range, anychar,
complement). Used to inform anchor interaction: when false, the regex can only
produce empty or none, regardless of the anchor context.
-/
private def RegexAST.hasNonAnchorContent (r : RegexAST) : Bool :=
  r.anyNode (fun
    | .char _       => true
    | .range _ _    => true
    | .anychar      => true
    -- a complement class always matches one character
    | .complement _ => true
    | _             => false)

-- Type annotations for regex ops.  concreteEval runs after the type-checker,
-- so expressions it produces must already carry annotations for the SMT encoder.
private def reTy  := mty[regex]
private def s2r   := mty[string → regex]
private def r2r   := mty[regex → regex]
private def rr2r  := mty[regex → (regex → regex)]
private def ss2r  := mty[string → (string → regex)]
private def rii2r := mty[regex → (int → (int → regex))]

/--
Empty regex pattern; matches an empty string.
-/
private def Core.emptyRegex : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none strToRegexFunc.name (some s2r)) [strConst Strata.SourceRange.none ""]

/--
Unmatchable regex pattern.
-/
private def Core.unmatchableRegex : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reNoneFunc.name (some reTy)) []

-- Core regex expression builders.
private abbrev mkReFromStr (s : String) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none strToRegexFunc.name (some s2r)) [strConst Strata.SourceRange.none s]
private abbrev mkReRange   (c1 c2 : Char) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reRangeFunc.name (some ss2r)) [strConst Strata.SourceRange.none (toString c1), strConst Strata.SourceRange.none (toString c2)]
private abbrev mkReAllChar : Expression.Expr :=
  .op Strata.SourceRange.none reAllCharFunc.name (some reTy)
private abbrev mkReComp    (r : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reCompFunc.name (some r2r)) [r]
private abbrev mkReUnion   (a b : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reUnionFunc.name (some rr2r)) [a, b]
private abbrev mkReConcat  (a b : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reConcatFunc.name (some rr2r)) [a, b]
private abbrev mkReInter   (a b : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reInterFunc.name (some rr2r)) [a, b]
private abbrev mkReStar    (r   : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reStarFunc.name (some r2r)) [r]
private abbrev mkRePlus    (r   : Expression.Expr) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none rePlusFunc.name (some r2r)) [r]
private abbrev mkReLoop    (r   : Expression.Expr) (lo hi : Nat) : Expression.Expr :=
  mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reLoopFunc.name (some rii2r)) [r, intConst Strata.SourceRange.none lo, intConst Strata.SourceRange.none hi]

/--
Shared body for `star` and `loop {0, m}` (m ≥ 2):
  `union(union(empty, r1b), r2b)`
where `r2b` uses a split or simple path depending on whether `inner`
always consumes or contains an anchor.
- `simple r` wraps `r` for the no-split path (e.g. `mkReStar`).
- `center r` wraps `r` for the middle repetition in the split path
  (e.g. `mkReStar` for `star`; `mkReLoop · 0 (m-2)` for `loop {0,m}`).
- `rec s e` computes `toCore inner s e`.
-/
private def toCoreStarBody (inner : RegexAST)
    (simple center : Core.Expression.Expr → Core.Expression.Expr)
    (atStart atEnd : Bool)
    (rec : Bool → Bool → Core.Expression.Expr) : Core.Expression.Expr :=
  let r1b := rec atStart atEnd
  let r2b :=
    if inner.alwaysConsume || inner.containsAnchorStart || inner.containsAnchorEnd then
      let r1bStart := rec atStart false
      let r1bMid   := rec false false
      let r1bEnd   := rec false atEnd
      mkReConcat (mkReConcat r1bStart (center r1bMid)) r1bEnd
    else
      simple r1b
  mkReUnion (mkReUnion Core.emptyRegex r1b) r2b

/--
`endSplit r1End r1Mid r2`: the `$`-in-r1 split for `concat`:
  union(concat(r1End, r2∩ε), concat(r1Mid, r2))
Case 1: r2="" (intersection with ε forces this), r1 sees atEnd=true (r1End).
Case 2: r2 non-empty, r1 must not see atEnd (r1Mid).
-/
private abbrev endSplit (r1End r1Mid r2 : Core.Expression.Expr) : Core.Expression.Expr :=
  mkReUnion (mkReConcat r1End (mkReInter r2 Core.emptyRegex)) (mkReConcat r1Mid r2)

/--
`startSplit r1 r2Start r2Mid`: the `^`-in-r2 split for `concat`:
  union(concat(r1∩ε, r2Start), concat(r1, r2Mid))
Case 1: r1="" (intersection with ε forces this), r2 sees atStart=true (r2Start).
Case 2: r1 non-empty, r2 must not see atStart (r2Mid).
-/
private abbrev startSplit (r1 r2Start r2Mid : Core.Expression.Expr) : Core.Expression.Expr :=
  mkReUnion (mkReConcat (mkReInter r1 Core.emptyRegex) r2Start) (mkReConcat r1 r2Mid)

/--
Shared concat logic for `.concat` and `.plus`.
`r1` and `r2` supply the structural data for anchor/consume checks;
`rec1`/`rec2` are their translations (called as `rec1 atStart atEnd`, etc.).
Made `abbrev` so the body is transparent to the termination checker.
-/
private abbrev toCoreConcat (r1 r2 : RegexAST) (atStart atEnd : Bool)
    (rec1 rec2 : Bool → Bool → Core.Expression.Expr) : Core.Expression.Expr :=
  match r1.alwaysConsume, r2.alwaysConsume with
  | true, true =>
    mkReConcat (rec1 atStart false) (rec2 false atEnd)
  | true, false =>
    if atEnd && r1.containsAnchorEnd && r2.hasNonAnchorContent then
      endSplit (rec1 atStart true) (rec1 atStart false) (rec2 false true)
    else
      mkReConcat (rec1 atStart atEnd) (rec2 false atEnd)
  | false, true =>
    if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
      let r1b := rec1 atStart false
      startSplit r1b (rec2 atStart atEnd) (rec2 false atEnd)
    else
      mkReConcat (rec1 atStart false) (rec2 atStart atEnd)
  | false, false =>
    if atStart && r2.containsAnchorStart && r1.hasNonAnchorContent then
      let r1b := rec1 atStart atEnd
      startSplit r1b (rec2 atStart atEnd) (rec2 false atEnd)
    else if atEnd && r1.containsAnchorEnd && r2.hasNonAnchorContent then
      endSplit (rec1 atStart true) (rec1 atStart false) (rec2 atStart true)
    else
      mkReConcat (rec1 atStart atEnd) (rec2 atStart atEnd)

/--
Shared loop logic for `.loop`. Recurses on `n`; `recInner` translates `r1`
(called as `recInner atStart atEnd`, etc.), so all inner calls are structural
in the original `.loop` node when invoked as `toCoreLoop r1 n m ... (toCore r1)`.
-/
private def toCoreLoop (r1 : RegexAST) (n m : Nat) (atStart atEnd : Bool)
    (recInner : Bool → Bool → Core.Expression.Expr) : Core.Expression.Expr :=
  match n, m with
  | 0, 0 => Core.emptyRegex
  | 0, 1 => mkReUnion Core.emptyRegex (recInner atStart atEnd)
  | 0, _ => -- m >= 2
    toCoreStarBody r1 (mkReLoop · 0 m) (mkReLoop · 0 (m - 2)) atStart atEnd recInner
  | n + 1, _ =>
    if !r1.containsAnchorStart && !r1.containsAnchorEnd then
      -- No anchors: all repetitions are identical, emit re.loop directly.
      mkReLoop (recInner false false) (n + 1) m
    else
      -- Anchors present: expand as concat(r1, loop(r1, n, m-1)) so each iteration
      -- gets the correct atStart/atEnd context.
      toCoreConcat r1 (.loop r1 n (m - 1)) atStart atEnd
        recInner
        (fun s e => toCoreLoop r1 n (m - 1) s e recInner)

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
private def RegexAST.toCore (r : RegexAST) (atStart atEnd : Bool) :
    Core.Expression.Expr :=
  match r with
  | .anchor_start =>
    if atStart then Core.emptyRegex else Core.unmatchableRegex
  | .anchor_end =>
    if atEnd then Core.emptyRegex else Core.unmatchableRegex
  | .char c => mkReFromStr (toString c)
  | .range c1 c2 => mkReRange c1 c2
  | .anychar => mkReAllChar
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
    mkReInter mkReAllChar (mkReComp (toCore r false false))
  | .plus r1 =>
    if !r1.containsAnchorStart && !r1.containsAnchorEnd then
      -- No anchors: all repetitions are identical, emit re.+ directly.
      mkRePlus (toCore r1 atStart atEnd)
    else
      -- Anchors present: expand as concat(r1, star(r1)) so each iteration
      -- gets the correct atStart/atEnd context.
      toCoreConcat r1 (.star r1) atStart atEnd
        (toCore r1)
        (fun s e => toCoreStarBody r1 mkReStar mkReStar s e (toCore r1))
  | .optional r1 =>
    mkReUnion Core.emptyRegex (toCore r1 atStart atEnd)
  | .union r1 r2 =>
    mkReUnion (toCore r1 atStart atEnd) (toCore r2 atStart atEnd)
  | .star r1 =>
    toCoreStarBody r1 mkReStar mkReStar atStart atEnd (toCore r1)
  | .loop r1 n m =>
    toCoreLoop r1 n m atStart atEnd (toCore r1)
  | .concat r1 r2 =>
    toCoreConcat r1 r2 atStart atEnd (toCore r1) (toCore r2)

def pythonRegexToCore (pyRegex : String) (mode : MatchMode := .fullmatch) :
    Core.Expression.Expr × Option ParseError :=
  match parseTop pyRegex with
  | .error err => (mkApp Strata.SourceRange.none (.op Strata.SourceRange.none reAllFunc.name (some reTy)) [], some err)
  | .ok ast =>
    -- `dotStar`: passed with `atStart=false`, `atEnd=false` since `anychar`
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
        let coreTT := RegexAST.toCore ast true true
        let coreTF := RegexAST.toCore ast true false
        mkReUnion coreTT (mkReConcat coreTF dotStar)
    | .search =>
        -- Four combinations of (`^` active, `$` active).
        let coreTT := RegexAST.toCore ast true  true
        let coreTF := RegexAST.toCore ast true  false
        let coreFT := RegexAST.toCore ast false true
        let coreFF := RegexAST.toCore ast false false
        mkReUnion coreTT
          (mkReUnion (mkReConcat coreTF dotStar)
            (mkReUnion (mkReConcat dotStar coreFT)
                       (mkReConcat dotStar (mkReConcat coreFF dotStar))))
    (result, none)

end
-------------------------------------------------------------------------------
