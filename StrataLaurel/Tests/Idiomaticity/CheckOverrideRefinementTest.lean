/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Before/after tests for the `CheckOverrideRefinement` pass (see
CheckOverrideRefinement.lean). Each `#strata` block is the *source* — a composite
`Parent` with a method `m` and a `Child extends Parent` that overrides it (the
"before"); the `#guard_msgs` block is the program the pass produces (the "after"),
printed as Laurel source.

`CheckOverrideRefinement` is purely ADDITIVE: it never rewrites an existing
procedure, it only APPENDS synthetic *checker* procedures whose verification is
the behavioral-subtyping (Liskov) obligation for each override pair:

  * `<Child>$<m>$<Parent>$refines$pre`  — assumes Parent.pre, asserts Child.pre
    (precondition contravariance). Emitted only when the child declares a
    precondition.
  * `<Child>$<m>$<Parent>$childspec`    — a bodyless opaque companion carrying the
    CHILD's post + modifies, so the post-checker becomes a heap-writer and `old(...)`
    survives two-state lowering.
  * `<Child>$<m>$<Parent>$refines$post` — assumes Parent.pre, calls `$childspec`,
    re-establishes Parent.post over the child-havoc'd heap (postcondition covariance
    + modifies-subset). Emitted when the parent declares a postcondition OR frames a
    target: a framed void parent still imposes a frame the override must not widen.

The pass runs on the still-composite program (before `LiftInstanceProcedures`
flattens methods), and needs a resolved program (`needsResolves := true`), so each
test resolves first and then drives `checkOverrideRefinementPass.run`.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.CheckOverrideRefinement
import StrataLaurel.Implementation.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Resolve `program`, run `CheckOverrideRefinement`, and print the resulting
    program as Laurel source: the composite types (unchanged — the pass is
    additive) then the static procedures (the appended checkers), plus any
    diagnostics. -/
private def printChecked (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let (checked, diags, _) := checkOverrideRefinementPass.run {} result.program result.model
  IO.println "-- types --"
  for ty in checked.types do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format ty)))
  IO.println "-- procedures --"
  for proc in checked.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  for d in diags do
    IO.println s!"diagnostic: {d.message}"

private def methodOn (p : Program) (tyName : String) : Option Procedure :=
  p.types.findSome? fun
    | .Composite ct => if ct.name.text == tyName then ct.instanceProcedures.head? else none
    | _ => none

/-- Reproduces what a frontend with no source for a declaration hands the pass, which no Laurel
    source can express. -/
private def blankMethodNames (tyName : String) (p : Program) : Program :=
  { p with types := p.types.map fun
    | .Composite ct =>
      .Composite (if ct.name.text == tyName then
        { ct with instanceProcedures := ct.instanceProcedures.map fun m =>
            { m with name := { m.name with source := .unknown } } }
      else ct)
    | td => td }

/-- Names the position an obligation landed on rather than printing it, so the golden does not
    pin byte offsets that every edit to the fixture above would shift. -/
private def printAnchors (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let overrideName := (methodOn result.program "Child").map (·.name.source)
  let inheritedClause := (methodOn result.program "Parent").bind fun p =>
    (bodyPostconditions p.body).head?.map (·.condition.source)
  for (label, prog) in [("override has a position", result.program),
                        ("override has none    ", blankMethodNames "Child" result.program)] do
    let (checked, _, _) := checkOverrideRefinementPass.run {} prog result.model
    let anchor := (checked.staticProcedures.find? (·.name.text.endsWith "refines$post")).bind
      fun proc => (bodyPostconditions proc.body).head?.map (·.condition.source)
    let place :=
      if anchor == overrideName then "the override's method name"
      else if anchor == inheritedClause then "the inherited clause"
      else "NEITHER"
    let real := if (anchor.map (·.range.isNone)).getD true then " (NO POSITION)" else ""
    IO.println s!"{label}: {place}{real}"

/-! ## Override with pre + post: both refinement checkers emitted

`Child.m` overrides `Parent.m`, declaring both a `requires` and an `ensures`, so
the pass appends all three synthesized procedures: the pre-checker, the
`$childspec` companion, and the two-state post-checker. -/

/--
info: -- types --
composite Parent {procedure m(self: Parent, a: int)
  returns (r: int)
  requires a >= 0
  opaque
  ensures r >= 0
{
  r := a
}; }
composite Child extends Parent {procedure m(self: Child, a: int)
  returns (r: int)
  requires a >= 0
  opaque
  ensures r == a
{
  r := a
}; }
-- procedures --
procedure u()
  opaque
{
  assert 1 == 1
};
procedure Child$m$Parent$refines$pre(self: Child, a: int)
  requires a >= 0
  opaque
{
  assert a >= 0 summary "override precondition 'a >= 0' no stronger than 'Parent.m'"
};
procedure Child$m$Parent$childspec(self: Child, a: int)
  returns (r: int)
  opaque
  ensures r == a;
procedure Child$m$Parent$refines$post(self: Child, a: int)
  returns (r: int)
  requires a >= 0
  opaque
  ensures r >= 0( summary "override postcondition no weaker than 'r >= 0' from 'Parent.m'")
{
  r := Child$m$Parent$childspec(self, a)
};
-/
#guard_msgs in
#eval printChecked <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent, a: int) returns (r: int) requires a >= 0 opaque ensures r >= 0 { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque ensures r == a { r := a };
}
procedure u() opaque { assert 1 == 1 };
#end

/-! ## Override with post only: no pre-checker

`Child.m` declares no precondition, so contravariance holds trivially and the
pre-checker is omitted; only the `$childspec` companion and the post-checker are
appended. -/

/--
info: -- types --
composite Parent {procedure m(self: Parent)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0
}; }
composite Child extends Parent {procedure m(self: Child)
  returns (r: int)
  opaque
  ensures r == 5
{
  r := 5
}; }
-- procedures --
procedure u()
  opaque
{
  assert 1 == 1
};
procedure Child$m$Parent$childspec(self: Child)
  returns (r: int)
  opaque
  ensures r == 5;
procedure Child$m$Parent$refines$post(self: Child)
  returns (r: int)
  opaque
  ensures r >= 0( summary "override postcondition no weaker than 'r >= 0' from 'Parent.m'")
{
  r := Child$m$Parent$childspec(self)
};
-/
#guard_msgs in
#eval printChecked <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 5 { r := 5 };
}
procedure u() opaque { assert 1 == 1 };
#end

/-! ## No override: no checkers

`Child` does not declare `m`, so there is no override pair and the pass appends
nothing — the program is unchanged apart from resolution. -/

/--
info: -- types --
composite Parent {procedure m(self: Parent)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0
}; }
composite Child extends Parent { }
-- procedures --
procedure u()
  opaque
{
  assert 1 == 1
};
-/
#guard_msgs in
#eval printChecked <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite Child extends Parent { }
procedure u() opaque { assert 1 == 1 };
#end

/-! ## Override with pre only: no post-checker

`Parent.m` declares no (non-free) postcondition, so covariance holds trivially and
the post-checker + `$childspec` companion are omitted; `Child.m` declares a `requires`,
so only the pre-checker is appended. Exercises the `parentPosts.isEmpty` guard. -/

/--
info: -- types --
composite Parent {procedure m(self: Parent, a: int)
  returns (r: int)
  opaque
{
  r := a
}; }
composite Child extends Parent {procedure m(self: Child, a: int)
  returns (r: int)
  requires a >= 0
  opaque
{
  r := a
}; }
-- procedures --
procedure u()
  opaque
{
  assert 1 == 1
};
procedure Child$m$Parent$refines$pre(self: Child, a: int)
  requires true
  opaque
{
  assert a >= 0 summary "override precondition 'a >= 0' no stronger than 'Parent.m'"
};
-/
#guard_msgs in
#eval printChecked <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent, a: int) returns (r: int) opaque { r := a };
}
composite Child extends Parent {
  procedure m(self: Child, a: int) returns (r: int) requires a >= 0 opaque { r := a };
}
procedure u() opaque { assert 1 == 1 };
#end

/-! ## Multi-clause ancestor: each inherited clause carries its own summary

Every obligation is anchored at the override, so two inherited clauses land at the SAME
position and only their text tells the resulting diagnostics apart. This pins that each
clause gets a summary quoting itself, rather than two copies of one sentence. -/

/--
info: -- types --
composite Parent {procedure m(self: Parent)
  returns (r: int)
  opaque
  ensures r >= 0
  ensures r <= 100
{
  r := 50
}; }
composite Child extends Parent {procedure m(self: Child)
  returns (r: int)
  opaque
  ensures r == 50
{
  r := 50
}; }
-- procedures --
procedure u()
  opaque
{
  assert 1 == 1
};
procedure Child$m$Parent$childspec(self: Child)
  returns (r: int)
  opaque
  ensures r == 50;
procedure Child$m$Parent$refines$post(self: Child)
  returns (r: int)
  opaque
  ensures r >= 0( summary "override postcondition no weaker than 'r >= 0' from 'Parent.m'")
  ensures r <= 100( summary "override postcondition no weaker than 'r <= 100' from 'Parent.m'")
{
  r := Child$m$Parent$childspec(self)
};
-/
#guard_msgs in
#eval printChecked <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 ensures r <= 100 { r := 50 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 50 { r := 50 };
}
procedure u() opaque { assert 1 == 1 };
#end

/-! ## Anchor fallback: an override with no position of its own

Nothing else pins the anchor guard: Laurel source always has positions, and the bytecode
frontend's XFAIL only asserts that the two frontends disagree, which stays true even if the
diagnostic degrades to no position at all. Hence the detour through the AST. -/

/--
info: override has a position: the override's method name
override has none    : the inherited clause
-/
#guard_msgs in
#eval printAnchors <|
#strata
program Laurel;
composite Parent {
  procedure m(self: Parent) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite Child extends Parent {
  procedure m(self: Child) returns (r: int) opaque ensures r == 5 { r := 5 };
}
procedure u() opaque { assert 1 == 1 };
#end

end Laurel
