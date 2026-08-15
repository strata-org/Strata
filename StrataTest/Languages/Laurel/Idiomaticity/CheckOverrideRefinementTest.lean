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
    + modifies-subset). Emitted only when the parent declares a postcondition.

The pass runs on the still-composite program (before `LiftInstanceProcedures`
flattens methods), and needs a resolved program (`needsResolves := true`), so each
test resolves first and then drives `checkOverrideRefinementPass.run`.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.CheckOverrideRefinement
import Strata.Languages.Laurel.Resolution

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
  assert a >= 0 summary "override precondition no stronger than 'Parent.m' (Liskov)"
};
procedure Child$m$Parent$childspec(self: Child, a: int)
  returns (r: int)
  opaque
  ensures r == a;
procedure Child$m$Parent$refines$post(self: Child, a: int)
  returns (r: int)
  requires a >= 0
  opaque
  ensures r >= 0( summary "override postcondition no weaker than 'Parent.m' (Liskov)")
{
  r := Child$m$Parent$childspec(self, a)
};
-/
#guard_msgs in
#eval printChecked
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
  ensures r >= 0( summary "override postcondition no weaker than 'Parent.m' (Liskov)")
{
  r := Child$m$Parent$childspec(self)
};
-/
#guard_msgs in
#eval printChecked
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
#eval printChecked
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
  assert a >= 0 summary "override precondition no stronger than 'Parent.m' (Liskov)"
};
-/
#guard_msgs in
#eval printChecked
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

end Laurel
