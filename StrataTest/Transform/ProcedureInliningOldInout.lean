/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.ProcedureInlining

meta section

open Core
open Core.Transform
open ProcedureInlining
open Strata
open Std

/-! # Regression: `old` on inout parameters survives procedure inlining

Each test inlines a callee that uses `old` on inout parameters and confirms
the result type-checks (pinned via `#guard_msgs`).
-/

namespace Strata.ProcedureInliningOldInout

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def runInlineCall (p : Core.Program) : Core.Program :=
  match (runProgram (targetProcList := .none) inlineCallCmd p .emp) with
  | ⟨.ok (_, res), _⟩ => res
  | ⟨.error e, _⟩ => panic! (toString e) -- nopanic:ok

/-- Type-check the result of inlining `p`. On success `Core.typeCheck` prints
    `ok: <program>`, so the pinned message both confirms type-checking and pins
    the exact inlined output. -/
private def inlinedTypeCheck (p : StrataDDM.Program) :=
  Core.typeCheck .quiet (runInlineCall (translate p))

-- A callee with an inout parameter `T` whose body asserts `old T`, inlined into
-- a caller.
private def oldInoutBodyPgm :=
#strata
program Core;

procedure Callee(inout T : bool)
{
  assert [inner]: old T;
};

procedure Caller()
{
  var T : bool := true;
  call Callee(inout T);
};
#end

/--
info: ok: program Core;

procedure Callee (inout T : bool)
{
  assert [inner]: old T;
};
procedure Caller ()
{
  var T : bool := true;
  $__inline1_Callee$inlined: {
    var $__inline1_T : bool := T;
    var $__inline1$old_T : bool := $__inline1_T;
    assert [$__inline1_inner]: $__inline1$old_T;
    T := $__inline1_T;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck oldInoutBodyPgm

-- Two inout parameters, each referenced via `old` in the body, so both the
-- rename and the per-parameter snapshot are exercised more than once.
private def oldInoutMultiPgm :=
#strata
program Core;

procedure Callee2(inout X : int, inout Y : int)
{
  assert [inner]: old X == old Y;
};

procedure Caller2()
{
  var X : int := 1;
  var Y : int := 2;
  call Callee2(inout X, inout Y);
};
#end

/--
info: ok: program Core;

procedure Callee2 (inout X : int, inout Y : int)
{
  assert [inner]: old X == old Y;
};
procedure Caller2 ()
{
  var X : int := 1;
  var Y : int := 2;
  $__inline1_Callee2$inlined: {
    var $__inline1_X : int := X;
    var $__inline1_Y : int := Y;
    var $__inline1$old_X : int := $__inline1_X;
    var $__inline1$old_Y : int := $__inline1_Y;
    assert [$__inline1_inner]: $__inline1$old_X == $__inline1$old_Y;
    X := $__inline1_X;
    Y := $__inline1_Y;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck oldInoutMultiPgm

-- Two call sites to the same callee in one caller. Each inlining bumps the run
-- counter, so the two blocks get distinct `$__inline<N>` prefixes (1 and 2) and
-- their fresh names cannot collide.
private def oldInoutTwoCallsPgm :=
#strata
program Core;

procedure Callee3(inout T : bool)
{
  assert [inner]: old T;
};

procedure Caller3()
{
  var T : bool := true;
  call Callee3(inout T);
  call Callee3(inout T);
};
#end

/--
info: ok: program Core;

procedure Callee3 (inout T : bool)
{
  assert [inner]: old T;
};
procedure Caller3 ()
{
  var T : bool := true;
  $__inline1_Callee3$inlined: {
    var $__inline1_T : bool := T;
    var $__inline1$old_T : bool := $__inline1_T;
    assert [$__inline1_inner]: $__inline1$old_T;
    T := $__inline1_T;
  }
  $__inline2_Callee3$inlined: {
    var $__inline2_T : bool := T;
    var $__inline2$old_T : bool := $__inline2_T;
    assert [$__inline2_inner]: $__inline2$old_T;
    T := $__inline2_T;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck oldInoutTwoCallsPgm

-- Callee with both an inout parameter and an output-only parameter: the
-- output-only param gets a nondet init while the inout param gets a pre-state
-- snapshot, so the `sigOutputOnly` filter and the snapshot inits are exercised
-- together.
private def mixedInoutOutPgm :=
#strata
program Core;

procedure MixedCallee(inout X : int, out Y : int)
{
  Y := X;
  assert [inner]: old X == X;
};

procedure MixedCaller(out R : int)
{
  var X : int := 0;
  call MixedCallee(inout X, out R);
};
#end

/--
info: ok: program Core;

procedure MixedCallee (inout X : int, out Y : int)
{
  Y := X;
  assert [inner]: old X == X;
};
procedure MixedCaller (out R : int)
{
  var X : int := 0;
  $__inline1_MixedCallee$inlined: {
    var $__inline1_X : int := X;
    var $__inline1$old_X : int := $__inline1_X;
    var $__inline1_Y : int;
    $__inline1_Y := $__inline1_X;
    assert [$__inline1_inner]: $__inline1$old_X == $__inline1_X;
    X := $__inline1_X;
    R := $__inline1_Y;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck mixedInoutOutPgm

-- Polymorphic callee: the inout parameter has the procedure's type variable as
-- its type. The rename and snapshot must be independent of the parameter type.
private def oldInoutPolyPgm :=
#strata
program Core;

procedure PolyCallee<a>(inout T : a)
{
  assert [inner]: old T == T;
};

procedure PolyCaller()
{
  var T : int := 0;
  call PolyCallee(inout T);
};
#end

/--
info: ok: program Core;

procedure PolyCallee (inout T : $__ty0)
{
  assert [inner]: old T == T;
};
procedure PolyCaller ()
{
  var T : int := 0;
  $__inline1_PolyCallee$inlined: {
    var $__inline1_T : int := T;
    var $__inline1$old_T : int := $__inline1_T;
    assert [$__inline1_inner]: $__inline1$old_T == $__inline1_T;
    T := $__inline1_T;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck oldInoutPolyPgm

-- An inout parameter whose body never references `old`. The pre-state snapshot
-- is still emitted (unused) and must not upset the type-checker.
private def inoutNoOldPgm :=
#strata
program Core;

procedure CalleeNoOld(inout T : bool)
{
  T := true;
};

procedure CallerNoOld()
{
  var T : bool := false;
  call CalleeNoOld(inout T);
};
#end

/--
info: ok: program Core;

procedure CalleeNoOld (inout T : bool)
{
  T := true;
};
procedure CallerNoOld ()
{
  var T : bool := false;
  $__inline1_CalleeNoOld$inlined: {
    var $__inline1_T : bool := T;
    var $__inline1$old_T : bool := $__inline1_T;
    $__inline1_T := true;
    T := $__inline1_T;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck inoutNoOldPgm

-- Direct unit test of the pure helper `snapshotOldInout`: one inout parameter
-- `T` (freshened to `RT`). Pins the emitted snapshot `init` and the returned
-- `old x → snapshot` rewrite entry.
/-- info: "init P$old_T := RT | old T -> P$old_T" -/
#guard_msgs in
#eval
  let (inits, subst) :=
    snapshotOldInout "P" [(⟨"T", ()⟩, ⟨"RT", ()⟩, (.forAll [] .bool : Expression.Ty))] #[]
  let initStr := match inits with
    | [Statement.init s _ (.det (.fvar _ r _)) _] => s!"init {s.name} := {r.name}"
    | _ => "<unexpected inits>"
  let substStr := String.intercalate ", "
    (subst.map (fun (ab : Expression.Ident × Expression.Ident) => s!"{ab.1.name} -> {ab.2.name}"))
  s!"{initStr} | {substStr}"

-- Nested control flow in the callee: the `old` reference and its labelled assert
-- live inside an `if`, so the recursive rename/label/snapshot substitution must
-- propagate through nested statements rather than a flat body.
private def nestedInoutPgm :=
#strata
program Core;

procedure NestedCallee(inout T : int)
{
  if (int.gt(T, 0)) {
    assert [inner]: old T == T;
  } else {
    T := int.sub(T, 1);
  }
};

procedure NestedCaller()
{
  var T : int := 5;
  call NestedCallee(inout T);
};
#end

/--
info: ok: program Core;

procedure NestedCallee (inout T : int)
{
  if (int.gt(T, 0)) {
    assert [inner]: old T == T;
  } else {
    T := int.sub(T, 1);
  }
};
procedure NestedCaller ()
{
  var T : int := 5;
  $__inline1_NestedCallee$inlined: {
    var $__inline1_T : int := T;
    var $__inline1$old_T : int := $__inline1_T;
    if (int.gt($__inline1_T, 0)) {
      assert [$__inline1_inner]: $__inline1$old_T == $__inline1_T;
    } else {
      $__inline1_T := int.sub($__inline1_T, 1);
    }
    T := $__inline1_T;
  }
};
-/
#guard_msgs in
#eval inlinedTypeCheck nestedInoutPgm

end Strata.ProcedureInliningOldInout

end
