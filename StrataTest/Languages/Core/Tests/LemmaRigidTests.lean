/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.GenOpaqueTypeParams
meta import StrataTest.Languages.Core.Tests.TestUtil
import StrataDDM.Integration.Lean.HashCommands

/-! # A lemma's type parameter is one type

A lemma holds at every type, so `genOpaqueTypeParams` replaces each of its type parameters by one
opaque type: every occurrence of a parameter has the same type. Here the two quantifiers over `a`
share it, so the lemma holds, and `Core.verify` proves it.
-/

meta section
open StrataDDM (Program)

namespace Core.LemmaRigidTests

private abbrev toCore := Core.TestUtil.translateWithMetaData

/-- `p` type-checked, then through `genOpaqueTypeParams`, printed. -/
private def opaqued (p : Core.Program) : IO Unit :=
  match Core.TestUtil.typeCheckThenGenOpaque p with
  | .ok q => IO.println (toString (Std.format q))
  | .error e => IO.println s!"error: {e}"

private def verdicts (p : StrataDDM.Program) : IO Unit := do
  for r in ← Strata.Core.verify p (options := .quiet) do
    IO.println s!"{r.obligation.label}: {r.formatOutcome}"

private def oneTypePgm :=
#strata
program Core;
lemma [L] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v);
#end

/--
info: program Core;

type $__opaque_L_a_0;
lemma [L]: (forall x : $__opaque_L_a_0 :: forall y : $__opaque_L_a_0 :: x == y) ==> (forall u : $__opaque_L_a_0 :: forall v : $__opaque_L_a_0 :: u == v);
-/
#guard_msgs in
#eval opaqued (toCore oneTypePgm)

/-- info: L: ✅ pass -/
#guard_msgs in
#eval verdicts oneTypePgm

/-! The opaque type's name avoids every name the program declares, before or after the lemma. -/

private def declaredBeforePgm :=
#strata
program Core;
type $__opaque_L_a_0;
lemma [L] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v);
#end

private def declaredAfterPgm :=
#strata
program Core;
lemma [L] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v);
type $__opaque_L_a_0;
#end

/--
info: program Core;

type $__opaque_L_a_0;
type $__opaque_L_a_1;
lemma [L]: (forall x : $__opaque_L_a_1 :: forall y : $__opaque_L_a_1 :: x == y) ==> (forall u : $__opaque_L_a_1 :: forall v : $__opaque_L_a_1 :: u == v);
-/
#guard_msgs in
#eval opaqued (toCore declaredBeforePgm)

/--
info: program Core;

type $__opaque_L_a_1;
lemma [L]: (forall x : $__opaque_L_a_1 :: forall y : $__opaque_L_a_1 :: x == y) ==> (forall u : $__opaque_L_a_1 :: forall v : $__opaque_L_a_1 :: u == v);
type $__opaque_L_a_0;
-/
#guard_msgs in
#eval opaqued (toCore declaredAfterPgm)

/-- info: L: ✅ pass -/
#guard_msgs in
#eval verdicts declaredBeforePgm

/-- info: L: ✅ pass -/
#guard_msgs in
#eval verdicts declaredAfterPgm

/-! Lemmas whose labels or type parameters contain `#`. The parser accepts no `#` in a label or
a type parameter, so these lemmas are built directly, as a front end would.

Both are accepted. `genOpaqueTypeParams` replaces each type parameter by its own opaque type,
built with each `#` replaced by `_` and picked fresh after that: two type parameters whose names
differ only by `#` and `_` get different types (`Lb`), and two lemmas whose labels differ so
(`L#a`, `L_a`) each get their own opaque type; the labels are kept. -/

private def hashBase :=
#strata
program Core;
lemma [La] <a>: (forall x : a, y : a :: x == y) ==> (forall u : a, v : a :: u == v);
lemma [Lb] <x, y>: (forall p : x, q : y :: p == p && q == q);
#end

private def withHashes : Core.Program :=
  let ds := (toCore hashBase).decls
  let edit : Core.Decl → Core.Decl
    | .lemma l md =>
      if l.name == "La" then .lemma { l with name := "L#a" } md
      else
        let S : Lambda.Subst :=
          Strata.Util.HMaps.ofScopes [[("x", .ftvar "x#y"), ("y", .ftvar "x_y")]]
        .lemma { l with typeArgs := ["x#y", "x_y"], e := l.e.applyTypeSubst S } md
    | d => d
  let la : List Core.Decl := match ds.head? with
    | some (.lemma l md) => [.lemma { l with name := "L_a" } md]
    | _ => []
  { decls := ds.map edit ++ la }

/--
info: program Core;

type $__opaque_L_a_a_0;
lemma [|L#a|]: (forall x : $__opaque_L_a_a_0 :: forall y : $__opaque_L_a_a_0 :: x == y) ==> (forall u : $__opaque_L_a_a_0 :: forall v : $__opaque_L_a_a_0 :: u == v);
type $__opaque_Lb_x_y_1;
type $__opaque_Lb_x_y_2;
lemma [Lb] (p : $__opaque_Lb_x_y_1, q : $__opaque_Lb_x_y_2): p == p && q == q;
type $__opaque_L_a_a_3;
lemma [L_a]: (forall x : $__opaque_L_a_a_3 :: forall y : $__opaque_L_a_a_3 :: x == y) ==> (forall u : $__opaque_L_a_a_3 :: forall v : $__opaque_L_a_a_3 :: u == v);
-/
#guard_msgs in
#eval opaqued withHashes

-- `Core.typeCheck` accepts the lemmas whose labels contain `#`, and keeps their type parameters
-- as written.
/--
info: program Core;

lemma [|L#a|] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
lemma [Lb] <|x#y|, x_y>(p : |x#y|, q : x_y): p == p && q == q;
lemma [L_a] <a>: (forall x : a :: forall y : a :: x == y) ==> (forall u : a :: forall v : a :: u == v);
-/
#guard_msgs in
#eval match Core.typeCheck .quiet withHashes with
  | .ok q => IO.println (toString (Std.format q))
  | .error e => IO.println s!"error: {e.message}"

-- The three lemmas verify under their own labels.
/--
info: L#a: ✅ pass
Lb: ✅ pass
L_a: ✅ pass
-/
#guard_msgs in
#eval do
  for r in ← EIO.toIO (fun s => IO.userError s) (Strata.Core.verifyProgram withHashes .quiet) do
    IO.println s!"{r.obligation.label}: {r.formatOutcome}"

/-! Two type parameters whose names coincide once `#` is replaced (`a#` and `a_`) must still get
different opaque types: the lemma below holds when they are one type (over one sort, either all
elements are equal or two differ), but not when the first type has two elements and the second
one. So it must not pass: the solver finds no proof (`unknown`, since the model it would report
has quantifiers). `Lone`, the same formula over one type parameter, passes, so the verdict
depends on the two types being kept apart. -/

private def collidePgm :=
#strata
program Core;
lemma [Lc] <a, b>: (forall x : a, y : a :: x == y) || (exists u : b, v : b :: !(u == v));
lemma [Lone] <a>: (forall x : a, y : a :: x == y) || (exists u : a, v : a :: !(u == v));
#end

private def collideHashes : Core.Program :=
  { decls := (toCore collidePgm).decls.map fun
      | .lemma l md =>
        if l.name == "Lc" then
          let S : Lambda.Subst :=
            Strata.Util.HMaps.ofScopes [[("a", .ftvar "a#"), ("b", .ftvar "a_")]]
          .lemma { l with typeArgs := ["a#", "a_"], e := l.e.applyTypeSubst S } md
        else .lemma l md
      | d => d }

/--
info: Lc: ❓ unknown
Lone: ✅ pass
-/
#guard_msgs in
#eval do
  for r in ← EIO.toIO (fun s => IO.userError s) (Strata.Core.verifyProgram collideHashes .quiet) do
    IO.println s!"{r.obligation.label}: {r.formatOutcome}"

end Core.LemmaRigidTests
end
