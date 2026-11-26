/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.GenOpaqueTypeParams
meta import StrataTest.Languages.Core.Tests.TestUtil

/-! # The opaque type names minted from labels

`genOpaqueTypeParams` builds an opaque type's name from a label with each `#` replaced by `_`
(`Core.FreshPlainName.sanitize`), fresh against every name the program declares with the
generated prefix and against the names minted before it. The label itself is kept. -/

meta section

open Strata
open Core.TestUtil (translate)

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

private abbrev opaqued := Core.TestUtil.typeCheckThenGenOpaque

/-- The type names `genOpaqueTypeParams` mints for `p`: those it declares that `p` does not. -/
private def minted (p : Core.Program) : List String :=
  match opaqued p with
  | .ok q => (Core.Program.typeNames q).filter (· ∉ Core.Program.typeNames p)
  | .error e => [e]

/-! ### The sanitizer -/

#guard Core.FreshPlainName.sanitize "$__free_a#b#c_0" = "$__free_a_b_c_0"
#guard Core.FreshPlainName.sanitize "plain" = "plain"
#guard ["#", "a#", "##", "x#y#"].all fun b => '#' ∉ (Core.FreshPlainName.sanitize b).toList

/-! ### (a) `a#b` and `a_b` in one program get distinct minted names -/

private def clashPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) };
lemma [|a#b|] <t>: forall x : List t :: x == x;
lemma [a_b] <t>: forall x : List t :: x == x;
#end

/-- info: ["$__opaque_a_b_t_0", "$__opaque_a_b_t_1"] -/
#guard_msgs in
#eval minted (translate clashPgm)

-- Both lemmas keep their labels.
#guard ((opaqued (translate clashPgm)).toOption.map fun q =>
  q.decls.filterMap fun | .lemma l _ => some l.name | _ => none) = some ["a#b", "a_b"]

/-! ### (b) a name the program already declares is not minted again

The program declares a type named as `L`'s opaque type would be, and a function named as the
opaque type of `M#x` would be once its `#` is replaced: declarations share one namespace, so
neither name is minted. -/

private def takenPgm :=
#strata
program Core;
type $__opaque_L_t_0;
function $__opaque_M_x_t_0 () : int { 1 }
datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) };
lemma [L] <t>: forall x : List t :: x == x;
lemma [|M#x|] <t>: forall x : List t :: x == x;
#end

/-- info: ["$__opaque_L_t_1", "$__opaque_M_x_t_2"] -/
#guard_msgs in
#eval minted (translate takenPgm)

#guard (minted (translate takenPgm)).all (· ∉ Core.Program.declaredNames (translate takenPgm))

/-! ### (c) every minted name is free of `#` -/

#guard (minted (translate clashPgm) ++ minted (translate takenPgm)).all fun n =>
  '#' ∉ n.toList

/-! ### A procedure's opaque type avoids a declared type of the same name -/

private def procTakenPgm :=
#strata
program Core;
type $__opaque_P_a_0;
procedure P<a>(x : a, out r : a)
spec { ensures r == x; }
{ r := x; };
#end

/-- info: ["$__opaque_P_a_1"] -/
#guard_msgs in
#eval minted (translate procTakenPgm)

/-! ### Procedures whose names coincide only once `#` is replaced

`P#1` and `P_1` both give the base `$__opaque_P_1_a`: the shared counter still gives them
distinct opaque types, and both procedures verify under their own names. -/

private def procClashPgm :=
#strata
program Core;
procedure |P#1|<a>(x : a, out r : a)
spec { ensures r == x; }
{ r := x; };
procedure P_1<a>(x : a, out r : a)
spec { ensures r == x; }
{ r := x; };
#end

/-- info: ["$__opaque_P_1_a_0", "$__opaque_P_1_a_1"] -/
#guard_msgs in
#eval minted (translate procClashPgm)

/-- info: #[("P#1_ensures_0", true), ("P_1_ensures_0", true)] -/
#guard_msgs in
#eval do
  let r ← EIO.toIO (fun s => IO.userError s)
    (Strata.Core.verifyProgram (translate procClashPgm) quietOpts)
  return r.map fun (v : Core.VCResult) => (v.obligation.label, v.isSuccess)

end
