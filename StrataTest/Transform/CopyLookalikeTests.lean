/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.FoldConnectives
meta import all Strata.Transform.UnrollBoundedQuantifiers

meta section

open Strata

/-! # A user's name that looks like a copy is never read as one

When a name of the program starts with `$__mono`, monomorphization pads its copies' prefix
(`choosePrefix`), so a user's function may be named `$__mono#Int.Add#int`, which looks like a
copy of `Int.Add` under the plain prefix. Every site that reads a copy's base, to pick what an
operator means, reads it under the chosen prefix only. These tests give each such site a name
of that shape and check it is read as written: end to end through `Core.verify` for the SMT
encoder, where a misread changes the verdict, and at the site for the phases and the verifier's
helpers. Each end-to-end `ensures` holds only under the user's definition, and the last one is
false under it but true under the built-in. -/

namespace Core.CopyLookalikeTests

/-- A user function named like a copy of integer addition, with another body. -/
private def addPgm :=
#strata
program Core;
function |$__mono#Int.Add#int|(a : int, b : int) : int { 0 }
procedure P(out r : int)
spec { ensures [userAdd]: r == 0; }
{ r := |$__mono#Int.Add#int|(2, 3); };
#end

/-- A user function named like a copy of conjunction. -/
private def andPgm :=
#strata
program Core;
function |$__mono#Bool.And#bool|(a : bool, b : bool) : bool { true }
procedure P(out r : bool)
spec { ensures [userAnd]: r; }
{ r := |$__mono#Bool.And#bool|(false, false); };
#end

/-- A user function named like a copy of a datatype's constructor. -/
private def consPgm :=
#strata
program Core;
datatype L { Nil(), Cons(h : int, t : L) };
function |$__mono#Cons#int|(a : int, b : L) : L { Nil() }
procedure P(out r : L)
spec { ensures [userCons]: L..isNil(r); }
{ r := |$__mono#Cons#int|(1, Nil()); };
#end

/-- Under the user's definition `r` is 6, so this `ensures` must fail; read as addition it
    would pass. -/
private def falseIfMisreadPgm :=
#strata
program Core;
function |$__mono#Int.Add#int|(a : int, b : int) : int { int.add(int.add(a, b), 1) }
procedure P(out r : int)
spec { ensures [falseUnderUser]: r == 5; }
{ r := |$__mono#Int.Add#int|(2, 3); };
#end

/-- A quantifier whose binder is named like the copy of `id` at `int`, and whose body calls
    that copy. The binder pads the copies' prefix, so the copy's function symbol differs from
    the binder and the body reads `id`: the first assertion holds and the second fails. -/
private def binderCallsCopyPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P()
{
  assert [binderTrue]: forall |$__mono#id#int| : int :: id(|$__mono#id#int|) == |$__mono#id#int|;
  assert [binderFalse]: forall |$__mono#id#int| : int ::
    id(|$__mono#id#int|) == int.add(|$__mono#id#int|, 1);
};
#end

/-- A name starting with `$__mono` pads the copies' prefix. Pruning must still keep `f`'s
    axiom for the obligation that calls `f`'s copy. -/
private def padPrunePgm :=
#strata
program Core;
function |$__mono_pad|(x : int) : int { x }
function f<a>(x : a) : a;
axiom [fax]: forall x : int :: f(x) == x;
procedure P(out r : int)
spec { ensures [rIs5]: r == 5; }
{ r := f(5); };
#end

/-- An uninterpreted user function named like a copy, with its own axiom. Pruning must keep
    that axiom: the name seeds itself as well as the base it looks like. -/
private def lookalikeAxiomPgm :=
#strata
program Core;
function |$__mono__#g#int|(x : int) : int;
axiom [gax]: forall x : int :: |$__mono__#g#int|(x) == x;
procedure P(out r : int)
spec { ensures [rIs5]: r == 5; }
{ r := |$__mono__#g#int|(5); };
#end

/-- Under a padded prefix, with a user type named `update`: the map operators' copies at
    `int` must be told apart from those at `Pair update int`. -/
private def padMapPgm :=
#strata
program Core;
type |update|;
type Pair (a : Type, b : Type);
function |$__mono_pad|(x : int) : int { x }
procedure P(k : Pair |update| int, m1 : Map (Pair |update| int) int,
    out r1 : Map (Pair |update| int) int, out r2 : Map int int)
spec {
  ensures [e1]: r1[k] == 1;
  ensures [e2]: r2[1] == 2;
  ensures [e3]: r2[3] == 0;
}
{ r1 := m1[k := 1]; r2 := mapConst<int>(0)[1 := 2]; };
#end

/-- A check labelled exactly like the copy of `id` at `int` would be named under the prefix the
    procedure's name alone pads to. The copies' prefix avoids the labels too, so the copy takes
    another name and the program verifies. -/
private def labelClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure |$__monoP|() {
  assert [|$__mono________________________#id#int|]: id(1) == 1;
};
#end

/-- The verdicts of `p`'s obligations, by label, with the incremental back end or the default. -/
private def verdicts (p : StrataDDM.Program) (incremental : Bool := false)
    (prune : _root_.Core.IrrelevantAxiomsMode := .Off) :
    IO (List (String × Bool)) := do
  let opts : _root_.Core.VerifyOptions :=
    { _root_.Core.VerifyOptions.default with
      incremental := incremental
      removeIrrelevantAxioms := prune }
  let rs ← Strata.Core.verify p (options := opts)
  return rs.toList.map fun r => (r.obligation.label, r.isSuccess)

#guard_msgs (drop info) in
#eval do
  let v ← verdicts addPgm
  unless v == [("userAdd", true)] do throw (IO.userError s!"addPgm: {v}")
  let v ← verdicts andPgm
  unless v == [("userAnd", true)] do throw (IO.userError s!"andPgm: {v}")
  let v ← verdicts consPgm
  unless v == [("userCons", true)] do throw (IO.userError s!"consPgm: {v}")
  let v ← verdicts falseIfMisreadPgm
  unless v == [("falseUnderUser", false)] do throw (IO.userError s!"falseIfMisreadPgm: {v}")
  -- The incremental back end reads the copy mark (`monoCopyOf`) as the default one does.
  let v ← verdicts falseIfMisreadPgm (incremental := true)
  unless v == [("falseUnderUser", false)] do
    throw (IO.userError s!"falseIfMisreadPgm, incremental: {v}")
  let v ← verdicts addPgm (incremental := true)
  unless v == [("userAdd", true)] do throw (IO.userError s!"addPgm, incremental: {v}")
  -- Axiom pruning reads seeds by name; a lookalike only keeps more axioms.
  let v ← verdicts falseIfMisreadPgm (prune := .Precise)
  unless v == [("falseUnderUser", false)] do
    throw (IO.userError s!"falseIfMisreadPgm, pruning: {v}")
  let v ← verdicts addPgm (prune := .Precise)
  unless v == [("userAdd", true)] do throw (IO.userError s!"addPgm, pruning: {v}")
  let v ← verdicts padPrunePgm (prune := .Precise)
  unless v == [("rIs5", true)] do throw (IO.userError s!"padPrunePgm, Precise: {v}")
  let v ← verdicts padPrunePgm (prune := .Aggressive)
  unless v == [("rIs5", true)] do throw (IO.userError s!"padPrunePgm, Aggressive: {v}")
  let v ← verdicts lookalikeAxiomPgm (prune := .Precise)
  unless v == [("rIs5", true)] do throw (IO.userError s!"lookalikeAxiomPgm, Precise: {v}")
  let v ← verdicts lookalikeAxiomPgm (prune := .Aggressive)
  unless v == [("rIs5", true)] do throw (IO.userError s!"lookalikeAxiomPgm, Aggressive: {v}")
  let v ← verdicts padMapPgm
  unless v == [("e1", true), ("e2", true), ("e3", true)] do
    throw (IO.userError s!"padMapPgm: {v}")
  let v ← verdicts labelClashPgm
  unless v == [("$__mono________________________#id#int", true)] do
    throw (IO.userError s!"labelClashPgm: {v}")
  let v ← verdicts binderCallsCopyPgm
  unless v == [("binderTrue", true), ("binderFalse", false)] do
    throw (IO.userError s!"binderCallsCopyPgm: {v}")

/-! ## At each site

A site that decides what an operator means reads the copy mark (`FuncAttr.monoCopyOf`), which
only monomorphization sets, so a function named like a copy is read as written; the axiom
seeds read the name, under any prefix monomorphization can choose (`Core.seedNames`). -/

-- Connectives are monomorphic, never copied, so they are read as written.
#guard FoldConnectives.boolOpOf? "Bool.And" == some .And
#guard FoldConnectives.boolOpOf? "$__mono#Bool.And#bool" == none

/-- A factory function named like a copy of `Sequence.select!`, unmarked or marked. -/
private def selectLike (marked : Bool) : Lambda.LFunc _root_.Core.CoreLParams :=
  { name := ⟨"$__mono#Sequence.select!#int", ()⟩, inputs := [(⟨"s", ()⟩, .int), (⟨"i", ()⟩, .int)],
    output := .int,
    attr := if marked then #[.monoCopyOf "Sequence.select!"] else #[] }

-- The bounded-quantifier unrolling recognizes a selector's copy by its mark.
#guard _root_.Core.UnrollBoundedQuantifiers.baseName
    (_root_.Core.Factory.pushIfNew (selectLike false)) "$__mono#Sequence.select!#int" ==
  "$__mono#Sequence.select!#int"
#guard _root_.Core.UnrollBoundedQuantifiers.baseName
    (_root_.Core.Factory.pushIfNew (selectLike true)) "$__mono#Sequence.select!#int" ==
  "Sequence.select!"

-- The axiom seeds decode by name under any prefix monomorphization can choose: a name of a
-- copy's shape seeds itself and its base (extra true axioms), and any other name only itself.
#guard _root_.Core.seedNames ⟨"$__mono#f#int", ()⟩ == ["$__mono#f#int", "f"]
#guard _root_.Core.seedNames ⟨"$__mono____#f#int", ()⟩ == ["$__mono____#f#int", "f"]
#guard _root_.Core.seedNames ⟨"$__mono_x#f#int", ()⟩ == ["$__mono_x#f#int"]
#guard _root_.Core.seedNames ⟨"$__mono_pad", ()⟩ == ["$__mono_pad"]

-- The encoder's trigger spine matches the trigger operators by their exact names.
#guard _root_.Core.isCoreTriggerListExpr
    (.op default ⟨"$__mono#Triggers.empty#int", ()⟩ none) == false
#guard _root_.Core.isCoreTriggerListExpr (.op default ⟨"Triggers.empty", ()⟩ none)

-- A collection literal whose operator has neither its built-in nor a marked copy in the factory
-- is an encoding error, never a function picked by its name.
#guard match _root_.Core.collectionOpIdent
    (Lambda.Factory.default : @Lambda.Factory _root_.Core.CoreLParams) "mapConst" [.int, .int] with
  | .error _ => true
  | .ok _ => false

/-! ## A pipeline without monomorphization

A front end may skip monomorphization when its program has no polymorphic function: here the
monomorphization slot holds the check of `noPolymorphicFunctions` instead, which this program
passes. There are then no copies, so no factory function carries the copy mark (`monoCopyOf`),
the user's function is encoded from its own declaration, and the false `ensures` fails. -/

#guard_msgs (drop info) in
#eval show IO Unit from do
  let phases := (Strata.Core.corePipelinePhases).map fun p =>
    if p.phase.name == "monomorphizeFunctions" then
      Strata.Core.assertPhase .noPolymorphicFunctions
    else p
  match Strata.Core.validatePipeline phases with
  | .error e => throw (IO.userError s!"pipeline rejected: {e}")
  | .ok vp =>
    let prog := (TransM.run Inhabited.default (translateProgram falseIfMisreadPgm)).fst
    match ← (Strata.Core.verifyProgram prog (pipeline := some vp)).toBaseIO with
    | .error e => throw (IO.userError s!"verify error: {e}")
    | .ok rs =>
      let v := rs.toList.map fun (r : _root_.Core.VCResult) => (r.obligation.label, r.isSuccess)
      unless v == [("falseUnderUser", false)] do
        throw (IO.userError s!"no-monomorphize pipeline: {v}")

/-! ## Printing a program

A program function is printed as written, whatever its name looks like: the user's
`$__mono#update#int`, which returns its map unchanged, is not printed as a map update. -/

private def lookalikeUpdatePgm :=
#strata
program Core;
function |$__mono#update#int|(m : Map int int, i : int, v : int) : Map int int { m }
procedure P(m : Map int int, out r : Map int int)
spec { ensures [unchanged]: r[1] == m[1]; }
{ r := m; r := |$__mono#update#int|(r, 1, 2); };
#end

#guard
  let s := toString (Std.format
    (TransM.run Inhabited.default (translateProgram lookalikeUpdatePgm)).fst)
  (s.splitOn "r[1] := 2").length == 1 && (s.splitOn "|$__mono#update#int|(r, 1, 2)").length == 2

#guard_msgs (drop info) in
#eval do
  let v ← verdicts lookalikeUpdatePgm
  unless v == [("unchanged", true)] do throw (IO.userError s!"lookalikeUpdatePgm: {v}")

end Core.CopyLookalikeTests

end
