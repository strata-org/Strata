/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.MonomorphizeFunctions
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

open Strata
open Core.TestUtil (translateWithMetaData)

/-! ## `MonomorphizeFunctions` keeps copies apart from names that look like them

`MonomorphizeFunctions` names the copy of `id` at `int` `$__mono#id#int`. A program that
already declared a function with that name would get two declarations with one name, and
the renamed call `id(5)` would resolve to the first: the user's constant `6`, not `id`. The
postcondition `r == 6`, false of the input (`id(5) = 5`), would then hold of the output.
So the pass chooses the copies' prefix against the program's names (`choosePrefix`): when a
name starts with `$__mono`, the prefix is padded with `_`, and the copy of `id` is named
apart from the user's function. Names with `#` are kept as written, and a `#` inside a
copy's name is escaped (`escName`).
-/

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

private def fmtMonoFns (t : StrataDDM.Program) : IO Std.Format := do
  let prog := translateWithMetaData t
  match Core.typeCheck quietOpts prog with
  | .error msg => throw (IO.userError s!"{msg}")
  | .ok tc =>
    let seedState : Core.Transform.CoreTransformState :=
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
    match (Core.Transform.runWith tc Core.MonomorphizeFunctions.run seedState).1 with
    | .ok p => return Std.format p.stripMetaData
    | .error msg => return f!"error: {msg}"

private def clashPgm :=
#strata
program Core;
function |$__mono#id#int|(x : int) : int { 6 }
function id<a>(x : a) : a { x }
procedure P(out r : int)
spec {
  ensures r == 6;
}
{
  r := id(5);
};
#end

/--
info: program Core;

function |$__mono#id#int| (x : int) : int {
  6
}
function |$__mono________________________#id#int| (x : int) : int {
  x
}
procedure P (out r : int)
spec {
  ensures [P_ensures_0]: r == 6;
  } {
  r := |$__mono________________________#id#int|(5);
};
-/
#guard_msgs in
#eval fmtMonoFns clashPgm

/-! Every kind of name with `#` is kept as written: none is rejected. -/

private def hashDatatypePgm :=
#strata
program Core;
datatype |D#1| { Mk(v : int) };
#end

/--
info: program Core;

datatype |D#1| {
  Mk(v : int)
};
-/
#guard_msgs in
#eval fmtMonoFns hashDatatypePgm

private def hashConstructorPgm :=
#strata
program Core;
datatype D { |Mk#1|(v : int) };
#end

/--
info: program Core;

datatype D {
  |Mk#1|(v : int)
};
-/
#guard_msgs in
#eval fmtMonoFns hashConstructorPgm

private def hashFieldPgm :=
#strata
program Core;
datatype D { Mk(|v#1| : int) };
#end

/--
info: program Core;

datatype D {
  Mk(|v#1| : int)
};
-/
#guard_msgs in
#eval fmtMonoFns hashFieldPgm

/-- An operator name is checked even when nothing declares it: the axiom below refers to
    `g#1`, which no declaration introduces (the program is built directly, since it would
    not type-check). -/
private def hashOpProgram : Core.Program :=
  { decls := [.ax { name := "a", e := .op default ⟨"g#1", ()⟩ none } .empty] }

/--
info: "OK"
-/
#guard_msgs in
#eval match Core.Transform.run hashOpProgram (fun p => Core.MonomorphizeFunctions.run p) with
  | .ok _ => "OK"
  | .error m => toString m

/-- An opaque type whose name contains `#` is accepted, and so is a type constructor with
    `#` in an operator's annotation: the pass names copies after the type constructors of
    their instantiation, escaped. -/
private def hashTypePgm :=
#strata
program Core;
type |Foo#bar|;
function c() : |Foo#bar|;
axiom [a]: c() == c();
#end

/--
info: program Core;

type |Foo#bar|;
function c () : |Foo#bar|;
axiom [a]: c == c;
-/
#guard_msgs in
#eval fmtMonoFns hashTypePgm

/-- Two distinct instantiations would share a copy's name: `f` at the opaque type `T#1#int`
    and `f` at `T int` both mangle to `$__mono#f#T#1#int`, so one copy would serve both. -/
private def typeClashPgm :=
#strata
program Core;
type T (a : Type);
type |T#1#int|;
function f<a>(x : a) : int;
function u() : |T#1#int|;
function v() : T int;
axiom [ax]: f(u()) == f(v());
#end

/--
info: program Core;

type T (a : Type);
type |T#1#int|;
function |$__mono#f#T?h1?hint| (x : |T#1#int|) : int;
function |$__mono#f#T#1#int| (x : T int) : int;
function u () : |T#1#int|;
function v () : T int;
axiom [ax]: |$__mono#f#T?h1?hint|(u) == |$__mono#f#T#1#int|(v);
-/
#guard_msgs in
#eval fmtMonoFns typeClashPgm

/-- A type synonym whose name contains `#` is accepted too. -/
private def hashSynonymPgm :=
#strata
program Core;
type |S#1| := int;
#end

/--
info: program Core;

type |S#1| := int;
-/
#guard_msgs in
#eval fmtMonoFns hashSynonymPgm

/-- A Factory function named like a copy is accepted too, though the program never declares
    or calls it: a front end can supply Factory functions, and the copies' prefix is chosen
    against their names, so the copy of `id` at `int` does not share its name. -/
private def factoryClashPgm :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(out r : int)
spec {
  ensures r == 5;
}
{
  r := id(5);
};
#end

/-- Run the pass on `t` with a Factory that also has a function named `name`. -/
private def monoWithFactoryFn (t : StrataDDM.Program) (name : String) : String :=
  match Core.typeCheck quietOpts (translateWithMetaData t), Core.Factory.toArray[0]? with
  | .error msg, _ => s!"{msg}"
  | _, none => "empty Factory"
  | .ok tc, some f =>
    let factory := Lambda.Factory.ofArray
      (Core.Factory.toArray.push { f with name := ⟨name, ()⟩ })
    let seedState : Core.Transform.CoreTransformState :=
      { Core.Transform.CoreTransformState.emp with factory }
    match (Core.Transform.runWith tc Core.MonomorphizeFunctions.run seedState).1 with
    | .ok _ => "OK"
    | .error m => toString m

/--
info: "OK"
-/
#guard_msgs in
#eval monoWithFactoryFn factoryClashPgm "$__mono#id#int"

-- The same Factory function under a name without `#` is accepted.
#guard monoWithFactoryFn factoryClashPgm "extraFn" == "OK"

-- `tconsNames` collects type constructors nested inside other types' arguments.
#guard Core.NameMangling.tconsNames
    (.tcons "Map" [.int, .tcons "Set" [.tcons "Foo#bar" []]]) == ["Map", "int", "Set", "Foo#bar"]

/-- A `#` type constructor nested in an operator's annotation is accepted even when nothing
    declares it (the program is built directly, since it would not type-check). -/
private def nestedHashTyProgram : Core.Program :=
  let ty : Lambda.LMonoTy := .tcons "Map" [.int, .tcons "Set" [.tcons "Foo#bar" []]]
  { decls := [.ax { name := "a", e := .op default ⟨"g", ()⟩ (some ty) } .empty] }

/--
info: "OK"
-/
#guard_msgs in
#eval match Core.Transform.run nestedHashTyProgram (fun p => Core.MonomorphizeFunctions.run p) with
  | .ok _ => "OK"
  | .error m => toString m

/-- A polymorphic procedure whose name contains `#` is accepted by the full pipeline:
    `genOpaqueTypeParams` builds its opaque type's name with the `#` replaced by `_`, and the
    procedure keeps its name. -/
private def hashProcPgm :=
#strata
program Core;
procedure |P#1|<a>(x : a, out r : a)
spec {
  ensures r == x;
}
{
  r := x;
};
#end

/--
info:
Obligation: P#1_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval EIO.toIO (fun s => IO.userError s)
  (Core.verifyProgram (translateWithMetaData hashProcPgm) quietOpts)

/-- `datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) }` and the
    lemma `L#1 : List..isNil(Nil())`. The formula leaves the element type of
    `Nil()` undetermined, so type checking rejects the lemma under the name the
    user wrote. -/
private def hashLemmaPgm : Core.Program :=
  { decls := [Core.TestUtil.listDecl,
      .lemma { name := "L#1", typeArgs := [],
               e := .app Core.coreLoc (.op Core.coreLoc "List..isNil" none)
                   (.op Core.coreLoc "Nil" none) } .empty] }

/--
error: ❌ Type checking error.
Lemma 'L#1' is typed at a generated type variable that is not declared
-/
#guard_msgs in
#eval EIO.toIO (fun s => IO.userError s) (Core.verifyProgram hashLemmaPgm quietOpts)

/-! A lemma `L#1` with a type parameter is accepted: the opaque type minted for the parameter
has the `#` replaced by `_`, and the lemma keeps its name. -/

/-- A lemma `L#1` over `List` with an explicit type parameter `t`. -/
private def hashLemmaParamPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) };
lemma [|L#1|] <t>: forall x : List t :: x == x;
#end

/-- info: "[List, $__opaque_L_1_t_0]" -/
#guard_msgs in
#eval match Core.typeCheck quietOpts (translateWithMetaData hashLemmaParamPgm) with
  | .error m => toString m
  | .ok tc => match Core.Transform.run tc Core.genOpaqueTypeParams with
    | .ok (_, p) => toString (Core.Program.typeNames p)
    | .error m => toString m

/-- info: #[("L#1", true)] -/
#guard_msgs in
#eval do
  let r ← EIO.toIO (fun s => IO.userError s)
    (Core.verifyProgram (translateWithMetaData hashLemmaParamPgm) quietOpts)
  return r.map fun (v : Core.VCResult) => (v.obligation.label, v.isSuccess)

/-- A lemma whose name contains `#` but from which no opaque type is built is accepted, and
    is verified under its own name. -/
private def hashLabelLemmaPgm :=
#strata
program Core;
lemma [|L#1|]: true;
#end

/-- info: #[("L#1", true)] -/
#guard_msgs in
#eval do
  let r ← EIO.toIO (fun s => IO.userError s)
    (Core.verifyProgram (translateWithMetaData hashLabelLemmaPgm) quietOpts)
  return r.map fun (v : Core.VCResult) => (v.obligation.label, v.isSuccess)

/-- A pipeline that runs the pass twice is accepted: the second run finds no polymorphic
    function left, and the first run's copies are ordinary names to it. -/
private def twiceMsg : String :=
  match Core.typeCheck quietOpts (translateWithMetaData factoryClashPgm) with
  | .error msg => s!"{msg}"
  | .ok tc =>
    let seedState : Core.Transform.CoreTransformState :=
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
    let twice (p : Core.Program) : Core.Transform.CoreTransformM Core.Program := do
      Core.MonomorphizeFunctions.run (← Core.MonomorphizeFunctions.run p)
    match (Core.Transform.runWith tc twice seedState).1 with
    | .ok _ => "OK"
    | .error m => toString m

/--
info: "OK"
-/
#guard_msgs in
#eval twiceMsg

end
