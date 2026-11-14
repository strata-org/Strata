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

meta section

open Strata

/-! ## `MonomorphizeFunctions` rejects input names that look mangled

`MonomorphizeFunctions` names the copy of `id` at `int` `$__mono#id#int`. A program that
already declared a function with that name would get two declarations with one name, and
the renamed call `id(5)` would resolve to the first: the user's constant `6`, not `id`. The
postcondition `r == 6`, false of the input (`id(5) = 5`), would then hold of the output.
The pass therefore rejects any program with a name or operator containing `#`.
-/

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

private def fmtMonoFns (t : StrataDDM.Program) : IO Std.Format := do
  let prog := translate t
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
info: error: MonomorphizeFunctions: the name '$__mono#id#int' contains '#', which is reserved for monomorphized copies; if it is a copy, monomorphizeFunctions ran on its own output, and it must run once per pipeline
-/
#guard_msgs in
#eval fmtMonoFns clashPgm

/-! Every kind of name the check inspects is rejected, not only a function's. -/

private def hashDatatypePgm :=
#strata
program Core;
datatype |D#1| { Mk(v : int) };
#end

/--
info: error: MonomorphizeFunctions: the name 'D#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval fmtMonoFns hashDatatypePgm

private def hashConstructorPgm :=
#strata
program Core;
datatype D { |Mk#1|(v : int) };
#end

/--
info: error: MonomorphizeFunctions: the name 'Mk#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval fmtMonoFns hashConstructorPgm

private def hashFieldPgm :=
#strata
program Core;
datatype D { Mk(|v#1| : int) };
#end

/--
info: error: MonomorphizeFunctions: the name 'v#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval fmtMonoFns hashFieldPgm

/-- An operator name is checked even when nothing declares it: the axiom below refers to
    `g#1`, which no declaration introduces (the program is built directly, since it would
    not type-check). -/
private def hashOpProgram : Core.Program :=
  { decls := [.ax { name := "a", e := .op default ⟨"g#1", ()⟩ none } .empty] }

/--
info: "MonomorphizeFunctions: the name 'g#1' contains '#', which is reserved for monomorphized copies"
-/
#guard_msgs in
#eval match Core.Transform.run hashOpProgram (fun p => Core.MonomorphizeFunctions.run p) with
  | .ok _ => "OK"
  | .error m => toString m

/-- An opaque type whose name contains `#` is rejected, and so is a type constructor with
    `#` in an operator's annotation: the pass names copies after the type constructors of
    their instantiation. -/
private def hashTypePgm :=
#strata
program Core;
type |Foo#bar|;
function c() : |Foo#bar|;
axiom [a]: c() == c();
#end

/--
info: error: MonomorphizeFunctions: the name 'Foo#bar' contains '#', which is reserved for monomorphized copies
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
info: error: MonomorphizeFunctions: the name 'T#1#int' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval fmtMonoFns typeClashPgm

/-- A type synonym whose name contains `#` is rejected too. -/
private def hashSynonymPgm :=
#strata
program Core;
type |S#1| := int;
#end

/--
info: error: MonomorphizeFunctions: the name 'S#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval fmtMonoFns hashSynonymPgm

/-- A Factory function named like a copy is rejected too, though the program never declares
    or calls it: a front end can supply Factory functions, and this one would share its name
    with the copy of `id` at `int`. -/
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
  match Core.typeCheck quietOpts (translate t), Core.Factory.toArray[0]? with
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
info: "MonomorphizeFunctions: the name '$__mono#id#int' contains '#', which is reserved for monomorphized copies; if it is a copy, monomorphizeFunctions ran on its own output, and it must run once per pipeline"
-/
#guard_msgs in
#eval monoWithFactoryFn factoryClashPgm "$__mono#id#int"

-- The same Factory function under a name without `#` is accepted.
#guard monoWithFactoryFn factoryClashPgm "extraFn" == "OK"

-- `tconsNames` collects type constructors nested inside other types' arguments.
#guard Core.NameMangling.tconsNames
    (.tcons "Map" [.int, .tcons "Set" [.tcons "Foo#bar" []]]) == ["Map", "int", "Set", "Foo#bar"]

/-- A `#` type constructor nested in an operator's annotation is rejected even when nothing
    declares it (the program is built directly, since it would not type-check). -/
private def nestedHashTyProgram : Core.Program :=
  let ty : Lambda.LMonoTy := .tcons "Map" [.int, .tcons "Set" [.tcons "Foo#bar" []]]
  { decls := [.ax { name := "a", e := .op default ⟨"g", ()⟩ (some ty) } .empty] }

/--
info: "MonomorphizeFunctions: the name 'Foo#bar' contains '#', which is reserved for monomorphized copies"
-/
#guard_msgs in
#eval match Core.Transform.run nestedHashTyProgram (fun p => Core.MonomorphizeFunctions.run p) with
  | .ok _ => "OK"
  | .error m => toString m

/-- A polymorphic procedure whose name contains `#` is rejected by the full pipeline with the
    name the user wrote, before `genOpaqueTypeParams` builds an opaque type name from it. -/
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
error: GenOpaqueTypeParams: the name 'P#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval EIO.toIO (fun s => IO.userError s) (Core.verifyProgram (translate hashProcPgm) quietOpts)

/-- A lemma whose name contains `#` is rejected with that name when an opaque type is built
    from it, even without type parameters: the element type of `Nil()` would otherwise become
    `$__free_L#1_0`. -/
private def hashLemmaPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(hd : a, tl : List a) };
lemma [|L#1|]: List..isNil(Nil());
#end

/--
error: ❌ Type checking error.
GenOpaqueTypeParams: the name 'L#1' contains '#', which is reserved for monomorphized copies
-/
#guard_msgs in
#eval EIO.toIO (fun s => IO.userError s) (Core.verifyProgram (translate hashLemmaPgm) quietOpts)

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
    (Core.verifyProgram (translate hashLabelLemmaPgm) quietOpts)
  return r.map fun (v : Core.VCResult) => (v.obligation.label, v.isSuccess)

/-- A pipeline that runs the pass twice is rejected by the second run, which finds the first
    one's copies, and the error says so: it never yields a verdict. -/
private def twiceMsg : String :=
  match Core.typeCheck quietOpts (translate factoryClashPgm) with
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
info: "MonomorphizeFunctions: the name '$__mono#id#int' contains '#', which is reserved for monomorphized copies; if it is a copy, monomorphizeFunctions ran on its own output, and it must run once per pipeline"
-/
#guard_msgs in
#eval twiceMsg

end
