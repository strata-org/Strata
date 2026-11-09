/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataLaurel.Tests.Util.TestLaurel
meta import StrataLaurel.Implementation.Interpreter
import StrataLaurel.Implementation.LowerComposite
import StrataLaurel.Implementation.ConstrainedTypeElim
import StrataLaurel.Implementation.MonomorphizeComposites

open Strata
open StrataTest.Util

namespace Strata.Laurel

private meta def animals : StrataDDM.Program :=
#strata
program Laurel;
composite Animal { var legs: int }
composite Cat extends Animal { var lives: int }
procedure main()
  opaque
  modifies *
{
  var c: Cat := new Cat;
  c#legs := 4;
  c#lives := 9;
  var a: Animal := c;
  assert a is Cat;
  assert a#legs == 4;
  var back: Cat := a as Cat;
  assert back#lives == 9;
  assert back == c;
  var d: Cat := new Cat;
  assert d != c;
  assert d#lives == 1
};
#end

/--
info: datatype TypeTag { Animal_TypeTag, Cat_TypeTag }
datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }
constrained Animal = $c: Composite where Composite..typeTag!($c) == Animal_TypeTag() | Composite..typeTag!($c) == Cat_TypeTag() witness MkComposite(0, Animal_TypeTag())
constrained Cat = $c: Composite where Composite..typeTag!($c) == Cat_TypeTag() witness MkComposite(0, Cat_TypeTag())
$heapfield var Animal.legs: int
$heapfield var Cat.lives: int
procedure main()
  opaque
  modifies *
{
  var c: Cat := MkComposite($allocate(), Cat_TypeTag());
  Composite..ref!(c)#Animal.legs := 4;
  Composite..ref!(c)#Cat.lives := 9;
  var a: Animal := c;
  assert a is Cat;
  assert Composite..ref!(a)#Animal.legs == 4;
  var back: Cat := a as Cat;
  assert Composite..ref!(back)#Cat.lives == 9;
  assert Composite..ref!(back) == Composite..ref!(c);
  var d: Cat := MkComposite($allocate(), Cat_TypeTag());
  assert Composite..ref!(d) != Composite..ref!(c);
  assert Composite..ref!(d)#Cat.lives == 1
};
procedure $allocate()
  returns (r: int)external;
-/
#guard_msgs in
#eval runPassForIdiomaticity lowerCompositePass animals

private meta def interpretBeforeAndAfter (program : StrataDDM.Program) (monomorphize : Bool := false) :
    IO Unit := do
  let parsed ← translateLaurel program
  let resolved := resolve (withBuiltins parsed)
  let resolved := if monomorphize then
      resolve (monomorphizeComposites resolved.program resolved.model).1 (some resolved.model)
    else resolved
  let (out, messages, _) :=
    lowerCompositePass.run {} (.Unordered resolved.program) resolved.model
  let lowered := resolve out.laurelProgram! (some resolved.model)
  let (eliminated, cteMessages) := constrainedTypeElim lowered.model lowered.program
  let reresolved := resolve eliminated (some lowered.model)
  IO.println s!"diagnostics: {messages.length + cteMessages.length + lowered.errors.size + reresolved.errors.size}"
  for (label, p) in [("source", resolved.program), ("lowered", reresolved.program)] do
    let (_, failures) ← Interpreter.evalProgram {}
      { entryProcedure := "main", dumpState := false, printAsserts := false } p
    IO.println s!"{label} failures: {failures.size}"

/--
info: diagnostics: 0
source failures: 1
lowered failures: 1
-/
#guard_msgs in
#eval interpretBeforeAndAfter animals

/--
info: diagnostics: 0
source failures: 0
lowered failures: 0
-/
#guard_msgs in
#eval (interpretBeforeAndAfter (monomorphize := true)) <|
#strata
program Laurel;
composite Box<T> { var n: int }
composite D extends Box<int>, Box<bool> { }
procedure main()
  opaque
  modifies *
{
  var d: D := new D;
  var x: Box<int> := d;
  var y: Box<bool> := d;
  x#n := 1;
  y#n := 2;
  assert x#n == 2
};
#end

private meta def heapFieldsRoundTrip (program : StrataDDM.Program) (monomorphize : Bool := false) :
    IO Unit := do
  let parsed ← translateLaurel program
  let resolved := resolve (withBuiltins parsed)
  let resolved := if monomorphize then
      resolve (monomorphizeComposites resolved.program resolved.model).1 (some resolved.model)
    else resolved
  let (out, _, _) := lowerCompositePass.run {} (.Unordered resolved.program) resolved.model
  let lowered := out.laurelProgram!
  let text := toString (formatProgram { lowered with staticProcedures := [], types := [], constants := [] }).pretty
  IO.println text
  let back ← (Strata.parseLaurelText "<roundtrip>" text : IO LaurelProgram)
  IO.println s!"reparsed: {back.heapFields.map fun f => (f.name.text, f.isMutable, f.location.text)}"

/--
info: $heapfield var Animal.legs: int

$heapfield Animal.tag: bool
reparsed: [(Animal.legs, (true, Animal.legs)), (Animal.tag, (false, Animal.tag))]
-/
#guard_msgs in
#eval heapFieldsRoundTrip <|
#strata
program Laurel;
composite Animal { var legs: int  tag: bool }
#end

/--
info: $heapfield var Plain.w: bool

$heapfield var Box$a1$int.v: int as Box.v

$heapfield var Box$a1$bool.v: bool as Box.v
reparsed: [(Plain.w, (true, Plain.w)), (Box$a1$int.v, (true, Box.v)), (Box$a1$bool.v, (true, Box.v))]
-/
#guard_msgs in
#eval (heapFieldsRoundTrip (monomorphize := true)) <|
#strata
program Laurel;
composite Box<T> { var v: T }
composite Plain extends Box<int> { var w: bool }
procedure f(x: Box<int>, y: Box<bool>, z: Plain) opaque { };
#end

private meta def parsesAsIdentifier (src : String) : IO Unit := do
  try
    let _ ← (Strata.parseLaurelText "<identifier>" src : IO LaurelProgram)
    IO.println "parsed"
  catch e => IO.println s!"{e}"

/-- info: parsed
-/
#guard_msgs in
#eval parsesAsIdentifier "procedure heapfield() opaque { var heapfield: int := 1 };"

end Strata.Laurel
