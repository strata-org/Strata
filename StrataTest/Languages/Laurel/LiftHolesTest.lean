/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the eliminateHoles pass correctly replaces `.Hole` nodes with calls
to freshly generated uninterpreted procedures, with types inferred from context.
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.InferHoleTypes
meta import Strata.Languages.Laurel.EliminateHoles
meta import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string, resolve, eliminate holes, and print all procedures. -/
private def parseElimAndPrint (input : String) : IO Unit := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    let (program, _, _) := inferHoleTypes model program
    let (program, _) := eliminateHoles program
    for proc in program.staticProcedures do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Basic: single hole in various positions -/

-- Hole in Add arg inside typed local variable → int.
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := 1 + $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := 1 + <?> };
"

-- Bare Hole as Assign Declare initializer → replaced with call (no longer preserved as havoc).
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := <?> };
"

-- Hole in comparison arg inside assert → int (inferred from sibling literal).
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  assert $hole_0() > 0
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ assert <?> > 0 };
"

-- Hole directly as assert condition → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assert $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ assert <?> };
"

-- Hole directly as assume condition → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assume $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ assume <?> };
"

-- Hole as if-then-else condition → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  if $hole_0()
  then {
    assert true
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ if <?> then { assert true } };
"

-- Hole in then-branch of if-then-else inside typed local variable → int.
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := if true
  then $hole_0()
  else 0
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := if true then <?> else 0 };
"

-- Hole as while-loop condition → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  while($hole_0()) {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ while(<?>) {} };
"

-- Hole as while-loop invariant → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  while(true)
    invariant $hole_0() {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ while(true) invariant <?> {} };
"

/-! ## Operators -/

-- Hole in And arg inside assert → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assert true && $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ assert true && <?> };
"

-- Hole in Neg inside typed local variable → int.
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := -$hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := -<?> };
"

-- Hole in StrConcat inside typed local variable → string.
/--
info: procedure $hole_0()
  returns ($result: string)
  opaque;
procedure test()
{
  var s: string := "hello" ++ $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint
  "procedure test() { var s: string := \"hello\" ++ <?> };"

/-! ## Multiple holes -/

-- Two holes in Add → both int, separate procedures.
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure $hole_1()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0() + $hole_1()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := <?> + <?> };
"

-- Holes across statements: Mul arg (int) then assert condition (bool).
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure $hole_1()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  var x: int := 2 * $hole_0();
  assert $hole_1()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := 2 * <?>; assert <?> };
"

/-! ## Combinations: holes in nested contexts -/

-- Hole in Add inside Gt inside if condition → int (inferred from sibling literal 0).
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  if 1 + $hole_0() > 0
  then {
    assert true
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ if 1 + <?> > 0 then { assert true } };
"

-- Hole in Implies inside while invariant → bool.
/--
info: procedure $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  var p: bool;
  while(true)
    invariant p ==> $hole_0() {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var p: bool; while(true) invariant p ==> <?> {} };
"

-- Hole in Mul inside typed local variable with real type → real.
/--
info: procedure $hole_0()
  returns ($result: real)
  opaque;
procedure test()
  opaque
{
  var r: real := 3.14 * $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var r: real := 3.14 * <?> };
"

/-! ## Call argument and return type inference -/

-- Hole in comparison with variable sibling → hole procedure takes the procedure's params.
/--
info: procedure $hole_0(n: int)
  returns ($result: int)
  opaque;
procedure test(n: int)
  opaque
{
  assert n > $hole_0(n)
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test(n: int)
  opaque
{ assert n > <?> };
"

/-! ## Holes in procedures -/

-- Hole in procedure body → same treatment as procedures.
/--
info: procedure $hole_0(x: int)
  returns ($result: int)
  opaque;
procedure test(x: int): int
{
  $hole_0(x)
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test(x: int): int
{ <?> };
"

/-! ## Nondeterministic holes (<??>) -/

-- Nondet hole in procedure → preserved after eliminateHoles (lifted by liftExpressionAssignments).
/--
info: procedure test()
  opaque
{
  assert <??>
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ assert <??> };
"

-- Mixed: det hole eliminated, nondet hole preserved.
/--
info: procedure $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0();
  assert <??>
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test()
  opaque
{ var x: int := <?>; assert <??> };
"

-- Nondet hole in procedure → should be rejected (not tested here since
-- the error occurs at Core translation time, which requires the full pipeline).

/-! ## Holes inside datatype destructor / tester arguments -/

-- Hole as argument to a (safe) datatype destructor → typed as the parent
-- datatype, then lifted to a generated `$hole_0` returning that datatype.
-- Regression test for PR #1134: the destructor's `ResolvedNode` carries the
-- parent datatype's resolved Identifier (with `uniqueId`), so this works
-- without textual decoding of the override name.
/--
info: procedure $hole_0()
  returns ($result: IntList)
  opaque;
procedure test()
{
  var x: int := IntList..head($hole_0())
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
datatype IntList { Nil(), Cons(head: int, tail: IntList) }
procedure test() { var x: int := IntList..head(<?>) };
"

-- Hole as argument to an unsafe `!` destructor → same datatype recovery.
/--
info: procedure $hole_0()
  returns ($result: IntList)
  opaque;
procedure test()
{
  var x: int := IntList..head!($hole_0())
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
datatype IntList { Nil(), Cons(head: int, tail: IntList) }
procedure test() { var x: int := IntList..head!(<?>) };
"

-- Hole as argument to a tester → typed as the parent datatype.
/--
info: procedure $hole_0()
  returns ($result: IntList)
  opaque;
procedure test()
{
  assert IntList..head($hole_0())
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
datatype IntList { Nil(), Cons(head: int, tail: IntList) }
procedure test() { assert IntList..head(<?>) };
"

end Laurel
end Strata
end
