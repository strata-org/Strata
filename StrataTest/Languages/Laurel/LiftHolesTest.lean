/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the eliminateHoles pass correctly replaces `.Hole` nodes with calls
to freshly generated uninterpreted functions, with types inferred from context.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateHoles
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string, resolve, eliminate holes, and print all procedures. -/
private def parseElimAndPrint (input : String) : IO Unit := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    let (program, _) := inferHoleTypes model program
    let (program, _) := eliminateHoles program
    for proc in program.staticProcedures do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Basic: single hole in various positions -/

-- Hole in Add arg inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := 1 + $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := 1 + <?> };
"

-- Bare Hole as Assign Declare initializer → replaced with call (no longer preserved as havoc).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := <?> };
"

-- Hole in comparison arg inside assert → int (inferred from sibling literal).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ assert $hole_0() > 0 };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { assert <?> > 0 };
"

-- Hole directly as assert condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ assert $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { assert <?> };
"

-- Hole directly as assume condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ assume $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { assume <?> };
"

-- Hole as if-then-else condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ if $hole_0() then { assert true } };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { if <?> then { assert true } };
"

-- Hole in then-branch of if-then-else inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := if true then $hole_0() else 0 };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := if true then <?> else 0 };
"

-- Hole as while-loop condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ while($hole_0()) {  } };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { while(<?>) {} };
"

-- Hole as while-loop invariant → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ while(true)
  invariant $hole_0() {  } };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { while(true) invariant <?> {} };
"

/-! ## Operators -/

-- Hole in And arg inside assert → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ assert true && $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { assert true && <?> };
"

-- Hole in Neg inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := -$hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := -<?> };
"

-- Hole in StrConcat inside typed local variable → string.
/--
info: function $hole_0()
  returns ($result: string)
  opaque;
procedure test()
{ var s: string := "hello" ++ $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint
  "procedure test() { var s: string := \"hello\" ++ <?> };"

/-! ## Multiple holes -/

-- Two holes in Add → both int, separate functions.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
function $hole_1()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := $hole_0() + $hole_1() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := <?> + <?> };
"

-- Holes across statements: Mul arg (int) then assert condition (bool).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
function $hole_1()
  returns ($result: bool)
  opaque;
procedure test()
{ var x: int := 2 * $hole_0(); assert $hole_1() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := 2 * <?>; assert <?> };
"

/-! ## Combinations: holes in nested contexts -/

-- Hole in Add inside Gt inside if condition → int (inferred from sibling literal 0).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ if 1 + $hole_0() > 0 then { assert true } };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { if 1 + <?> > 0 then { assert true } };
"

-- Hole in Implies inside while invariant → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
{ var p: bool; while(true)
  invariant p ==> $hole_0() {  } };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var p: bool; while(true) invariant p ==> <?> {} };
"

-- Hole in Mul inside typed local variable with real type → real.
/--
info: function $hole_0()
  returns ($result: real)
  opaque;
procedure test()
{ var r: real := 3.14 * $hole_0() };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var r: real := 3.14 * <?> };
"

/-! ## Call argument and return type inference -/

-- Hole in comparison with variable sibling → hole function takes the procedure's params.
/--
info: function $hole_0(n: int)
  returns ($result: int)
  opaque;
procedure test(n: int)
{ assert n > $hole_0(n) };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test(n: int) { assert n > <?> };
"

/-! ## Holes in functions -/

-- Hole in function body → same treatment as procedures.
/--
info: function $hole_0(x: int)
  returns ($result: int)
  opaque;
function test(x: int): int
{ $hole_0(x) };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
function test(x: int): int { <?> };
"

/-! ## Nondeterministic holes (<??>) -/

-- Nondet hole in procedure → preserved after eliminateHoles (lifted by liftExpressionAssignments).
/--
info: procedure test()
{ assert <??> };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { assert <??> };
"

-- Mixed: det hole eliminated, nondet hole preserved.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := $hole_0(); assert <??> };
-/
#guard_msgs in
#eval! parseElimAndPrint r"
procedure test() { var x: int := <?>; assert <??> };
"

-- Nondet hole in function → should be rejected (not tested here since
-- the error occurs at Core translation time, which requires the full pipeline).

end Laurel
