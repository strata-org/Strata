/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the StaticFieldParameterization pass, which eliminates static fields
by converting them to explicit in/out parameters on procedures.

Uses the Laurel parser to construct programs (similar to LiftHolesTest.lean),
then adds staticFields and runs the pass.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.StaticFieldParameterization

open Strata
open Strata.Elab (parseStrataProgramFromDialect)
open Strata.Laurel

namespace Strata.Laurel.StaticFieldParameterizationTest

/-! ## Helpers -/

private def intTy : HighTypeMd := ⟨.TInt, none, .empty⟩

private def mkField (n : String) : Field :=
  { name := mkId n, isMutable := true, type := intTy }

/-- Parse a Laurel source string, add static fields, run the pass, and print procedures. -/
private def parseTransformAndPrint (input : String) (fields : List Field := []) : IO Unit := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let program := { program with staticFields := fields }
    let result := staticFieldParameterization program
    for proc in result.staticProcedures do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Test: No static fields → pass is a no-op -/

/--
info: procedure noop()
1;
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure noop()
  1;
"

/-! ## Test: Single global write — writer gets in/out params, __main__ keeps locals -/

/--
info: procedure writer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 42 } };
procedure __main__()
{ var $sf_x: int := <?>; $sf_x := writer($sf_x) };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure writer()
  { var $sf_x: int := <?>; $sf_x := 42 };

procedure __main__()
  { var $sf_x: int := <?>; writer() };
" [mkField "x"]

/-! ## Test: Read-only access → input parameter only, no output -/

/--
info: procedure reader($sf_in_x: int)
{ $sf_x := $sf_in_x; { $sf_x } };
procedure __main__()
{ var $sf_x: int := <?>; reader($sf_x) };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure reader()
  { var $sf_x: int := <?>; $sf_x };

procedure __main__()
  { var $sf_x: int := <?>; reader() };
" [mkField "x"]

/-! ## Test: Multiple globals, procedure uses only a subset -/

/--
info: procedure usesX($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 1 } };
procedure __main__()
{ var $sf_x: int := <?>; var $sf_y: int := <?>; $sf_x := usesX($sf_x) };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure usesX()
  { var $sf_x: int := <?>; $sf_x := 1 };

procedure __main__()
  { var $sf_x: int := <?>; var $sf_y: int := <?>; usesX() };
" [mkField "x", mkField "y"]

/-! ## Test: Transitive propagation — caller inherits callee's field usage -/

/--
info: procedure inner($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 99 } };
procedure outer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := inner($sf_x) } };
procedure __main__()
{ var $sf_x: int := <?>; $sf_x := outer($sf_x) };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure inner()
  { var $sf_x: int := <?>; $sf_x := 99 };

procedure outer()
  { var $sf_x: int := <?>; inner() };

procedure __main__()
  { var $sf_x: int := <?>; outer() };
" [mkField "x"]

/-! ## Test: Two globals — both written by same procedure -/

/--
info: procedure writesBoth($sf_in_a: int, $sf_in_b: int)
  returns ($sf_a: int, $sf_b: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_a := 1; $sf_b := 2 } };
procedure __main__()
{ var $sf_a: int := <?>; var $sf_b: int := <?>; $sf_a := writesBoth($sf_a, $sf_b) };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure writesBoth()
  { var $sf_a: int := <?>; var $sf_b: int := <?>; $sf_a := 1; $sf_b := 2 };

procedure __main__()
  { var $sf_a: int := <?>; var $sf_b: int := <?>; writesBoth() };
" [mkField "a", mkField "b"]

/-! ## Test: Procedure with existing parameters — SF params prepended -/

/--
info: procedure addToGlobal($sf_in_x: int, n: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := $sf_x + n } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure addToGlobal(n: int)
  { var $sf_x: int := <?>; $sf_x := $sf_x + n };
" [mkField "x"]

/-! ## Test: Procedure with existing outputs — SF outputs prepended -/

/--
info: procedure getAndBump($sf_in_x: int)
  returns ($sf_x: int, $result: int)
{ $sf_x := $sf_in_x; { var old: int := $sf_x; $sf_x := $sf_x + 1; old } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure getAndBump()
  returns ($result: int)
  { var $sf_x: int := <?>; var old: int := $sf_x; $sf_x := $sf_x + 1; old };
" [mkField "x"]

/-! ## Test: Write one, read another — mixed in/out parameters -/

/--
info: procedure copyAtoB($sf_in_a: int, $sf_in_b: int)
  returns ($sf_b: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_b := $sf_a } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure copyAtoB()
  { var $sf_a: int := <?>; var $sf_b: int := <?>; $sf_b := $sf_a };
" [mkField "a", mkField "b"]

/-! ## Test: staticFields is cleared after the pass -/

/--
info: true
-/
#guard_msgs in
#eval! do
  let inputCtx := Strata.Parser.stringInputContext "test" r"
procedure f()
  { var $sf_x: int := <?>; $sf_x := 1 };

procedure __main__()
  { var $sf_x: int := <?>; f() };
"
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let program := { program with staticFields := [mkField "x"] }
    IO.println (toString (staticFieldParameterization program).staticFields.isEmpty)

/-! ## Test: Call to non-SF procedure is unchanged -/

/--
info: procedure helper()
42;
procedure writer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := helper() } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure helper()
  42;

procedure writer()
  { var $sf_x: int := <?>; $sf_x := helper() };
" [mkField "x"]

/-! ## Test: Conditional write — if branch writes global -/

/--
info: procedure condWriter($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { if true then $sf_x := 1 else $sf_x := 2 } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure condWriter()
  { var $sf_x: int := <?>; if true then $sf_x := 1 else $sf_x := 2 };
" [mkField "x"]

/-! ## Test: Global in while loop body -/

/--
info: procedure looper($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { while(true) { $sf_x := $sf_x + 1 } } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure looper()
  { var $sf_x: int := <?>; while(true) { $sf_x := $sf_x + 1 } };
" [mkField "x"]

/-! ## Test: Two procedures write the same global, caller calls both -/

/--
info: procedure setA($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 1 } };
procedure setB($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 2 } };
procedure callBoth($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := setA($sf_x); $sf_x := setB($sf_x) } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure setA()
  { var $sf_x: int := <?>; $sf_x := 1 };

procedure setB()
  { var $sf_x: int := <?>; $sf_x := 2 };

procedure callBoth()
  { var $sf_x: int := <?>; setA(); setB() };
" [mkField "x"]

/-! ## Test: Procedure writes global a, reads global b — correct parameter separation -/

/--
info: procedure swapper($sf_in_a: int, $sf_in_b: int)
  returns ($sf_a: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_a := $sf_b } };
-/
#guard_msgs in
#eval! parseTransformAndPrint r"
procedure swapper()
  { var $sf_a: int := <?>; var $sf_b: int := <?>; $sf_a := $sf_b };
" [mkField "a", mkField "b"]

end Strata.Laurel.StaticFieldParameterizationTest
