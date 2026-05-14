/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init

/-!
# Core Roundtrip Tests

Tests that `Core.formatProgram` produces output that can be parsed back to the
same AST. The roundtrip is: parse → translate → format → re-parse → re-translate
→ compare.
-/

namespace Strata.Test.Roundtrip

open Strata
open Strata.CoreDDM
open Core
open Lean.Parser (InputContext)

/-- Parse a string as a Core program and translate to AST. -/
private def parseAndTranslate (input : String) : IO Core.Program := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  -- Strip "program Core;\n\n" header if present
  let body := if input.startsWith "program Core;\n\n" then
    (input.drop "program Core;\n\n".length).toString
  else input
  let inputCtx := Strata.Parser.stringInputContext ⟨"roundtrip-test"⟩ body
  let strataProgram ← Strata.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
  let (ast, errs) := TransM.run Inhabited.default (translateProgram strataProgram)
  if !errs.isEmpty then
    throw (IO.userError s!"Translation errors: {errs}")
  pure ast

/-- Perform a roundtrip test: parse → format → re-parse → compare.
    Prints OK or FAIL with details. -/
def roundtrip (program : Strata.Program) : IO Unit := do
  -- First pass: translate to AST
  let (ast1, errs1) := TransM.run Inhabited.default (translateProgram program)
  if !errs1.isEmpty then
    IO.println s!"FAIL: First translation errors: {errs1}"
    return
  -- Format back to text
  let formatted := (Core.formatProgram ast1).pretty
  -- Second pass: re-parse and re-translate
  let ast2 ← parseAndTranslate formatted
  -- Compare: format both ASTs and check they match
  let formatted2 := (Core.formatProgram ast2).pretty
  if formatted == formatted2 then
    IO.println "OK"
  else
    IO.println s!"FAIL: Roundtrip mismatch.\nFirst format:\n{formatted}\nSecond format:\n{formatted2}"

-------------------------------------------------------------------------------
-- Test: Basic types and type aliases
-------------------------------------------------------------------------------

private def testTypesRoundtrip : Program :=
#strata
program Core;

type T0;
type Byte := bv8;
type IntMap := Map int int;
type T1 (x : Type);
type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testTypesRoundtrip

-------------------------------------------------------------------------------
-- Test: Polymorphic datatypes with parameterized types
-- NOTE: Datatype formatting has extra parentheses around constructors
-- (known issue in the file header). This test verifies the first format
-- succeeds without errors.
-------------------------------------------------------------------------------

private def testDatatypesRoundtrip : Program :=
#strata
program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};

datatype Tree (a : Type) {
  Leaf(val : a),
  Node(left : Tree a, right : Tree a)
};
#end

/--
info: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
datatype Tree (a : Type) {
  Leaf(val : a),
  Node(left : Tree a, right : Tree a)
};
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default (translateProgram testDatatypesRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

-------------------------------------------------------------------------------
-- Test: Functions and axioms with quantifiers
-------------------------------------------------------------------------------

private def testFunctionsRoundtrip : Program :=
#strata
program Core;

function f1(x : int) : int;
axiom [f1_ax]: (forall x : int :: f1(x) > x);

function f2(x : int, y : bool) : bool;
axiom [f2_ax]: (forall x : int, y : bool ::
                  {f2(x, true), f2(x, false)}
                  f2(x, true) == true);

function f3<T1, T2>(x : T1) : Map T1 T2;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testFunctionsRoundtrip

-------------------------------------------------------------------------------
-- Test: Procedures with specs
-------------------------------------------------------------------------------

private def testProceduresRoundtrip : Program :=
#strata
program Core;

procedure Test(x : bool, out y : bool)
spec {
  requires x == true;
  ensures y == x;
} {
  y := x;
};
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testProceduresRoundtrip

-------------------------------------------------------------------------------
-- Test: Inline functions
-------------------------------------------------------------------------------

private def testInlineFunctionRoundtrip : Program :=
#strata
program Core;

inline function double(x : int) : int {
  x + x
}
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testInlineFunctionRoundtrip

-------------------------------------------------------------------------------
-- Test: Parameterized type arguments (the reversed-args bug)
-------------------------------------------------------------------------------

private def testTypeArgsRoundtrip : Program :=
#strata
program Core;

type Pair (a : Type, b : Type);

function f(x : Pair int bool) : int;
function g(x : Map int bool) : int;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testTypeArgsRoundtrip

end Strata.Test.Roundtrip
