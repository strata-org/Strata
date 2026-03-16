/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the liftHoles pass correctly lifts `.Hole` nodes out of expression
positions, replacing them with fresh `$hole_N` variables, and that the type
assigned to each lifted variable is inferred from its surrounding context.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LiftHoles
import Strata.Languages.Laurel.LaurelFormat

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string, resolve, lift holes, and print all procedures. -/
private def parseLiftAndPrint (input : String) : IO Unit := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    let lifted := liftHoles model program
    for proc in lifted.staticProcedures do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Basic: single hole in various positions -/

-- Hole in Add arg inside typed local variable → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 1 + $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := 1 + <?> };
"

-- Bare Hole as LocalVariable initializer → preserved as havoc (not lifted).
/--
info: procedure test() returns ⏎
()
deterministic
{ var x: int := <?> }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := <?> };
"

-- Hole in comparison arg inside assert → int (inferred from sibling literal).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; assert $hole_0 > 0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assert <?> > 0 };
"

-- Hole directly as assert condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assert $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assert <?> };
"

-- Hole directly as assume condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assume $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assume <?> };
"

-- Hole as if-then-else condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; if $hole_0 then { { assert true } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { if (<?>) { assert true } };
"

-- Hole in then-branch of if-then-else inside typed local variable → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then $hole_0 else 0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := if (true) <?> else 0 };
"

-- Hole in else-branch of if-then-else inside typed local variable → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then 1 else $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := if (true) 1 else <?> };
"

-- Hole as while-loop condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; while $hole_0 { {  } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { while(<?>) {} };
"

-- Hole as while-loop invariant → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; while true invariant $hole_0 { {  } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { while(true) invariant <?> {} };
"

-- Hole as return value → Top (no output params).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; return $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { return <?> };
"

/-! ## Operators -/

-- Hole in And arg inside assert → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assert true && $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assert true && <?> };
"

-- Hole in Neg inside typed local variable → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := -$hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := -<?> };
"

-- Hole in StrConcat inside typed local variable → string.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: string; var s: string := "hello" ++ $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint
  "procedure test() { var s: string := \"hello\" ++ <?> };"

/-! ## Multiple holes -/

-- Two holes in Add → both int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var $hole_1: int; var x: int := $hole_0 + $hole_1 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := <?> + <?> };
"

-- Holes in both if-then-else branches → both bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; var $hole_1: bool; var x: bool := if true then $hole_0 else $hole_1 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: bool := if (true) <?> else <?> };
"

-- Holes across statements: Mul arg (int) then assert condition (bool).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 2 * $hole_0; var $hole_1: bool; assert $hole_1 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var x: int := 2 * <?>; assert <?> };
"

/-! ## Combinations: holes in nested contexts -/

-- Hole in Add inside Gt inside if condition → int (inferred from sibling literal 0).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; if 1 + $hole_0 > 0 then { { assert true } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { if (1 + <?> > 0) { assert true } };
"

-- Hole in Lt inside while condition → int (inferred from sibling literal).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; while 0 < $hole_0 { {  } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { while(0 < <?>) {} };
"

-- Hole in And: Gt arg (int from sibling) + direct And arg (bool).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var $hole_1: bool; assert $hole_0 > 0 && $hole_1 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assert <?> > 0 && <?> };
"

-- Hole in Implies inside while invariant → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var p: bool; var $hole_0: bool; while true invariant p ==> $hole_0 { {  } } }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var p: bool; while(true) invariant p ==> <?> {} };
"

-- Hole in Sub inside Leq inside assert → int (Leq infers int from sibling literal 10).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; assert 5 - $hole_0 <= 10 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { assert 5 - <?> <= 10 };
"

-- Hole in Mul inside typed local variable with real type → real.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: real; var r: real := 3.14 * $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() { var r: real := 3.14 * <?> };
"

/-! ## Call argument and return type inference -/

-- Hole in call arg with known callee → infers param type (int).
/--
info: procedure f(a: int, b: int) returns ⏎
()
deterministic
external
procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; f(1, $hole_0) }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure f(a: int, b: int) external;
procedure test() { f(1, <?>) };
"

-- Hole in first call arg, second arg is string → infers param types positionally.
/--
info: procedure g(flag: bool, msg: string) returns ⏎
()
deterministic
external
procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; g($hole_0, "hello") }
-/
#guard_msgs in
#eval! parseLiftAndPrint
  "procedure g(flag: bool, msg: string) external;\nprocedure test() { g(<?>, \"hello\") };"

-- Hole as return value with known output type → int.
/--
info: procedure test() returns ⏎
(result: int)
deterministic
{ var $hole_0: int; return $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test() returns(result: int) { return <?> };
"

-- Hole in comparison with variable sibling → infers type from variable.
/--
info: procedure test(n: int) returns ⏎
()
deterministic
{ var $hole_0: int; assert n > $hole_0 }
-/
#guard_msgs in
#eval! parseLiftAndPrint r"
procedure test(n: int) { assert n > <?> };
"

end Laurel
