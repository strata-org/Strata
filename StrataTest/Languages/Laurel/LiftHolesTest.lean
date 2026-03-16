/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the liftHoles pass correctly lifts `.Hole` nodes out of expression
positions, replacing them with fresh `$hole_N` variables, and that the type
assigned to each lifted variable is inferred from its surrounding context.
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftHoles
import Strata.Languages.Laurel.LaurelFormat

open Strata.Laurel

namespace Strata.Laurel

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

private def mkParam (n : String) (t : HighType) : Parameter :=
  { name := n, type := bareType t }

private def emptyModel : SemanticModel := { nextId := 0, compositeCount := 0, refToDef := {} }

/-- Helper: build a single-procedure program, lift holes, and print. -/
private def liftAndPrint (name : String) (body : StmtExprMd) : IO Unit := do
  let proc : Procedure := {
    name := name
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := false
    body := .Transparent body
    md := emptyMd
  }
  let prog : Program := { staticProcedures := [proc], staticFields := [], types := [] }
  let lifted := liftHoles emptyModel prog
  for p in lifted.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format p)))

/-! ## Basic: single hole in various positions -/

-- Hole in Add arg inside `var x: int` → lifted var gets type int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 1 + $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Add [bare (.LiteralInt 1), bare .Hole]))))
  ] none))

-- Bare Hole as LocalVariable initializer → preserved as havoc (not lifted).
/--
info: procedure test() returns ⏎
()
deterministic
{ var x: int := <?> }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt) (some (bare .Hole)))
  ] none))

-- Hole in comparison arg inside assert → int (inferred from sibling literal).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; assert $hole_0 > 0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .Gt [bare .Hole, bare (.LiteralInt 0)])))
  ] none))

-- Hole directly as assert condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assert $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare .Hole))
  ] none))

-- Hole directly as assume condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assume $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assume (bare .Hole))
  ] none))

-- Hole as if-then-else condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; if $hole_0 then { assert true } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.IfThenElse (bare .Hole)
      (bare (.Assert (bare (.LiteralBool true))))
      none)
  ] none))

-- Hole in then-branch of if-then-else inside `var x: int` → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then $hole_0 else 0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare .Hole)
        (some (bare (.LiteralInt 0)))))))
  ] none))

-- Hole in else-branch of if-then-else inside `var x: int` → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then 1 else $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare (.LiteralInt 1))
        (some (bare .Hole))))))
  ] none))

-- Hole as while-loop condition → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; while $hole_0 { {  } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.While (bare .Hole) [] none (bare (.Block [] none)))
  ] none))

-- Hole as while-loop invariant → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; while true invariant $hole_0 { {  } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.While (bare (.LiteralBool true)) [bare .Hole] none (bare (.Block [] none)))
  ] none))

-- Hole as while-loop decreases measure → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; while true { {  } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.While (bare (.LiteralBool true)) [] (some (bare .Hole)) (bare (.Block [] none)))
  ] none))

-- Hole as static call argument → Top.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; f(1, $hole_0) }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.StaticCall "f" [bare (.LiteralInt 1), bare .Hole])
  ] none))

-- Hole as return value → Top.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; return $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Return (some (bare .Hole)))
  ] none))

-- Hole inside Old → inherits int from `var x: int`.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := old($hole_0) }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.Old (bare .Hole)))))
  ] none))

-- Hole in And arg inside assert → bool (And propagates bool).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; assert true && $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .And [bare (.LiteralBool true), bare .Hole])))
  ] none))

-- Hole in Neg inside `var x: int` → int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := -$hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Neg [bare .Hole]))))
  ] none))

-- Hole in StrConcat inside `var s: string` → string.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: string; var s: string := "hi" ++ $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "s" (bareType .TString)
      (some (bare (.PrimitiveOp .StrConcat [bare (.LiteralString "hi"), bare .Hole]))))
  ] none))

-- Hole in ProveBy value position → inherits int from `var x: int`.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := proveBy($hole_0, true) }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.ProveBy (bare .Hole) (bare (.LiteralBool true))))))
  ] none))

-- Hole in ReferenceEquals → Top.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; assert $hole_0 === y }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare (.ReferenceEquals (bare .Hole) (bare (.Identifier "y")))))
  ] none))

/-! ## Multiple holes in one procedure -/

-- Two holes in Add → both int.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var $hole_1: int; var x: int := $hole_0 + $hole_1 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Add [bare .Hole, bare .Hole]))))
  ] none))

-- Holes in both if-then-else branches → both bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; var $hole_1: bool; var x: bool := if true then $hole_0 else $hole_1 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TBool)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare .Hole)
        (some (bare .Hole))))))
  ] none))

-- Holes across statements: Mul arg (int) then assert condition (bool).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 2 * $hole_0; var $hole_1: bool; assert $hole_1 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Mul [bare (.LiteralInt 2), bare .Hole])))),
    bare (.Assert (bare .Hole))
  ] none))

/-! ## Combinations: holes in nested contexts -/

-- Hole in Add inside Gt inside if condition → int (inferred from sibling literal 0).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; if 1 + $hole_0 > 0 then { assert true } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.IfThenElse
      (bare (.PrimitiveOp .Gt [
        bare (.PrimitiveOp .Add [bare (.LiteralInt 1), bare .Hole]),
        bare (.LiteralInt 0)]))
      (bare (.Assert (bare (.LiteralBool true))))
      none)
  ] none))

-- Hole in Lt inside while condition → int (inferred from sibling literal).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; while 0 < $hole_0 { {  } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.While
      (bare (.PrimitiveOp .Lt [bare (.LiteralInt 0), bare .Hole]))
      [] none (bare (.Block [] none)))
  ] none))

-- Hole in call arg inside `var x: int` → Top (call arg, not var type).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; var x: int := compute($hole_0) }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.StaticCall "compute" [bare .Hole]))))
  ] none))

-- Hole in And: Gt arg (int from sibling) + direct And arg (bool).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; var $hole_1: bool; assert $hole_0 > 0 && $hole_1 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .And [
      bare (.PrimitiveOp .Gt [bare .Hole, bare (.LiteralInt 0)]),
      bare .Hole])))
  ] none))

-- Hole in Implies inside while invariant → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; while true invariant p ==> $hole_0 { {  } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.While (bare (.LiteralBool true))
      [bare (.PrimitiveOp .Implies [bare (.Identifier "p"), bare .Hole])]
      none (bare (.Block [] none)))
  ] none))

-- Hole as inner if condition (nested if-then-else) → bool.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; if true then { if $hole_0 then { assert true } } }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.IfThenElse (bare (.LiteralBool true))
      (bare (.IfThenElse (bare .Hole)
        (bare (.Assert (bare (.LiteralBool true))))
        none))
      none)
  ] none))

-- Hole in Sub inside Leq inside assert → int (Leq infers int from sibling literal 10).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; assert 5 - $hole_0 <= 10 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .Leq [
      bare (.PrimitiveOp .Sub [bare (.LiteralInt 5), bare .Hole]),
      bare (.LiteralInt 10)])))
  ] none))

-- Hole in Mul inside `var r: real` → real.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: real; var r: real := 3.14 * $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrint "test" (bare (.Block [
    bare (.LocalVariable "r" (bareType .TReal)
      (some (bare (.PrimitiveOp .Mul [bare (.LiteralDecimal ⟨314, -2⟩), bare .Hole]))))
  ] none))

/-! ## Call argument and return type inference -/

/-- Helper: build a program with extra procedures (for callee lookup), lift holes,
    and print only the named procedure. -/
private def liftAndPrintWith (name : String) (body : StmtExprMd)
    (inputs : List Parameter := []) (outputs : List Parameter := [])
    (extraProcs : List Procedure := []) : IO Unit := do
  let proc : Procedure := {
    name := name
    inputs := inputs
    outputs := outputs
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := false
    body := .Transparent body
    md := emptyMd
  }
  let prog : Program := {
    staticProcedures := extraProcs ++ [proc]
    staticFields := []
    types := []
  }
  let lifted := liftHoles emptyModel prog
  match lifted.staticProcedures.getLast? with
  | some p => IO.println (toString (Std.Format.pretty (Std.ToFormat.format p)))
  | none => IO.println "ERROR: no procedures"

private def mkExternalProc (name : String) (inputs : List Parameter)
    (outputs : List Parameter := []) : Procedure := {
  name := name
  inputs := inputs
  outputs := outputs
  preconditions := []
  determinism := .deterministic none
  decreases := none
  isFunctional := false
  body := .External
  md := emptyMd
}

-- Hole in call arg with known callee → infers param type (int).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: int; f(1, $hole_0) }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.StaticCall "f" [bare (.LiteralInt 1), bare .Hole])
  ] none))
  (extraProcs := [mkExternalProc "f"
    [mkParam "a" .TInt, mkParam "b" .TInt]])

-- Hole in first call arg, second arg is string → infers param types positionally.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; g($hole_0, "hi") }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.StaticCall "g" [bare .Hole, bare (.LiteralString "hi")])
  ] none))
  (extraProcs := [mkExternalProc "g"
    [mkParam "flag" .TBool, mkParam "msg" .TString]])

-- Hole in call arg with unknown callee → falls back to Top.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; unknown(1, $hole_0) }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.StaticCall "unknown" [bare (.LiteralInt 1), bare .Hole])
  ] none))

-- Hole in call arg inside typed LocalVariable, callee known → param type (not var type).
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: bool; var x: int := compute($hole_0) }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.StaticCall "compute" [bare .Hole]))))
  ] none))
  (extraProcs := [mkExternalProc "compute"
    [mkParam "flag" .TBool]
    [mkParam "result" .TInt]])

-- Hole as return value with known output type → infers int.
/--
info: procedure test() returns ⏎
(result: int)
deterministic
{ var $hole_0: int; return $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.Return (some (bare .Hole)))
  ] none))
  (outputs := [mkParam "result" .TInt])

-- Hole in return with no output params → Top.
/--
info: procedure test() returns ⏎
()
deterministic
{ var $hole_0: ⊤; return $hole_0 }
-/
#guard_msgs in
#eval! liftAndPrintWith "test"
  (bare (.Block [
    bare (.Return (some (bare .Hole)))
  ] none))

end Laurel
