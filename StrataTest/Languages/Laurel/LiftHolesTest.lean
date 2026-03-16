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
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelFormat

open Strata.Laurel

namespace Strata.Laurel

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

private def mkProc (name : String) (body : StmtExprMd) : Procedure := {
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

private def mkParam (n : String) (t : HighType) : Parameter :=
  { name := n, type := bareType t }

private def printProgram (p : Program) : IO Unit := do
  for proc in p.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Basic: single hole in various positions -/

/-- Hole in arithmetic PrimitiveOp arg, inside a typed LocalVariable → int. -/
def holeInArithmeticOp : Procedure :=
  mkProc "holeInArithmeticOp" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Add [bare (.LiteralInt 1), bare .Hole]))))
  ] none))

/-- Bare Hole as LocalVariable initializer → preserved as havoc. -/
def holeAsInitializer : Procedure :=
  mkProc "holeAsInitializer" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt) (some (bare .Hole)))
  ] none))

/-- Hole in comparison arg inside assert → Top (comparison arg type unknown). -/
def holeInComparisonInsideAssert : Procedure :=
  mkProc "holeInComparisonInsideAssert" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .Gt [bare .Hole, bare (.LiteralInt 0)])))
  ] none))

/-- Hole directly as assert condition → bool. -/
def holeAsAssertCondition : Procedure :=
  mkProc "holeAsAssertCondition" (bare (.Block [
    bare (.Assert (bare .Hole))
  ] none))

/-- Hole directly as assume condition → bool. -/
def holeAsAssumeCondition : Procedure :=
  mkProc "holeAsAssumeCondition" (bare (.Block [
    bare (.Assume (bare .Hole))
  ] none))

/-- Hole as if-then-else condition → bool. -/
def holeAsIfCondition : Procedure :=
  mkProc "holeAsIfCondition" (bare (.Block [
    bare (.IfThenElse (bare .Hole)
      (bare (.Assert (bare (.LiteralBool true))))
      none)
  ] none))

/-- Hole in then-branch of if-then-else inside typed LocalVariable → int. -/
def holeInIfThenBranch : Procedure :=
  mkProc "holeInIfThenBranch" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare .Hole)
        (some (bare (.LiteralInt 0)))))))
  ] none))

/-- Hole in else-branch of if-then-else inside typed LocalVariable → int. -/
def holeInIfElseBranch : Procedure :=
  mkProc "holeInIfElseBranch" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare (.LiteralInt 1))
        (some (bare .Hole))))))
  ] none))

/-- Hole as while-loop condition → bool. -/
def holeAsWhileCondition : Procedure :=
  mkProc "holeAsWhileCondition" (bare (.Block [
    bare (.While (bare .Hole) [] none
      (bare (.Block [] none)))
  ] none))

/-- Hole as while-loop invariant → bool. -/
def holeAsWhileInvariant : Procedure :=
  mkProc "holeAsWhileInvariant" (bare (.Block [
    bare (.While (bare (.LiteralBool true)) [bare .Hole] none
      (bare (.Block [] none)))
  ] none))

/-- Hole as while-loop decreases measure → int. -/
def holeAsWhileDecreases : Procedure :=
  mkProc "holeAsWhileDecreases" (bare (.Block [
    bare (.While (bare (.LiteralBool true)) [] (some (bare .Hole))
      (bare (.Block [] none)))
  ] none))

/-- Hole as static call argument → Top (no parameter type info). -/
def holeInCallArg : Procedure :=
  mkProc "holeInCallArg" (bare (.Block [
    bare (.StaticCall "f" [bare (.LiteralInt 1), bare .Hole])
  ] none))

/-- Hole as return value → Top. -/
def holeInReturn : Procedure :=
  mkProc "holeInReturn" (bare (.Block [
    bare (.Return (some (bare .Hole)))
  ] none))

/-- Hole inside Old → inherits int from LocalVariable. -/
def holeInOld : Procedure :=
  mkProc "holeInOld" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.Old (bare .Hole)))))
  ] none))

/-- Hole in boolean And arg inside assert → bool (And propagates bool). -/
def holeInBooleanOp : Procedure :=
  mkProc "holeInBooleanOp" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .And [bare (.LiteralBool true), bare .Hole])))
  ] none))

/-- Hole in Neg inside typed LocalVariable → int. -/
def holeInNeg : Procedure :=
  mkProc "holeInNeg" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Neg [bare .Hole]))))
  ] none))

/-- Hole in StrConcat inside typed LocalVariable → string. -/
def holeInStrConcat : Procedure :=
  mkProc "holeInStrConcat" (bare (.Block [
    bare (.LocalVariable "s" (bareType .TString)
      (some (bare (.PrimitiveOp .StrConcat [bare (.LiteralString "hi"), bare .Hole]))))
  ] none))

/-- Hole in ProveBy value position → inherits int from LocalVariable. -/
def holeInProveByValue : Procedure :=
  mkProc "holeInProveByValue" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.ProveBy (bare .Hole) (bare (.LiteralBool true))))))
  ] none))

/-- Hole in ReferenceEquals → Top. -/
def holeInReferenceEquals : Procedure :=
  mkProc "holeInReferenceEquals" (bare (.Block [
    bare (.Assert (bare (.ReferenceEquals (bare .Hole) (bare (.Identifier "y")))))
  ] none))

/-! ## Multiple holes in one procedure -/

/-- Two holes in the same arithmetic expression → both int. -/
def twoHolesInAdd : Procedure :=
  mkProc "twoHolesInAdd" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Add [bare .Hole, bare .Hole]))))
  ] none))

/-- Holes in both branches of if-then-else → both bool. -/
def holesInBothBranches : Procedure :=
  mkProc "holesInBothBranches" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TBool)
      (some (bare (.IfThenElse (bare (.LiteralBool true))
        (bare .Hole)
        (some (bare .Hole))))))
  ] none))

/-- Holes in multiple statements: one in local var (int), one in assert (bool). -/
def holesInMultipleStatements : Procedure :=
  mkProc "holesInMultipleStatements" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.PrimitiveOp .Mul [bare (.LiteralInt 2), bare .Hole])))),
    bare (.Assert (bare .Hole))
  ] none))

/-! ## Combinations: holes in nested contexts -/

/-- Hole in arithmetic inside if-then-else condition → Top (comparison arg). -/
def holeInArithInsideIfCond : Procedure :=
  mkProc "holeInArithInsideIfCond" (bare (.Block [
    bare (.IfThenElse
      (bare (.PrimitiveOp .Gt [bare (.PrimitiveOp .Add [bare (.LiteralInt 1), bare .Hole]), bare (.LiteralInt 0)]))
      (bare (.Assert (bare (.LiteralBool true))))
      none)
  ] none))

/-- Hole in comparison inside while condition → Top (comparison arg). -/
def holeInCompInsideWhileCond : Procedure :=
  mkProc "holeInCompInsideWhileCond" (bare (.Block [
    bare (.While
      (bare (.PrimitiveOp .Lt [bare (.Identifier "i"), bare .Hole]))
      [] none
      (bare (.Block [] none)))
  ] none))

/-- Hole in call argument inside typed LocalVariable → Top (call arg). -/
def holeInCallInsideLocalVar : Procedure :=
  mkProc "holeInCallInsideLocalVar" (bare (.Block [
    bare (.LocalVariable "x" (bareType .TInt)
      (some (bare (.StaticCall "compute" [bare .Hole]))))
  ] none))

/-- Hole in And: one in comparison arg (Top), one direct (bool). -/
def holeInAndWithComparison : Procedure :=
  mkProc "holeInAndWithComparison" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .And [
      bare (.PrimitiveOp .Gt [bare .Hole, bare (.LiteralInt 0)]),
      bare .Hole])))
  ] none))

/-- Hole in Implies inside while invariant → bool. -/
def holeInImpliesInsideInvariant : Procedure :=
  mkProc "holeInImpliesInsideInvariant" (bare (.Block [
    bare (.While (bare (.LiteralBool true))
      [bare (.PrimitiveOp .Implies [bare (.Identifier "p"), bare .Hole])]
      none
      (bare (.Block [] none)))
  ] none))

/-- Hole in nested if-then-else: condition of inner if → bool. -/
def holeInNestedIfCondition : Procedure :=
  mkProc "holeInNestedIfCondition" (bare (.Block [
    bare (.IfThenElse (bare (.LiteralBool true))
      (bare (.IfThenElse (bare .Hole)
        (bare (.Assert (bare (.LiteralBool true))))
        none))
      none)
  ] none))

/-- Hole in Sub inside Leq inside assert → Top (comparison arg). -/
def holeInSubInsideLeq : Procedure :=
  mkProc "holeInSubInsideLeq" (bare (.Block [
    bare (.Assert (bare (.PrimitiveOp .Leq [
      bare (.PrimitiveOp .Sub [bare (.Identifier "n"), bare .Hole]),
      bare (.LiteralInt 10)])))
  ] none))

/-- Hole in Mul inside typed LocalVariable with real type → real. -/
def holeInMulWithReal : Procedure :=
  mkProc "holeInMulWithReal" (bare (.Block [
    bare (.LocalVariable "r" (bareType .TReal)
      (some (bare (.PrimitiveOp .Mul [bare (.LiteralDecimal ⟨314, -2⟩), bare .Hole]))))
  ] none))

/-! ## Test execution -/

def testBasic : Program := {
  staticProcedures := [holeInArithmeticOp, holeAsInitializer, holeInComparisonInsideAssert]
  staticFields := []
  types := []
}

/--
info: procedure holeInArithmeticOp() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 1 + $hole_0 }
procedure holeAsInitializer() returns ⏎
()
deterministic
{ var x: int := <?> }
procedure holeInComparisonInsideAssert() returns ⏎
()
deterministic
{ var $hole_0: ⊤; assert $hole_0 > 0 }
-/
#guard_msgs in
#eval! printProgram (liftHoles testBasic)

def testBoolContexts : Program := {
  staticProcedures := [
    holeAsAssertCondition, holeAsAssumeCondition,
    holeAsIfCondition, holeAsWhileCondition,
    holeAsWhileInvariant, holeAsWhileDecreases
  ]
  staticFields := []
  types := []
}

/--
info: procedure holeAsAssertCondition() returns ⏎
()
deterministic
{ var $hole_0: bool; assert $hole_0 }
procedure holeAsAssumeCondition() returns ⏎
()
deterministic
{ var $hole_0: bool; assume $hole_0 }
procedure holeAsIfCondition() returns ⏎
()
deterministic
{ var $hole_0: bool; if $hole_0 then { assert true } }
procedure holeAsWhileCondition() returns ⏎
()
deterministic
{ var $hole_0: bool; while $hole_0 { {  } } }
procedure holeAsWhileInvariant() returns ⏎
()
deterministic
{ var $hole_0: bool; while true invariant $hole_0 { {  } } }
procedure holeAsWhileDecreases() returns ⏎
()
deterministic
{ var $hole_0: int; while true { {  } } }
-/
#guard_msgs in
#eval! printProgram (liftHoles testBoolContexts)

def testBranches : Program := {
  staticProcedures := [
    holeInIfThenBranch, holeInIfElseBranch,
    holeInCallArg, holeInReturn, holeInOld
  ]
  staticFields := []
  types := []
}

/--
info: procedure holeInIfThenBranch() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then $hole_0 else 0 }
procedure holeInIfElseBranch() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := if true then 1 else $hole_0 }
procedure holeInCallArg() returns ⏎
()
deterministic
{ var $hole_0: ⊤; f(1, $hole_0) }
procedure holeInReturn() returns ⏎
()
deterministic
{ var $hole_0: ⊤; return $hole_0 }
procedure holeInOld() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := old($hole_0) }
-/
#guard_msgs in
#eval! printProgram (liftHoles testBranches)

def testOperators : Program := {
  staticProcedures := [
    holeInBooleanOp, holeInNeg, holeInStrConcat,
    holeInProveByValue, holeInReferenceEquals
  ]
  staticFields := []
  types := []
}

/--
info: procedure holeInBooleanOp() returns ⏎
()
deterministic
{ var $hole_0: bool; assert true && $hole_0 }
procedure holeInNeg() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := -$hole_0 }
procedure holeInStrConcat() returns ⏎
()
deterministic
{ var $hole_0: string; var s: string := "hi" ++ $hole_0 }
procedure holeInProveByValue() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := proveBy($hole_0, true) }
procedure holeInReferenceEquals() returns ⏎
()
deterministic
{ var $hole_0: ⊤; assert $hole_0 === y }
-/
#guard_msgs in
#eval! printProgram (liftHoles testOperators)

def testMultipleHoles : Program := {
  staticProcedures := [twoHolesInAdd, holesInBothBranches, holesInMultipleStatements]
  staticFields := []
  types := []
}

/--
info: procedure twoHolesInAdd() returns ⏎
()
deterministic
{ var $hole_0: int; var $hole_1: int; var x: int := $hole_0 + $hole_1 }
procedure holesInBothBranches() returns ⏎
()
deterministic
{ var $hole_0: bool; var $hole_1: bool; var x: bool := if true then $hole_0 else $hole_1 }
procedure holesInMultipleStatements() returns ⏎
()
deterministic
{ var $hole_0: int; var x: int := 2 * $hole_0; var $hole_1: bool; assert $hole_1 }
-/
#guard_msgs in
#eval! printProgram (liftHoles testMultipleHoles)

def testCombinations : Program := {
  staticProcedures := [
    holeInArithInsideIfCond, holeInCompInsideWhileCond,
    holeInCallInsideLocalVar, holeInAndWithComparison,
    holeInImpliesInsideInvariant
  ]
  staticFields := []
  types := []
}

/--
info: procedure holeInArithInsideIfCond() returns ⏎
()
deterministic
{ var $hole_0: ⊤; if 1 + $hole_0 > 0 then { assert true } }
procedure holeInCompInsideWhileCond() returns ⏎
()
deterministic
{ var $hole_0: ⊤; while i < $hole_0 { {  } } }
procedure holeInCallInsideLocalVar() returns ⏎
()
deterministic
{ var $hole_0: ⊤; var x: int := compute($hole_0) }
procedure holeInAndWithComparison() returns ⏎
()
deterministic
{ var $hole_0: ⊤; var $hole_1: bool; assert $hole_0 > 0 && $hole_1 }
procedure holeInImpliesInsideInvariant() returns ⏎
()
deterministic
{ var $hole_0: bool; while true invariant p ==> $hole_0 { {  } } }
-/
#guard_msgs in
#eval! printProgram (liftHoles testCombinations)

def testNestedAndMisc : Program := {
  staticProcedures := [
    holeInNestedIfCondition, holeInSubInsideLeq,
    holeInMulWithReal
  ]
  staticFields := []
  types := []
}

/--
info: procedure holeInNestedIfCondition() returns ⏎
()
deterministic
{ var $hole_0: bool; if true then { if $hole_0 then { assert true } } }
procedure holeInSubInsideLeq() returns ⏎
()
deterministic
{ var $hole_0: ⊤; assert n - $hole_0 <= 10 }
procedure holeInMulWithReal() returns ⏎
()
deterministic
{ var $hole_0: real; var r: real := 3.14 * $hole_0 }
-/
#guard_msgs in
#eval! printProgram (liftHoles testNestedAndMisc)

end Laurel
