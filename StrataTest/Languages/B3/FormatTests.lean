/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt

namespace B3

open Std (Format)

section ExpressionFormatTests

instance : Std.ToFormat defaultExprParams.Metadata where
   format _ := f!""

instance : Std.ToFormat defaultExprParams.Identifier where
   format id := f!"{id.name}"

instance : Coe String defaultExprParams.Identifier
 where
  coe s := B3Ident.mk s





-- Test quantifier expression formatting (no patterns)
def testQuantifierExpr : B3Expression :=
  .quantifierExpr () .forall "i" "int" []
    (.binaryOp () .ge
      (.id () "i")
      (.literal () (Lambda.LConst.intConst 0)))

/-- info: forall i : int i >= 0 -/
#guard_msgs in
#eval testQuantifierExpr.format

-- Test quantifier expression with single pattern
def testQuantifierExprWithPattern : B3Expression :=
  .quantifierExpr () .forall "x" "int"
    [.pattern () [.functionCall () "f" [.id () "x"]]]
    (.binaryOp () .gt
      (.functionCall () "f" [.id () "x"])
      (.literal () (Lambda.LConst.intConst 0)))

/-- info: forall x : int pattern f(x), f(x) > 0 -/
#guard_msgs in
#eval testQuantifierExprWithPattern.format

-- Test quantifier expression with multiple patterns
def testQuantifierExprWithMultiplePatterns : B3Expression :=
  .quantifierExpr () .exists "y" "bool"
    [.pattern () [.id () "y"],
     .pattern () [.unaryOp () .not (.id () "y")]]
    (.binaryOp () .or
      (.id () "y")
      (.unaryOp () .not (.id () "y")))

/-- info: exists y : bool pattern y, pattern !y, y || !y -/
#guard_msgs in
#eval testQuantifierExprWithMultiplePatterns.format

end ExpressionFormatTests

section StatementFormatTests

-- Test variable declaration formatting
def testVarDecl : B3Stmt :=
  Stmt.varDecl () "x" "int" none none

/--
info: var x : int
-/
#guard_msgs in
#eval testVarDecl.format

-- Test variable declaration with initialization
def testVarDeclInit : B3Stmt :=
  .varDecl () "y" "bool" none
    (some (Expression.literal () (Lambda.LConst.boolConst true)))

/--
info: var y : bool := true
-/
#guard_msgs in
#eval testVarDeclInit.format

-- Test variable declaration with autoinvariant
def testVarDeclAutoinv : B3Stmt :=
  .varDecl () "z" (some "int")
    (some (Expression.binaryOp () .ge (Expression.id () "z") (Expression.literal () (Lambda.LConst.intConst 0))))
    none

/--
info: var z : int autoinv z >= 0
-/
#guard_msgs in
#eval testVarDeclAutoinv.format



-- Test procedure call formatting
def testCall : B3Stmt :=
  .call () ["result"] "compute"
    [.expr (.id () "a"), .expr (.id () "b")]

/--
info: result := compute(a, b)
-/
#guard_msgs in
#eval testCall.format

-- Test procedure call with out/inout parameters
def testCallOutInout : B3Stmt :=
  .call () [] "modify"
    [.inout "x", .out "y"]

/--
info: modify(inout x, out y)
-/
#guard_msgs in
#eval testCallOutInout.format









-- Test aForall formatting
def testAForall : B3Stmt :=
  .aForall () "x" "int"
    (.blockStmt () [
      .check () (.binaryOp () .ge (.id () "x") (.literal () (Lambda.LConst.intConst 0)))
    ])

/--
info: forall x : int {
  check x >= 0
}
-/
#guard_msgs in
#eval testAForall.format

-- Test choose formatting
def testChoose : B3Stmt :=
  .choose () [
    .blockStmt () [.assign () "x" (.literal () (Lambda.LConst.intConst 1))],
    .blockStmt () [.assign () "x" (.literal () (Lambda.LConst.intConst 2))]
  ]

/--
info: choose {
  x := 1
} or {
  x := 2
}
-/
#guard_msgs in
#eval testChoose.format

-- Test ifCase formatting
def testIfCase : B3Stmt :=
  .ifCase () [
    (.binaryOp () .eq (.id () "x") (.literal () (Lambda.LConst.intConst 1)),
     .blockStmt () [.assign () "y" (.literal () (Lambda.LConst.intConst 10))]),
    (.binaryOp () .eq (.id () "x") (.literal () (Lambda.LConst.intConst 2)),
     .blockStmt () [.assign () "y" (.literal () (Lambda.LConst.intConst 20))])
  ]

/--
info: if
case x == 1 {
  y := 10
}
case x == 2 {
  y := 20
}
-/
#guard_msgs in
#eval testIfCase.format

end StatementFormatTests

end B3
