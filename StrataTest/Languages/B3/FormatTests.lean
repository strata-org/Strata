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

-- Test identifier formatting
def testId : B3Expression :=
  .id () "x"

/--
info: x
-/
#guard_msgs in
#eval testId.format

-- Test function call formatting
def testFunctionCall : B3Expression :=
  .functionCall () "foo"
    [.id () "x", .id () "y"]

/--
info: foo(x, y)
-/
#guard_msgs in
#eval testFunctionCall.format

-- Test let expression formatting
def testLetExpr : B3Expression :=
  .letExpr () "temp"
    (.literal () (Lambda.LConst.intConst 10))
    (.binaryOp () .add
      (.id () "temp")
      (.id () "x"))

/--
info: val temp := 10 temp + x
-/
#guard_msgs in
#eval testLetExpr.format

-- Test labeled expression formatting
def testLabeledExpr : B3Expression :=
  .labeledExpr () "important"
    (.id () "result")

/--
info: important: result
-/
#guard_msgs in
#eval testLabeledExpr.format

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

-- Test block statement formatting
def testBlockStmt : B3Stmt :=
  .blockStmt () [
    .assign () "x" (.literal () (Lambda.LConst.intConst 1)),
    .assign () "y" (.literal () (Lambda.LConst.intConst 2))
  ]

/--
info: {
  x := 1
  y := 2
}
-/
#guard_msgs in
#eval testBlockStmt.format

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

-- Test if statement formatting
def testIfStmt : B3Stmt :=
  .ifStmt ()
    (.id () "flag")
    (.blockStmt () [.assign () "x" (.literal () (Lambda.LConst.intConst 1))])
    (some (.blockStmt () [.assign () "x" (.literal () (Lambda.LConst.intConst 0))]))

/--
info: if flag {
  x := 1
} else {
  x := 0
}
-/
#guard_msgs in
#eval testIfStmt.format

-- Test loop formatting
def testLoop : B3Stmt :=
  .loop () []
    (.blockStmt () [
      .assign () "i"
        (.binaryOp () .add
          (.id () "i")
          (.literal () (Lambda.LConst.intConst 1)))
    ])

/--
info: loop {
  i := i + 1
}
-/
#guard_msgs in
#eval testLoop.format

-- Test loop with invariants
def testLoopInv : B3Stmt :=
  .loop ()
    [.binaryOp () .ge (.id () "i") (.literal () (Lambda.LConst.intConst 0)),
     .binaryOp () .le (.id () "i") (.id () "n")]
    (.blockStmt () [
      .assign () "i"
        (.binaryOp () .add
          (.id () "i")
          (.literal () (Lambda.LConst.intConst 1)))
    ])

/--
info: loop
  invariant i >= 0
  invariant i <= n {
  i := i + 1
}
-/
#guard_msgs in
#eval testLoopInv.format

-- Test labeled statement formatting
def testLabeledStmt : B3Stmt :=
  .labeledStmt () "loop_start"
    (.assign () "x" (.literal () (Lambda.LConst.intConst 0)))

/--
info: loop_start: x := 0
-/
#guard_msgs in
#eval testLabeledStmt.format

-- Test exit formatting
def testExit : B3Stmt :=
  .exit () (some "loop_start")

/--
info: exit loop_start
-/
#guard_msgs in
#eval testExit.format

-- Test probe formatting
def testProbe : B3Stmt :=
  .probe () "debug_point"

/--
info: probe debug_point
-/
#guard_msgs in
#eval testProbe.format

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
