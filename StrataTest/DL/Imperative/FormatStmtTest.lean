/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.Statement

namespace FormatStmtTest
open Core
open Imperative
open Std (format Format)
open Lambda (LExpr LMonoTy LTy)

private abbrev S := Core.Statement
private abbrev Ss := List S
private abbrev E := Expression.Expr

private def intTy : Expression.Ty := .forAll [] .int
private def x : E := .fvar () (CoreIdent.unres "x") (some .int)
private def y : E := .fvar () (CoreIdent.unres "y") (some .int)
private def tt : E := .boolConst () true
private def int0 : E := .intConst () 0
private def int1 : E := .intConst () 1
private def int2 : E := .intConst () 2
private def int42 : E := .intConst () 42
private def xEq0 : E := .eq () x int0
private def xEq5 : E := .eq () x (.intConst () 5)
private def xEq1 : E := .eq () x int1

-- 1. cmd: init
/-- info: init (x : int) := #0 -/
#guard_msgs in #eval! format (Statement.init "x" intTy int0 .empty : S)

-- 2. cmd: set
/-- info: x := #42 -/
#guard_msgs in #eval! format (Statement.set "x" int42 .empty : S)

-- 3. cmd: havoc
/-- info: havoc x -/
#guard_msgs in #eval! format (Statement.havoc "x" .empty : S)

-- 4. cmd: assert
/-- info: assert [lbl] #true -/
#guard_msgs in #eval! format (Statement.assert "lbl" tt .empty : S)

-- 5. cmd: assume
/-- info: assume [lbl] ((x : int) == #5) -/
#guard_msgs in #eval! format (Statement.assume "lbl" xEq5 .empty : S)

-- 6. cmd: call (no lhs)
/-- info: call foo(#1, #2) -/
#guard_msgs in #eval! format (Statement.call [] "foo" [int1, int2] .empty : S)

-- 7. cmd: call (with lhs)
/-- info: call [y] := bar(#1) -/
#guard_msgs in #eval! format (Statement.call ["y"] "bar" [int1] .empty : S)

-- 8. block: empty
/-- info: myBlock :
{} -/
#guard_msgs in #eval! format (Stmt.block "myBlock" ([] : Ss) .empty : S)

-- 9. block: with statements
/--
info: myBlock :
{
  x := #1
  assert [check] ((x : int) == #1)
}
-/
#guard_msgs in
#eval! format (Stmt.block "myBlock" ([Statement.set "x" int1 .empty,
                                      Statement.assert "check" xEq1 .empty] : Ss) .empty : S)

def p := (Stmt.ite xEq0
                ([Statement.set "y" int1 .empty] : Ss)
                ([Statement.set "y" int2 .empty] : Ss)
                .empty : S)
-- 10. ite: with body
/--
info: {
  if ((x : int) == #0) {
    y := #1
  }
  else {
    y := #2
  }
  if ((x : int) == #0) {
    y := #1
  }
  else {
    y := #2
  }
}
-/
#guard_msgs in
#eval! format [p,p]


/--
info: if ((x : int) == #0) {
  y := #1
}
else {
  y := #2
}
-/
#guard_msgs in
#eval! format p


-- 11. ite: empty branches
/--
info: if #true {}
else {}
-/
#guard_msgs in #eval! format (Stmt.ite tt ([] : Ss) ([] : Ss) .empty : S)

-- 12. loop: no measure, no invariant
/--
info: while
  ((x : int) == #0)
  (none)
  []
{
  x := #1
}
-/
#guard_msgs in
#eval! format (Stmt.loop xEq0 none []
                ([Statement.set "x" int1 .empty] : Ss) .empty : S)

-- 13. loop: with measure and invariant
/--
info: while
  ((x : int) == #0)
  (some (x : int))
  [#true]
{
  x := #1
}
-/
#guard_msgs in
#eval! format (Stmt.loop xEq0 (some x) [tt]
                ([Statement.set "x" int1 .empty] : Ss) .empty : S)

-- 14. goto
/-- info: goto target -/
#guard_msgs in #eval! format (Stmt.goto "target" .empty : S)

-- 15. funcDecl
/-- info: funcDecl <function> -/
#guard_msgs in
#eval! format (Stmt.funcDecl
  ({ name := CoreIdent.unres "f",
     inputs := [("a", LTy.forAll [] .int)],
     output := LTy.forAll [] .int,
     body := some x } : PureFunc Expression) .empty : S)

-- 16. formatBlock: empty
/-- info: {} -/
#guard_msgs in #eval! format ([] : Ss)

-- 17. formatBlock: multiple statements
/--
info: {
  x := #1
  assert [check] ((x : int) == #1)
}
-/
#guard_msgs in
#eval! format ([Statement.set "x" int1 .empty,
                Statement.assert "check" xEq1 .empty] : Ss)

end FormatStmtTest
