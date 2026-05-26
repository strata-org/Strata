/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Statement Formatting Tests

Tests for round-trip conversion and formatting of B3 statements.
Verifies that DDM AST → B3 AST → B3 CST → formatted output preserves structure and catches conversion errors.
-/

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

-- Helper to perform the round-trip transformation for statements
-- DDM OperationF → B3 Stmt → DDM → formatted output
partial def doRoundtripStmt (stmt : OperationF SourceRange) (ctx : FormatContext) (state : FormatState) : Format :=
  match B3CST.Statement.ofAst stmt with
  | .ok cstStmt =>
      let (b3Stmt, cstToAstErrors) := B3.stmtFromCST B3.FromCSTContext.empty cstStmt
      let (cstStmt', astToCstErrors) := B3.stmtToCST B3.ToCSTContext.empty b3Stmt
      -- Convert to Unit metadata for repr
      let b3StmtUnit := B3AST.Statement.mapMetadata (fun _ => ()) b3Stmt
      let reprStr := (repr b3StmtUnit).pretty
      let reprStr := cleanupStmtRepr reprStr
      let reprStr := cleanupUnitRepr reprStr
      let errorStr := if cstToAstErrors.isEmpty && astToCstErrors.isEmpty then ""
        else
          let cstErrs := cstToAstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let astErrs := astToCstErrors.map Std.format |> List.map (·.pretty) |> String.intercalate "\n  "
          let parts := [
            if cstToAstErrors.isEmpty then "" else s!"\nCST→AST Errors:\n  {cstErrs}",
            if astToCstErrors.isEmpty then "" else s!"\nAST→CST Errors:\n  {astErrs}"
          ]
          String.join parts
      dbg_trace f!"B3: {reprStr}{errorStr}"
      let cstAst := cstStmt'.toAst
      (mformat (ArgF.op cstAst) ctx state).format
  | .error msg => s!"Parse error: {msg}"

-- Helper to extract statement from a program and apply round-trip transformation
def roundtripStmt (p : Program) : Format :=
  let ctx := FormatContext.ofDialects p.dialects p.globalContext {}
  let state : FormatState := { openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_stmt" then
      match op.args.toList with
      | [ArgF.op stmt] => doRoundtripStmt stmt ctx state
      | _ => "Error: expected statement op"
    else s!"Error: expected command_stmt, got {op.name.name}"
  | _ => "Error: expected single command"

section StatementRoundtripTests

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "x"
    u some u "int"
    u none
    u none,
  .assign
    ()
    u 0
    (.literal () (.intLit () 42))]
---
info:
{
  var x : int
  x := 42
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; {var x: int x := 42} #end

/--
info: B3: .check
  ()
  (.binaryOp
    ()
    (.gt ())
    (.literal () (.intLit () 5))
    (.literal () (.intLit () 0)))
---
info:
check 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; check 5 > 0 #end

/--
info: B3: .assume
  ()
  (.binaryOp
    ()
    (.ge ())
    (.literal () (.intLit () 10))
    (.literal () (.intLit () 0)))
---
info:
assume 10 >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; assume 10 >= 0 #end

/--
info: B3: .assert
  ()
  (.binaryOp
    ()
    (.gt ())
    (.literal () (.intLit () 5))
    (.literal () (.intLit () 0)))
---
info:
assert 5 > 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; assert 5 > 0 #end

/--
info: B3: .reach
  ()
  (.binaryOp
    ()
    (.eq ())
    (.literal () (.intLit () 5))
    (.literal () (.intLit () 5)))
---
info:
reach 5 == 5
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; reach 5 == 5 #end

/--
info: B3: .returnStmt ()
---
info:
return
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; return #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "x"
    u some u "int"
    u none
    u none,
  .varDecl
    ()
    u "y"
    u some u "int"
    u none
    u none,
  .blockStmt
    ()
    u #[.assign
      ()
      u 1
      (.literal () (.intLit () 1)),
    .assign
      ()
      u 0
      (.literal () (.intLit () 2))]]
---
info:
{
  var x : int
  var y : int
  {
    x := 1
    y := 2
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int { x := 1 y := 2 } } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "flag"
    u some u "bool"
    u none
    u none,
  .varDecl
    ()
    u "x"
    u some u "int"
    u none
    u none,
  .ifStmt
    ()
    (.id () 1)
    (.assign
      ()
      u 0
      (.literal () (.intLit () 1)))
    u some (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.literal () (.intLit () 0))])]
---
info:
{
  var flag : bool
  var x : int
  if flag ⏎
    x := 1
  else ⏎
    {
      x := 0
    }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST;{ var flag: bool var x: int if flag x := 1 else { x := 0 } } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "i"
    u some u "int"
    u none
    u none,
  .loop
    ()
    u #[]
    (.blockStmt
      ()
      u #[.assign
        ()
        u 0
        (.binaryOp
          ()
          (.add ())
          (.id () 0)
          (.literal () (.intLit () 1)))])]
---
info:
{
  var i : int
  loop ⏎
  {
    i := i + 1
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var i: int loop { i := i + 1 } } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "i"
    u some u "int"
    u none
    u none,
  .varDecl
    ()
    u "n"
    u some u "int"
    u none
    u none,
  .loop
    ()
    u #[.binaryOp
      ()
      (.ge ())
      (.id () 1)
      (.literal () (.intLit () 0)),
    .binaryOp
      ()
      (.le ())
      (.id () 1)
      (.id () 0)]
    (.blockStmt
      ()
      u #[.assign
        ()
        u 1
        (.binaryOp
          ()
          (.add ())
          (.id () 1)
          (.literal () (.intLit () 1)))])]
---
info:
{
  var i : int
  var n : int
  loop
    invariant i >= 0
    invariant i <= n ⏎
  {
    i := i + 1
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var i: int var n: int loop invariant i >= 0 invariant i <= n { i := i + 1 } } #end

/--
info: B3: .exit () u some u "loop_start"
---
info:
exit loop_start
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; exit loop_start #end

/--
info: B3: .labeledStmt
  ()
  u "labeled_block"
  (.blockStmt
    ()
    u #[.varDecl
      ()
      u "x"
      u some u "int"
      u none
      u none,
    .assign
      ()
      u 0
      (.literal () (.intLit () 0))])
---
info: labeled_block: ⏎
{
  var x : int
  x := 0
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; labeled_block: {var x: int x := 0} #end

/--
info: B3: .probe () u "debug_point"
---
info:
probe debug_point
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; probe debug_point #end

/--
info: B3: .varDecl
  ()
  u "x"
  u some u "int"
  u none
  u none
---
info:
var x : int
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var x : int #end

/--
info: B3: .varDecl
  ()
  u "x"
  u some u "bool"
  u none
  u some (.literal () (.boolLit () true))
---
info:
var x : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; val x : bool := true #end

/--
info: B3: .varDecl
  ()
  u "y"
  u some u "bool"
  u none
  u some (.literal () (.boolLit () true))
---
info:
var y : bool := true
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var y : bool := true #end

/--
info: B3: .varDecl
  ()
  u "z"
  u some u "int"
  u some (.binaryOp
    ()
    (.ge ())
    (.id () 0)
    (.literal () (.intLit () 0)))
  u none
---
info:
var z : int autoinv z >= 0
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; var z : int autoinv z >= 0 #end

/--
info: B3: .aForall
  ()
  u "x"
  u "int"
  (.blockStmt
    ()
    u #[.check
      ()
      (.binaryOp
        ()
        (.ge ())
        (.id () 0)
        (.literal () (.intLit () 0)))])
---
info:
forall x : int ⏎
{
  check x >= 0
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; forall x : int { check x >= 0 } #end

/--
info: B3: .choose
  ()
  u #[.blockStmt
    ()
    u #[.varDecl
      ()
      u "x"
      u some u "int"
      u none
      u none,
    .assign
      ()
      u 0
      (.literal () (.intLit () 2))],
  .blockStmt
    ()
    u #[.varDecl
      ()
      u "x"
      u some u "int"
      u none
      u none,
    .assign
      ()
      u 0
      (.literal () (.intLit () 1))]]
---
info:
choose ⏎
{
  var x : int
  x := 1
} or ⏎
{
  var x : int
  x := 2
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; choose { var x: int x := 1 } or { var x: int x := 2 } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "x"
    u some u "int"
    u none
    u none,
  .varDecl
    ()
    u "y"
    u some u "int"
    u none
    u none,
  .ifCase
    ()
    u #[.oneIfCase
      ()
      (.binaryOp
        ()
        (.eq ())
        (.id () 1)
        (.literal () (.intLit () 1)))
      (.blockStmt
        ()
        u #[.assign
          ()
          u 0
          (.literal () (.intLit () 10))]),
    .oneIfCase
      ()
      (.binaryOp
        ()
        (.eq ())
        (.id () 1)
        (.literal () (.intLit () 2)))
      (.blockStmt
        ()
        u #[.assign
          ()
          u 0
          (.literal
            ()
            (.intLit () 20))])]]
---
info:
{
  var x : int
  var y : int
  if
  case x == 1 ⏎
  {
    y := 10
  }
  case x == 2 ⏎
  {
    y := 20
  }
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int if case x == 1 { y := 10 } case x == 2 { y := 20 } } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "a"
    u some u "int"
    u none
    u none,
  .varDecl
    ()
    u "b"
    u some u "int"
    u none
    u none,
  .call
    ()
    u "compute"
    u #[.callArgOut () u "result",
      .callArgExpr () (.id () 1),
      .callArgExpr () (.id () 0)]]
---
info:
{
  var a : int
  var b : int
  compute(out result, a, b)
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var a: int var b: int compute(out result, a, b) } #end

/--
info: B3: .blockStmt
  ()
  u #[.varDecl
    ()
    u "x"
    u some u "int"
    u none
    u none,
  .varDecl
    ()
    u "y"
    u some u "int"
    u none
    u none,
  .call
    ()
    u "modify"
    u #[.callArgInout () u "x",
      .callArgOut () u "y"]]
---
info:
{
  var x : int
  var y : int
  modify(inout x, out y)
}
-/
#guard_msgs in
#eval roundtripStmt $ #strata program B3CST; { var x: int var y: int modify(inout x, out y) } #end

end StatementRoundtripTests

end B3
